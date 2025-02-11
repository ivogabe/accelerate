{-# LANGUAGE AllowAmbiguousTypes    #-}
{-# LANGUAGE BlockArguments         #-}
{-# LANGUAGE EmptyCase              #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE InstanceSigs           #-}
{-# LANGUAGE LambdaCase             #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE OverloadedStrings      #-}
{-# LANGUAGE PatternGuards          #-}
{-# LANGUAGE PatternSynonyms        #-}
{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE UndecidableInstances   #-}
{-# LANGUAGE ViewPatterns           #-}

{-# OPTIONS_GHC -fno-warn-name-shadowing #-}
{-# LANGUAGE QuantifiedConstraints #-}

module Data.Array.Accelerate.Eval where

import Prelude                                                      hiding (take, (!!), sum)
import Data.Array.Accelerate.AST.Idx
import Data.Array.Accelerate.AST.Partitioned
import Data.Array.Accelerate.Trafo.Desugar
import Data.Array.Accelerate.Representation.Array
import Data.Array.Accelerate.Representation.Type
import Data.Array.Accelerate.AST.Environment
import Data.Array.Accelerate.Trafo.Operation.LiveVars
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Graph (MakesILP (BackendClusterArg), BackendCluster)
import Data.Array.Accelerate.Pretty.Partitioned ()
import Data.Array.Accelerate.Error

import Data.Array.Accelerate.Trafo.Schedule.Uniform ()
import Data.Array.Accelerate.Pretty.Schedule.Uniform ()
import Data.Kind (Type)
import Data.Bifunctor (bimap)
import Data.Biapplicative (biliftA2)
import Data.Type.Equality
import Data.Array.Accelerate.Type (ScalarType)
import Unsafe.Coerce (unsafeCoerce)
import Data.Array.Accelerate.Representation.Shape (ShapeR (..))


type BackendArgs op env = PreArgs (BackendClusterArg2 op env)
type BackendArgEnv op env = Env (BackendArgEnvElem op env)
data BackendArgEnvElem op env arg = BAE (FromArg env (Embed op arg)) (BackendClusterArg2 op env arg)
type EmbedEnv op env = Env (FromArg' op env)
newtype FromArg' op env a = FromArg (FromArg env (Embed op a))
pattern PushFA :: () => (e' ~ (e, x)) => EmbedEnv op env e -> FromArg env (Embed op x) -> EmbedEnv op env e'
pattern PushFA env x = Push env (FromArg x)
{-# COMPLETE Empty, PushFA #-}


class ( MakesILP op
      -- , forall env arg. Eq (BackendClusterArg2 op env arg)
      , forall env arg. Show (BackendClusterArg2 op env arg))
    => StaticClusterAnalysis (op :: Type -> Type) where
  data BackendClusterArg2 op env arg
  onOp :: op args -> BackendArgs op env (OutArgsOf args) -> Args env args -> FEnv op env -> BackendArgs op env args
  bcaid :: BackendClusterArg op arg -> BackendClusterArg op arg'
  def :: Arg env arg -> FEnv op env -> BackendClusterArg op arg -> BackendClusterArg2 op env arg
  valueToIn    :: BackendClusterArg2 op env (Value sh e)     -> BackendClusterArg2 op env (In    sh e)
  valueToOut   :: BackendClusterArg2 op env (Value sh e)     -> BackendClusterArg2 op env (Out   sh e)
  inToValue    :: BackendClusterArg2 op env (In    sh e)     -> BackendClusterArg2 op env (Value sh e)
  outToValue   :: BackendClusterArg2 op env (Out   sh e)     -> BackendClusterArg2 op env (Value sh e)
  outToSh      :: BackendClusterArg2 op env (Out   sh e)     -> BackendClusterArg2 op env (Sh    sh e)
  outToVar     :: BackendClusterArg2 op env (Out   sh e)     -> BackendClusterArg2 op env (Var'  sh  )
  shToOut      :: BackendClusterArg2 op env (Sh    sh e)     -> BackendClusterArg2 op env (Out   sh e)
  shToValue    :: BackendClusterArg2 op env (Sh    sh e)     -> BackendClusterArg2 op env (Value sh e)
  varToValue   :: BackendClusterArg2 op env (Var'  sh)       -> BackendClusterArg2 op env (Value sh e)
  varToSh      :: BackendClusterArg2 op env (Var'  sh)       -> BackendClusterArg2 op env (Sh    sh e)
  shToVar      :: BackendClusterArg2 op env (Sh    sh e)     -> BackendClusterArg2 op env (Var'  sh  )
  shrinkOrGrow :: ArrayR (Array sh e') -> ArrayR (Array sh e) -> BackendClusterArg2 op env (m     sh e')    -> BackendClusterArg2 op env (m     sh e)
  addTup       :: BackendClusterArg2 op env (v     sh e)     -> BackendClusterArg2 op env (v     sh ((), e))
  unitToVar    :: BackendClusterArg2 op env (m     sh ())    -> BackendClusterArg2 op env (Var'  sh  )
  varToUnit    :: BackendClusterArg2 op env (Var' sh)        -> BackendClusterArg2 op env (m     sh ())
  inToVar      :: BackendClusterArg2 op env (In sh e)        -> BackendClusterArg2 op env (Var' sh   )
  unitinfo     :: BackendClusterArg2 op env (m     sh ())
  pairinfo     :: ArrayR (Array sh (a,b)) -> BackendClusterArg2 op env (m sh a)         -> BackendClusterArg2 op env (m sh b) -> BackendClusterArg2 op env (m sh (a,b))
  -- pairinfo a b = if shrinkOrGrow a == b then shrinkOrGrow a else error $ "pairing unequal: " <> show a <> ", " <> show b
  unpairinfo   :: ArrayR (Array sh (a,b)) -> BackendClusterArg2 op env (m sh (a,b))     -> (BackendClusterArg2 op env (m sh a),  BackendClusterArg2 op env (m sh b))
  unpairinfo repr@(ArrayR shr (TupRpair a b)) x = 
    ( shrinkOrGrow repr (ArrayR shr a) x
    , shrinkOrGrow repr (ArrayR shr b) x)
  unpairinfo _ _ = internalError "Pair impossible"

makeBackendArg :: forall op env args. StaticClusterAnalysis op => Args env args -> FEnv op env -> Cluster op args -> BackendCluster op args -> BackendArgs op env args
makeBackendArg args env c b = go args c (defaultOuts args b) b
  where
    go :: forall args. Args env args -> Cluster op args -> BackendArgs op env (OutArgsOf args) -> BackendCluster op args -> BackendArgs op env args
    go args (Fused f l r) outputs bs = let
      backR = go (right f args) r (rightB args f outputs) (right' (const bcaid) bcaid f bs)
      backL = go (left  f args) l (backleft f backR outputs) (left' (const bcaid) f bs)
      in fuseBack f backL backR
    go args (SingleOp (Single op opArgs) _l) outputs _ =
      inverseBackendArgs args opArgs $ onOp @op op (backendClusterOutArgs args outputs opArgs) (prjClusterArgs args opArgs) env

    defaultOuts :: Args env args -> BackendCluster op args -> BackendArgs op env (OutArgsOf args)
    defaultOuts args backendcluster = forgetIn args $ fuseArgsWith args backendcluster (\arg b -> def arg env b)

    fuseBack :: forall largs rargs args
              . Fusion largs rargs args
             -> BackendArgs op env largs
             -> BackendArgs op env rargs
             -> BackendArgs op env args
    fuseBack EmptyF ArgsNil ArgsNil = ArgsNil
    fuseBack (Vertical _  f) (_ :>: ls) (r :>: rs) = inToVar r :>: fuseBack f ls rs
    fuseBack (Horizontal  f) (l :>: ls) (_ :>: rs) = l :>: fuseBack f ls rs
    fuseBack (Diagonal    f) (l :>: ls) (_ :>: rs) = l :>: fuseBack f ls rs
    fuseBack (IntroI1     f) (l :>: ls)        rs  = l :>: fuseBack f ls rs
    fuseBack (IntroI2     f)        ls  (r :>: rs) = r :>: fuseBack f ls rs
    fuseBack (IntroO1     f) (l :>: ls)        rs  = l :>: fuseBack f ls rs
    fuseBack (IntroO2     f)        ls  (r :>: rs) = r :>: fuseBack f ls rs
    fuseBack (IntroL      f) (l :>: ls)        rs  = l :>: fuseBack f ls rs
    fuseBack (IntroR      f)        ls  (r :>: rs) = r :>: fuseBack f ls rs

    rightB :: forall largs rargs args
            . StaticClusterAnalysis op
           => Args env args
           -> Fusion largs rargs args
           -> BackendArgs op env (OutArgsOf  args)
           -> BackendArgs op env (OutArgsOf rargs)
    rightB args f = forgetIn (right f args) . right' (const $ valueToIn . varToValue) (valueToIn . outToValue) f . inventIn args

    backleft :: forall largs rargs args
              . StaticClusterAnalysis op
             => Fusion largs rargs args
             -> BackendArgs op env rargs
             -> BackendArgs op env (OutArgsOf args)
             -> BackendArgs op env (OutArgsOf largs)
    backleft EmptyF ArgsNil ArgsNil = ArgsNil
    backleft (Vertical _  f) (r:>:rs)      as  = (valueToOut . inToValue) r :>: backleft f rs as
    backleft (Horizontal  f) (_:>:rs)      as  =                                backleft f rs as
    backleft (Diagonal    f) (r:>:rs) (_:>:as) = (valueToOut . inToValue) r :>: backleft f rs as -- just using 'a' is also type correct, and maybe also fine? Not sure anymore
    backleft (IntroI1     f)      rs       as  =                                backleft f rs as
    backleft (IntroI2     f) (_:>:rs)      as  =                                backleft f rs as
    backleft (IntroO1     f)      rs  (a:>:as) = a                          :>: backleft f rs as
    backleft (IntroO2     f) (_:>:rs) (_:>:as) =                                backleft f rs as
    backleft (IntroL      f)      rs       as = unsafeCoerce $ backleft f rs (unsafeCoerce as)
    backleft (IntroR      f) (_:>:rs)      as =                                backleft f rs (unsafeCoerce as)

inventIn :: Args env args -> PreArgs f (OutArgsOf args) -> PreArgs f args
inventIn ArgsNil ArgsNil = ArgsNil
inventIn (ArgArray Out _ _ _ :>: args) (arg :>: out) = arg :>: inventIn args out
inventIn (ArgArray In  _ _ _ :>: args) out = error "fake argument" :>: inventIn args out
inventIn (ArgArray Mut _ _ _ :>: args) out = error "fake argument" :>: inventIn args out
inventIn (ArgVar _           :>: args) out = error "fake argument" :>: inventIn args out
inventIn (ArgExp _           :>: args) out = error "fake argument" :>: inventIn args out
inventIn (ArgFun _           :>: args) out = error "fake argument" :>: inventIn args out

forgetIn :: Args env args -> PreArgs f args -> PreArgs f (OutArgsOf args)
forgetIn ArgsNil ArgsNil = ArgsNil
forgetIn (ArgArray Out _ _ _ :>: args) (arg :>: out) = arg :>: forgetIn args out
forgetIn (ArgArray In  _ _ _ :>: args) (_   :>: out) = forgetIn args out
forgetIn (ArgArray Mut _ _ _ :>: args) (_   :>: out) = forgetIn args out
forgetIn (ArgVar _           :>: args) (_   :>: out) = forgetIn args out
forgetIn (ArgExp _           :>: args) (_   :>: out) = forgetIn args out
forgetIn (ArgFun _           :>: args) (_   :>: out) = forgetIn args out



class (StaticClusterAnalysis op, Monad (EvalMonad op), TupRmonoid (Embed' op))
    => EvalOp op where
  type family EvalMonad op :: Type -> Type
  type family Index op :: Type
  type family Embed' op :: Type -> Type
  type family EnvF op :: Type -> Type

  unit :: Embed' op ()
  embed :: EnvF op a -> Embed' op a

  -- TODO most of these functions should probably be unnecesary, but adding them is the easiest way to get things working right now
  indexsh :: GroundVars env sh -> FEnv op env -> EvalMonad op (Embed' op sh)
  indexsh'   :: ExpVars env sh -> FEnv op env -> EvalMonad op (Embed' op sh)
  subtup :: SubTupR e e' -> Embed' op e -> Embed' op e'


  evalOp :: Index op -> Label -> op args -> FEnv op env -> BackendArgEnv op env (InArgs args) -> EvalMonad op (EmbedEnv op env (OutArgs args))
  writeOutput :: ScalarType e -> GroundVars env sh -> GroundVars env (Buffers e) -> FEnv op env -> Index op -> Embed' op e -> EvalMonad op ()
  readInput :: ScalarType e -> GroundVars env sh -> GroundVars env (Buffers e) -> FEnv op env -> BackendClusterArg2 op env (In sh e) -> Index op -> EvalMonad op (Embed' op e)
type FEnv op = Env (EnvF op)
type family Embed (op :: Type -> Type) a where
  Embed op (Value sh e) = Value' op sh e
  Embed op (Sh sh e) = Sh' op sh e
  Embed op e = e -- Mut, Exp', Var', Fun'

data Value' op sh e = Value' (Embed' op e) (Sh' op sh e)
data Sh' op sh e = Shape' (ShapeR sh) (Embed' op sh)

splitFromArg' :: (EvalOp op) => FromArg' op env (Value sh (l,r)) -> (FromArg' op env (Value sh l), FromArg' op env (Value sh r))
splitFromArg' (FromArg v) = bimap FromArg FromArg $ unpair' v

pairInArg :: (EvalOp op) => Modifier m -> ArrayR (Array sh (l,r)) -> BackendArgEnvElem op env (InArg (m sh l)) ->  BackendArgEnvElem op env (InArg (m sh r)) ->  BackendArgEnvElem op env (InArg (m sh (l,r)))
pairInArg In  repr (BAE x b) (BAE y d) = BAE (pair' x y) (pairinfo repr b d)
pairInArg Out repr (BAE x b) (BAE y d) = BAE (pair' x y) (pairinfo repr b d)
pairInArg _ _ _ _ = error "SOA'd non-array args"

evalCluster :: (EvalOp op) => Cluster op args -> BackendCluster op args -> Args env args -> FEnv op env -> Index op -> EvalMonad op ()
evalCluster c b args env ix = do
  let ba = makeBackendArg args env c b
  input <- readInputs ix args ba env
  output <- evalOps ix c input args env
  writeOutputs ix args output env

evalOps :: forall op args env. (EvalOp op) => Index op -> Cluster op args -> BackendArgEnv op env (InArgs args) -> Args env args -> FEnv op env -> EvalMonad op (EmbedEnv op env (OutArgs args))
evalOps ix c ba args env = case c of
  SingleOp (Single op cargs) l
     -> prjOpOutputs args cargs
        <$> evalOp ix l op env (prjOpInputs env args ba cargs)
  Fused f l r -> do
    lin <- leftIn f ba env
    lout <- evalOps ix l lin (left f args) env
    let rin = rightIn f lout ba
    rout <- evalOps ix r rin (right f args) env
    return $ totalOut f lout rout

prjOpInputs
  :: forall op env args opArgs.
     EvalOp op
  => FEnv op env
  -> Args env args
  -> BackendArgEnv op env (InArgs args)
  -> ClusterArgs (FunToEnv args) opArgs
  -> Env (BackendArgEnvElem op env) (InArgs opArgs)
prjOpInputs fenv args bcas = \case
  opArg :>: opArgs ->
    prjOpInputs @op fenv args bcas opArgs `Push` prjOpInput @op fenv args bcas opArg
  ArgsNil -> Empty

argsPrj
  :: Args env args
  -> BackendArgEnv op env (InArgs args)
  -> Idx (FunToEnv args) opArg
  -> BackendArgEnvElem op env (InArg opArg)
argsPrj (_ :>: _) (_ `Push` b) ZeroIdx = b
argsPrj (_ :>: as) (bs `Push` _) (SuccIdx idx) = argsPrj as bs idx
argsPrj ArgsNil _ idx = case idx of {}

prjOpInput
  :: forall op env args opArg.
     EvalOp op
  => FEnv op env
  -> Args env args
  -> BackendArgEnv op env (InArgs args)
  -> ClusterArg (FunToEnv args) opArg
  -> BackendArgEnvElem op env (InArg opArg)
prjOpInput _    args bcas (ClusterArgSingle idx) = argsPrj args bcas idx
prjOpInput fenv args bcas (ClusterArgArray (m :: Modifier m) (shr :: ShapeR sh) _ buffers)
  = snd $ go buffers
  where
    go :: ClusterArgBuffers (FunToEnv args) m sh t -> (TypeR t, BackendArgEnvElem op env (InArg (m sh t)))
    go (ClusterArgBuffersPair a1 a2)
      | (tp1, ba1) <- go a1
      , (tp2, ba2) <- go a2
      , tp <- (TupRpair tp1 tp2)
      = (tp, pairInArg m (ArrayR shr tp) ba1 ba2)
    go (ClusterArgBuffersDead tp idx)
      = (tp, bvartosh (argsPrj args bcas idx) fenv)
    go (ClusterArgBuffersLive tp idx)
      = (tp, argsPrj args bcas idx)

-- Build a PartialEnv, and at the end try to convert the PartialEnv to an Env.
prjOpOutputs
  :: forall op env opArgs args.
     EvalOp op
  => Args env args
  -> ClusterArgs (FunToEnv args) opArgs
  -> EmbedEnv op env (OutArgs opArgs)
  -> EmbedEnv op env (OutArgs args)
prjOpOutputs args opArgs result = completeEnv args $ go opArgs result PEnd
  where
    go :: ClusterArgs (FunToEnv args) opArgs' -> EmbedEnv op env (OutArgs opArgs') -> PartialEnv (FromArg' op env) (OutArgs args) -> PartialEnv (FromArg' op env) (OutArgs args)
    go ArgsNil _ accum = accum
    go (ClusterArgSingle idx :>: as) out accum = case funToEnvPrj args idx of
      ArgVar _ -> go as out accum
      ArgExp _ -> go as out accum
      ArgFun _ -> go as out accum
      ArgArray Mut _ _ _ -> go as out accum
      ArgArray _ _ _ _ -> internalError "In or Out array should not occur in ClusterArgSingle"
    go (ClusterArgArray In  _ _ _ :>: as) out accum = go as out accum
    go (ClusterArgArray Mut _ _ _ :>: as) out accum = go as out accum
    go (ClusterArgArray Out _ _ buffers :>: as) (Push out o) accum = go as out $ handleBuffers buffers o accum

    handleBuffers
      :: ClusterArgBuffers (FunToEnv args) Out sh e
      -> FromArg' op env (Value sh e)
      -> PartialEnv (FromArg' op env) (OutArgs args)
      -> PartialEnv (FromArg' op env) (OutArgs args)
    handleBuffers (ClusterArgBuffersLive _ idx) value accum = partialUpdate value (toOutArgsIdx args idx) accum
    handleBuffers (ClusterArgBuffersPair b1 b2) value accum
      | (value1, value2) <- splitFromArg' value
      = handleBuffers b1 value1 $ handleBuffers b2 value2 accum
    handleBuffers _ _ accum = accum

    completeEnv :: Args env args' -> PartialEnv (FromArg' op env) (OutArgs args') -> EmbedEnv op env (OutArgs args')
    completeEnv (a :>: as) e = case a of
      ArgVar _ -> completeEnv as e
      ArgExp _ -> completeEnv as e
      ArgFun _ -> completeEnv as e
      ArgArray Mut _ _ _ -> completeEnv as e
      ArgArray In  _ _ _ -> completeEnv as e
      ArgArray Out _ _ _ -> case e of
        PPush e' o -> completeEnv as e' `Push` o
        _ -> internalError  "Binding missing in environment. The ClusterArgs didn't use an Out parameter"
    completeEnv ArgsNil PEnd = Empty

toOutArgsIdx :: Args env args -> Idx (FunToEnv args) (Out sh e) -> Idx (OutArgs args) (Value sh e)
toOutArgsIdx (a :>: as) (SuccIdx idx) = case a of
  ArgVar _ -> toOutArgsIdx as idx
  ArgExp _ -> toOutArgsIdx as idx
  ArgFun _ -> toOutArgsIdx as idx
  ArgArray Mut _ _ _ -> toOutArgsIdx as idx
  ArgArray In _ _ _ -> toOutArgsIdx as idx
  ArgArray Out _ _ _ -> SuccIdx $ toOutArgsIdx as idx
toOutArgsIdx (_ :>: _) ZeroIdx = ZeroIdx
toOutArgsIdx ArgsNil idx = case idx of {}

toOutArgsIdx' :: Args env args -> Idx (FunToEnv args) (Out sh e) -> Idx (FunToEnv (OutArgsOf args)) (Out sh e)
toOutArgsIdx' (a :>: as) (SuccIdx idx) = case a of
  ArgVar _ -> toOutArgsIdx' as idx
  ArgExp _ -> toOutArgsIdx' as idx
  ArgFun _ -> toOutArgsIdx' as idx
  ArgArray Mut _ _ _ -> toOutArgsIdx' as idx
  ArgArray In _ _ _ -> toOutArgsIdx' as idx
  ArgArray Out _ _ _ -> SuccIdx $ toOutArgsIdx' as idx
toOutArgsIdx' (_ :>: _) ZeroIdx = ZeroIdx
toOutArgsIdx' ArgsNil idx = case idx of {}

bvartosh :: forall op sh e env. EvalOp op => BackendArgEnvElem op env (Var' sh) -> FEnv op env -> BackendArgEnvElem op env (Sh sh e)
bvartosh (BAE e b) env = BAE (Shape' (varsToShapeR e) (fromTupR (unit @op) $ mapTupR (embed @op) $ varsGet' e env)) (varToSh b)

readInputs :: forall args env op. (EvalOp op) => Index op -> Args env args -> BackendArgs op env args -> FEnv op env -> EvalMonad op (BackendArgEnv op env (InArgs args))
readInputs _ ArgsNil ArgsNil _ = pure Empty
readInputs ix (arg :>: args) (bca :>: bcas) env = case arg of
  ArgVar x -> flip Push (BAE x bca) <$> readInputs ix args bcas env
  ArgExp x -> flip Push (BAE x bca) <$> readInputs ix args bcas env
  ArgFun x -> flip Push (BAE x bca) <$> readInputs ix args bcas env
  ArgArray Mut (ArrayR shr r) sh buf -> flip Push (BAE (ArrayDescriptor shr sh buf, r) bca) <$> readInputs ix args bcas env
  ArgArray Out (ArrayR shr _) sh _   -> (\sh' -> flip Push (BAE (Shape' shr sh') (outToSh bca))) <$> indexsh @op sh env <*> readInputs ix args bcas env
  ArgArray In  (ArrayR shr r) sh buf -> case r of
    TupRsingle t -> (\env v sh' -> Push env (BAE (Value' v (Shape' shr sh')) (inToValue bca))) <$> readInputs ix args bcas env <*> readInput t sh buf env bca ix <*> indexsh @op sh env
    TupRunit -> (\sh' -> flip Push (BAE (Value' (unit @op) (Shape' shr sh')) (inToValue bca))) <$> indexsh @op sh env <*> readInputs ix args bcas env
    TupRpair{} -> error "not SOA'd"

writeOutputs :: forall args env op. (EvalOp op) => Index op -> Args env args -> EmbedEnv op env (OutArgs args) -> FEnv op env -> EvalMonad op ()
writeOutputs _  ArgsNil Empty _ = pure ()
writeOutputs ix (ArgArray Out (ArrayR _ r) sh buf :>: args) (PushFA env (Value' x _)) env'
  | TupRsingle t <- r = writeOutput @op t sh buf env' ix x >> writeOutputs ix args env env'
  | TupRunit <- r = writeOutputs ix args env env'
  | otherwise = error "not soa'd"
writeOutputs ix (ArgVar _           :>: args) env env' = writeOutputs ix args env env'
writeOutputs ix (ArgExp _           :>: args) env env' = writeOutputs ix args env env'
writeOutputs ix (ArgFun _           :>: args) env env' = writeOutputs ix args env env'
writeOutputs ix (ArgArray In  _ _ _ :>: args) env env' = writeOutputs ix args env env'
writeOutputs ix (ArgArray Mut _ _ _ :>: args) env env' = writeOutputs ix args env env'

leftIn :: forall largs rargs args op env. (EvalOp op) => Fusion largs rargs args -> BackendArgEnv op env (InArgs args) -> FEnv op env -> EvalMonad op (BackendArgEnv op env (InArgs largs))
leftIn EmptyF Empty _ = pure Empty
leftIn (Vertical _ f) (Push env (BAE x b)) env'= Push <$> leftIn f env env' <*> ((`BAE` varToSh b) . Shape' (varsToShapeR x) <$> indexsh' @op x env')
leftIn (Horizontal f) (Push env bae) env' = (`Push` bae) <$> leftIn f env env'
leftIn (Diagonal   f) (Push env bae) env' = (`Push` bae) <$> leftIn f env env'
leftIn (IntroI1    f) (Push env bae) env' = (`Push` bae) <$> leftIn f env env'
leftIn (IntroI2    f) (Push env _  ) env' =                  leftIn f env env'
leftIn (IntroO1    f) (Push env bae) env' = (`Push` bae) <$> leftIn f env env'
leftIn (IntroO2    f) (Push env _  ) env' =                  leftIn f env env'
leftIn (IntroL     f) (Push env bae) env' = (`Push` bae) <$> leftIn f env env'
leftIn (IntroR     f) (Push env _  ) env' =                  leftIn f env env'

rightIn :: (EvalOp op)
        => Fusion largs rargs args
        -> EmbedEnv op env (OutArgs largs)
        -> BackendArgEnv op env  ( InArgs  args)
        -> BackendArgEnv op env  ( InArgs rargs)
rightIn EmptyF Empty Empty = Empty
rightIn (Vertical _  f) (PushFA lenv fa) (Push env (BAE _ b)) = Push (rightIn f lenv env) (BAE fa $ varToValue b)
rightIn (Horizontal  f)         lenv     (Push env bae      ) = Push (rightIn f lenv env) bae
rightIn (Diagonal    f) (PushFA lenv fa) (Push env (BAE _ b)) = Push (rightIn f lenv env) (BAE fa $ shToValue b)
rightIn (IntroI1     f)         lenv     (Push env _        ) =       rightIn f lenv env
rightIn (IntroI2     f)         lenv     (Push env bae      ) = Push (rightIn f lenv env) bae
rightIn (IntroO1     f) (PushFA lenv _ ) (Push env _        ) =       rightIn f lenv env
rightIn (IntroO2     f)         lenv     (Push env bae      ) = Push (rightIn f lenv env) bae
rightIn (IntroL      f)         lenv     (Push env _        ) =       rightIn f (unsafeCoerce lenv) env
rightIn (IntroR      f)         lenv     (Push env bae      ) = Push (rightIn f lenv env) bae

inargs :: forall op env args args'
        . (EvalOp op)
        => (forall f. PreArgs f args -> PreArgs f args')
        -> BackendArgEnv op env (InArgs args)
        -> BackendArgEnv op env (InArgs args')
inargs f
  | Refl <- inargslemma @args
  = toEnv . f . fromEnv
  where
    fromEnv :: forall args. BackendArgEnv op env args -> PreArgs (BAEEInArg op env) (InArgs' args)
    fromEnv Empty = ArgsNil
    fromEnv (Push env (x :: BackendArgEnvElem op env t))
      | Refl <- inarglemma @t = BAEEInArg x :>: fromEnv env
    toEnv :: forall args. PreArgs (BAEEInArg op env) args -> BackendArgEnv op env (InArgs args)
    toEnv ArgsNil = Empty
    toEnv (BAEEInArg x :>: args) = Push (toEnv args) x


totalOut :: (EvalOp op)
         => Fusion largs rargs args
         -> EmbedEnv op env (OutArgs largs)
         -> EmbedEnv op env (OutArgs rargs)
         -> EmbedEnv op env (OutArgs args)
totalOut EmptyF Empty Empty = Empty
totalOut (Vertical _ f) (Push l _)      r    =       totalOut f l r
totalOut (Horizontal f)       l         r    =       totalOut f l r
totalOut (Diagonal   f) (Push l o)      r    = Push (totalOut f l r) o
totalOut (IntroI1    f)       l         r    =       totalOut f l r
totalOut (IntroI2    f)       l         r    =       totalOut f l r
totalOut (IntroO1    f) (Push l o)      r    = Push (totalOut f l r) o
totalOut (IntroO2    f)       l   (Push r o) = Push (totalOut f l r) o
totalOut (IntroL     f)       l         r    = unsafeCoerce $ totalOut f (unsafeCoerce l) r
totalOut (IntroR     f)       l         r    = unsafeCoerce $ totalOut f l (unsafeCoerce r)

outargs :: forall args args' env op
         . (EvalOp op)
        => (forall f. PreArgs f args -> PreArgs f args')
        -> Args env args
        -> EmbedEnv op env (OutArgs args)
        -> EmbedEnv op env (OutArgs args')
outargs f args
  | Refl <- inargslemma @args = toEnv . f . fromEnv args
  where
    -- coerces are safe, just me being lazy
    fromEnv :: forall args. Args env args -> EmbedEnv op env (OutArgs args) -> PreArgs (FAOutArg op env) args
    fromEnv ArgsNil Empty = ArgsNil
    fromEnv (a :>: args) out = case a of
      ArgArray Out _ _ _ -> case out of
        Push out' x -> FAOutJust x :>: fromEnv args out'
      _ -> FAOutNothing :>: fromEnv args (unsafeCoerce out)
    toEnv :: forall args. PreArgs (FAOutArg op env) args -> EmbedEnv op env (OutArgs args)
    toEnv ArgsNil = Empty
    toEnv (FAOutJust x :>: args) = Push (toEnv args) x
    toEnv (FAOutNothing :>: args) = unsafeCoerce $ toEnv args

newtype BAEEInArg op env arg = BAEEInArg (BackendArgEnvElem op env (InArg arg))
data FAOutArg (op :: Type -> Type) env arg where
  FAOutNothing :: FAOutArg op env arg
  FAOutJust :: FromArg' op env (Value sh e) -> FAOutArg op env (Out sh e)


instance EvalOp op => TupRmonoid (Value' op sh) where
  pair' (Value' x sh1) (Value' y sh2) = Value' (pair' x y) (pair' sh1 sh2)
  unpair' (Value' x sh) = biliftA2 Value' Value' (unpair' x) (unpair' sh)

instance TupRmonoid (Sh' op sh) where
  pair' (Shape' shr sh) _ = Shape' shr sh
  unpair' (Shape' shr sh) = (Shape' shr sh, Shape' shr sh)

backendClusterOutArgs
  :: forall op env args opArgs.
     StaticClusterAnalysis op
  => Args env args
  -> BackendArgs op env (OutArgsOf args)
  -> PreArgs (ClusterArg (FunToEnv args)) opArgs
  -> BackendArgs op env (OutArgsOf opArgs)
backendClusterOutArgs _ _ ArgsNil = ArgsNil
backendClusterOutArgs args ba (a :>: as) = case prjClusterArg args a of
  ArgVar _ -> backendClusterOutArgs args ba as
  ArgExp _ -> backendClusterOutArgs args ba as
  ArgFun _ -> backendClusterOutArgs args ba as
  ArgArray In  _ _ _ -> backendClusterOutArgs args ba as
  ArgArray Mut _ _ _ -> backendClusterOutArgs args ba as
  ArgArray Out (ArrayR shr _) _ _
    | ClusterArgArray _ _ _ buffers <- a -> case go shr buffers of
        (_, Just b) -> b :>: backendClusterOutArgs args ba as
        _ -> internalError "No BackendClusterArg2. Are all outputs marked as dead?"
    | otherwise -> internalError "Out array not allowed in ClusterArgSingle"
  where
    go :: ShapeR sh -> ClusterArgBuffers (FunToEnv args) Out sh e -> (TypeR e, Maybe (BackendClusterArg2 op env (Out sh e)))
    go shr (ClusterArgBuffersPair c1 c2)
      | (tp1, b1) <- go shr c1
      , (tp2, b2) <- go shr c2
      , tp <- TupRpair tp1 tp2
      , repr <- ArrayR shr tp
      , b <- case (b1, b2) of
          (Nothing, Nothing) -> Nothing
          (Just x , Nothing) -> Just $ shrinkOrGrow (ArrayR shr tp1) repr x
          (Nothing, Just x ) -> Just $ shrinkOrGrow (ArrayR shr tp2) repr x
          (Just x , Just y ) -> Just $ pairinfo repr x y
      = (tp, b)
    go _ (ClusterArgBuffersLive tp idx)
      = (tp, Just $ funToEnvPrj ba $ toOutArgsIdx' args idx)
    go _ (ClusterArgBuffersDead tp _)
      = (tp, Nothing)

inverseBackendArgs
  :: forall op env args opArgs.
     StaticClusterAnalysis op
  => Args env args
  -> ClusterArgs (FunToEnv args) opArgs
  -> BackendArgs op env opArgs
  -> BackendArgs op env args
inverseBackendArgs args opArgs bArgs = completeEnv args $ go opArgs bArgs PEnd
  where
    go
      :: ClusterArgs (FunToEnv args) opArgs'
      -> BackendArgs op env opArgs'
      -> PartialEnv (BackendClusterArg2 op env) (FunToEnv args)
      -> PartialEnv (BackendClusterArg2 op env) (FunToEnv args)
    go ArgsNil _ accum = accum
    go (ClusterArgSingle idx :>: as) (o :>: os) accum =
      go as os $ partialUpdate o idx accum
    go (ClusterArgArray _ shr tp buffers :>: as) (o :>: os) accum =
      go as os $ handleBuffers shr tp buffers o accum
    
    handleBuffers
      :: ShapeR sh
      -> TypeR e
      -> ClusterArgBuffers (FunToEnv args) m sh e
      -> BackendClusterArg2 op env (m sh e)
      -> PartialEnv (BackendClusterArg2 op env) (FunToEnv args)
      -> PartialEnv (BackendClusterArg2 op env) (FunToEnv args)
    handleBuffers shr tp (ClusterArgBuffersPair b1 b2) value accum
      | TupRpair t1 t2 <- tp
      , (value1, value2) <- unpairinfo @op (ArrayR shr tp) value
      = handleBuffers shr t1 b1 value1 $ handleBuffers shr t2 b2 value2 accum
      | otherwise = internalError "Pair impossible"
    handleBuffers _ _ (ClusterArgBuffersLive _ idx) value accum
      = partialUpdate value idx accum
    handleBuffers _ _ (ClusterArgBuffersDead _ idx) value accum
      = partialUpdate (outToVar @op value) idx accum

    completeEnv :: Args env args' -> PartialEnv (BackendClusterArg2 op env) (FunToEnv args') -> BackendArgs op env args'
    completeEnv (_ :>: as) (os `PPush` o) = o :>: completeEnv as os
    completeEnv ArgsNil _ = ArgsNil
    completeEnv _ _ = internalError "Binding missing in environment. The ClusterArgs didn't use a parameter"

-- instance EvalOp op => TupRmonoid (Compose (BackendArgEnvElem op env) (Value sh)) where
--   pair' (Compose (BAE x b)) (Compose (BAE y d)) =
--     Compose $ BAE (pair' x y) (Debug.Trace.trace "pair'" $ pairinfo b d)
--   unpair' (Compose (BAE x b)) =
--     biliftA2
--       (Compose .* BAE)
--       (Compose .* BAE)
--       (unpair' x)
--       (unpairinfo _ b)

-- instance EvalOp op => TupRmonoid (Compose (BackendArgEnvElem op env) (Sh sh)) where
--   pair' (Compose (BAE x b)) (Compose (BAE y d)) =
--     Compose $ BAE (pair' x y) (pairinfo b d)
--   unpair' (Compose (BAE x b)) =
--     biliftA2
--       (Compose .* BAE)
--       (Compose .* BAE)
--       (unpair' x)
--       (unpairinfo _ b)



-- use this to check whether a singleton cluster is a generate, map, etc
peekSingletonCluster :: (forall args'. op args' -> r) -> Cluster op args -> Maybe r
peekSingletonCluster k = \case
  SingleOp (Single op _) _ -> Just $ k op
  _ -> Nothing -- not a singleton cluster


-- only use this function if you know it is a singleton cluster of the right operation
-- unsafeCoerce here matches the provided function against the type of the actual operation, e.g. Generate
{- applySingletonCluster :: forall op env args args' r
                       . (op args' -> Args env args' -> r)
                       -> Cluster op args
                       -> Args env args
                       -> r
applySingletonCluster k c args = case c of
  SingleOp (Single op soas (SA _ unsort) subargs) _ ->
    unsafeCoerce @(op args' -> Args env args' -> r) @(op _ -> Args env _ -> r) 
      k 
      op 
      $ soaShrink combine soas $ unsort $ slv' varout subargs args
  _ -> error "not singleton"


-- only use this function if you know it is a singleton cluster of the right operation
applySingletonCluster' :: forall op env args args' f
                       . (op args' -> Args env args' -> PreArgs f args')
                       -> (forall l r g. f (g (l,r)) -> (f (g l), f (g r)))
                       -> (forall sh e. f (Out sh e) -> f (Var' sh))
                       -> Cluster op args
                       -> Args env args
                       -> PreArgs f args
applySingletonCluster' k f outvar' c args = case c of
  SingleOp (Single op soas (SA sort unsort) subargs) _ ->
    slv outvar' subargs $ sort $ soaExpand f soas $
      unsafeCoerce @(op args' -> Args env args' -> PreArgs f args') @(op _ -> Args env _ -> PreArgs f _) 
        k 
        op 
        $ soaShrink combine soas $ unsort $ slv' varout subargs args
  _ -> error "not singleton" -}

