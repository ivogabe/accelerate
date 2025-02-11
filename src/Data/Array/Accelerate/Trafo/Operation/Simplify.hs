{-# LANGUAGE EmptyCase           #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE MultiWayIf          #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE PatternGuards       #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE TypeOperators       #-}
{-# OPTIONS_HADDOCK hide #-}
-- |
-- Module      : Data.Array.Accelerate.Trafo.Operation.Simplify
-- Copyright   : [2012..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.Trafo.Operation.Simplify (
  simplify, simplifyFun, SimplifyOperation(..), CopyOperation(..),
  copyOperationsForArray, detectMapCopies, detectBackpermuteCopies
) where

import Data.Array.Accelerate.AST.Environment
import Data.Array.Accelerate.AST.Idx
import Data.Array.Accelerate.AST.IdxSet                     ( IdxSet )
import qualified Data.Array.Accelerate.AST.IdxSet           as IdxSet
import Data.Array.Accelerate.AST.LeftHandSide
import Data.Array.Accelerate.AST.Operation
import Data.Array.Accelerate.Error
import Data.Array.Accelerate.Array.Buffer
import Data.Array.Accelerate.Type
import Data.Array.Accelerate.Representation.Type
import Data.Array.Accelerate.Representation.Array
import Data.Array.Accelerate.Analysis.Match
import qualified Data.Array.Accelerate.Trafo.Exp.Simplify   as Exp
import Data.Array.Accelerate.Trafo.Exp.Substitution
import Data.Array.Accelerate.Trafo.Var
import Data.Array.Accelerate.Trafo.Substitution             hiding ( weakenArrayInstr )
import Data.Array.Accelerate.Trafo.WeakenedEnvironment
import Data.Array.Accelerate.Trafo.Operation.Substitution
import Data.Array.Accelerate.Trafo.LiveVars                 ( SubTupR(..), subTupR, subTupRpair, subTupPreserves )
import Data.Maybe                                           ( mapMaybe )
import Data.List                                            ( foldl' )
import Control.Monad
import Data.Functor.Identity

class SimplifyOperation op where
  detectCopy :: op f -> Args env f -> [CopyOperation env]
  detectCopy _ _ = []

data CopyOperation env where
  CopyOperation
    :: Idx env (Buffer t) -- input
    -> Idx env (Buffer t) -- output
    -> CopyOperation env

copyOperationsForArray :: forall env sh sh' t. Arg env (In sh t) -> Arg env (Out sh' t) -> [CopyOperation env]
copyOperationsForArray (ArgArray _ (ArrayR _ tp) _ input) (ArgArray _ _ _ output) = go tp input output []
  where
    go :: forall s. TypeR s -> GroundVars env (Buffers s) -> GroundVars env (Buffers s) -> [CopyOperation env] -> [CopyOperation env]
    go (TupRpair t1 t2) (TupRpair i1 i2) (TupRpair o1 o2) = go t1 i1 o1 . go t2 i2 o2
    go (TupRsingle t) (TupRsingle (Var _ input')) (TupRsingle (Var _ output'))
      | Refl <- reprIsSingle @ScalarType @s @Buffer t = (CopyOperation input' output' :)
    go _ _ _ = id

detectMapCopies :: forall genv sh t s. Args genv (Fun' (t -> s) -> In sh t -> Out sh s -> ()) -> [CopyOperation genv]
detectMapCopies (ArgFun (Lam lhs (Body body)) :>: ArgArray _ _ _ input :>: ArgArray _ _ _ output :>: ArgsNil)
  = detectMapCopies' lhs body input output
detectMapCopies _ = internalError "Function impossible"

detectMapCopies' :: forall genv env t s. ELeftHandSide t () env -> OpenExp env genv s -> GroundVars genv (Buffers t) -> GroundVars genv (Buffers s) -> [CopyOperation genv]
detectMapCopies' lhs body input output = go Just body output []
  where
    go :: forall env' s'. env' :?> env -> OpenExp env' genv s' -> GroundVars genv (Buffers s') -> [CopyOperation genv] -> [CopyOperation genv]
    go k (Pair e1 e2) (TupRpair o1 o2) = go k e1 o1 . go k e2 o2
    go k (Let lhs' _ expr) output'     = go (strengthenWithLHS lhs' >=> k) expr output'
    go k (Evar (Var tp idx)) (TupRsingle (Var _ output'))
      | Just idx' <- k idx -- Check if index is bound by the function (opposed to local binding)
      , Refl <- reprIsSingle @ScalarType @s' @Buffer tp
      = (CopyOperation (findInput idx') output' :)
    go _ _ _ = id

    findInput :: Idx env t' -> Idx genv (Buffer t')
    findInput idx = case findInput' lhs input idx of
      Right buffer -> buffer
      Left idx' -> case idx' of {}

    findInput' :: forall u env1 env2 t'. ELeftHandSide u env1 env2 -> GroundVars genv (Buffers u) -> Idx env2 t' -> Either (Idx env1 t') (Idx genv (Buffer t'))
    findInput' (LeftHandSideWildcard _) _ idx = Left idx
    findInput' (LeftHandSideSingle tp) (TupRsingle (Var _ buffer)) idx = case idx of
      SuccIdx idx' -> Left idx'
      ZeroIdx
        | Refl <- reprIsSingle @ScalarType @u @Buffer tp -> Right buffer
    findInput' (LeftHandSidePair l1 l2) (TupRpair in1 in2) idx = case findInput' l2 in2 idx of
      Left idx' -> findInput' l1 in1 idx'
      Right buffer -> Right buffer
    findInput' _ _ _ = internalError "Tuple mismatch"

detectBackpermuteCopies :: forall env sh sh' t. Args env (Fun' (sh' -> sh) -> In sh t -> Out sh' t -> ()) -> [CopyOperation env]
detectBackpermuteCopies (ArgFun f :>: input@(ArgArray _ _ sh _) :>: output@(ArgArray _ _ sh' _) :>: ArgsNil)
  | Just Refl <- matchVars sh sh'
  , Just Refl <- isIdentity f = copyOperationsForArray input output
detectBackpermuteCopies _ = []

data Info env t where
  InfoConst    :: ScalarType t -> t -> Info env t -- A constant scalar
  InfoAlias    :: Idx env t -> Info env t
  InfoBuffer   :: Maybe (Idx env t) -- In case of a Unit, the index of the scalar variable that it contains.
               -- Copy of another buffer. This is similar to an alias, but a buffer may only
               -- be a copy of another buffer temporarily. A write to the original or copy
               -- causes that they aren't copies any more. Hence we also keep track in
               -- InfoBuffer of the buffers it was copied to.
               -> Maybe (Idx env (Buffer t))
               -> [Idx env (Buffer t)] -- List of buffers where this buffer is copied to
               -> Info env (Buffer t)
  InfoNone     :: Info env t

newtype InfoEnv env = InfoEnv { unInfoEnv :: WEnv Info env }

emptySimplifyEnv :: InfoEnv ()
emptySimplifyEnv = InfoEnv wempty

instance Sink Info where
  weaken k (InfoAlias idx) = InfoAlias $ weaken k idx
  weaken _ (InfoConst t c)   = InfoConst t c
  weaken k (InfoBuffer unitScalar copyOf copied) = InfoBuffer (fmap (weaken k) unitScalar) (fmap (weaken k) copyOf) (fmap (weaken k) copied)
  weaken _ InfoNone        = InfoNone

infoFor :: Idx env t -> InfoEnv env -> Info env t
infoFor ix (InfoEnv env) = wprj ix env

-- Substitutions for aliasing.
-- This substitution only assures that we use the original declaration instead
-- of the alias. It does not remove the definition of the alias, a later pass
-- should remove that (with a (strongly) live variable analysis).
--
substitute :: InfoEnv env -> env :> env
substitute env = Weaken $ \idx -> case infoFor idx env of
  InfoAlias idx' -> idx'
  InfoBuffer _ (Just idx') _ -> idx'
  _              -> idx

-- When reading from an array, we can read from another buffer with the same
-- contents. The index of such copy is stored in InfoBuffer. When writing we
-- cannot do that. Note that after a write, the information about the copy
-- is removed in 'invalidate'.
--
substituteOutput :: InfoEnv env -> env :> env
substituteOutput env = Weaken $ \idx -> case infoFor idx env of
  InfoAlias idx' -> idx'
  _              -> idx

simplifyFun :: SimplifyOperation op => OperationAfun op () t -> OperationAfun op () t
simplifyFun fun = snd (simplifyFun' fun) emptySimplifyEnv

-- Returns a set of array variables which may have been written to, and a the simplified function (given an InfoEnv)
simplifyFun' :: SimplifyOperation op => OperationAfun op env t -> (IdxSet env, InfoEnv env -> OperationAfun op env t)
simplifyFun' (Alam lhs f) = 
  (IdxSet.drop' lhs set, \env -> Alam lhs $ f' $ bindEnv lhs env)
  where
    (set, f') = simplifyFun' f
simplifyFun' (Abody body)  = (set, \env -> Abody $ body' env)
  where
    (set, body') = simplify' (TupRsingle Shared) body

simplifyFunWithUniqueness :: SimplifyOperation op => Uniquenesses t -> OperationAfun op env (t -> t) -> (IdxSet env, InfoEnv env -> OperationAfun op env (t -> t))
simplifyFunWithUniqueness uniquenesses (Alam lhs (Abody body)) =
  ( IdxSet.drop' lhs set
  , \env -> Alam lhs $ Abody $ body' $ bindEnv lhs env
  )
  where
    (set, body') = simplify' uniquenesses body
simplifyFunWithUniqueness _ (Abody body) = groundFunctionImpossible $ groundsR body
simplifyFunWithUniqueness _ (Alam lhs (Alam _ _)) = groundFunctionImpossible $ lhsToTupR lhs

simplify :: SimplifyOperation op => OperationAcc op () t -> OperationAcc op () t
simplify acc = snd (simplify' (TupRsingle Shared) acc) emptySimplifyEnv

-- Returns the simplified program and a set of array variables which may have been written to
simplify' :: SimplifyOperation op => Uniquenesses t -> OperationAcc op env t -> (IdxSet env, InfoEnv env -> OperationAcc op env t)
simplify' uniquenesses = \case
  Exec op args ->
    (outputArrays args, \env -> Exec op $ mapArgs (simplifyArg env) args)
  Return vars ->
    -- Note that we do not need to check for writes to variables here.
    -- This construct may cause aliassing of variables, but an aliassed
    -- variable cannot be unique and thus we do not need to signal the
    -- original variable as mutated if it's returned.
    ( variableIndices uniquenesses vars
    , \env -> Return $ simplifyReturnVars env uniquenesses vars
    )
  Compute expr ->
    ( IdxSet.empty
    , \env ->
        let expr' = simplifyExp env expr
        in 
          if
            | Just vars <- extractParams expr' ->
              Return $ mapTupR (\(Var tp ix) -> Var (GroundRscalar tp) ix) vars
            | otherwise ->
              Compute expr'
    )
  Alet lhs us bnd body ->
    let
      (setBnd, bnd') = simplify' us bnd
      (setBody, body') = simplify' uniquenesses body
    in
      ( setBnd `IdxSet.union` IdxSet.drop' lhs setBody
      , \env ->
          let
            bnd'' = bnd' env
            env' = bindingEnv setBnd lhs bnd'' (invalidate setBnd env)
          in alet' lhs us bnd'' (body' env')
      )
  Alloc shr tp sh -> (IdxSet.empty, \env -> Alloc shr tp $ mapTupR (weaken $ substitute env) sh)
  Use tp 1 buffer ->
    ( IdxSet.empty
    , const
      $ Alet (LeftHandSideSingle (GroundRscalar tp)) (TupRsingle Shared) (Compute $ Const tp $ indexBuffer tp buffer 0)
      $ Unit (Var tp ZeroIdx)
    )
  Use tp n buffer -> (IdxSet.empty, const $ Use tp n buffer)
  Unit var -> (IdxSet.empty, \env -> Unit $ weaken (substitute env) var)
  Acond cond true false ->
    let
      (setT, true')  = simplify' uniquenesses true
      (setF, false') = simplify' uniquenesses false
      set = IdxSet.union setT setF
    in 
      ( set
      , \env -> case infoFor (varIdx cond) env of
        InfoConst _ 0 -> false' env
        InfoConst _ _ -> true'  env
        InfoAlias ix -> Acond (cond{varIdx = ix}) (true' env) (false' env)
        InfoNone     -> Acond cond                (true' env) (false' env)
      )
  Awhile us cond step initial ->
    let
      (setC, cond') = simplifyFun' cond
      (setS, step') = simplifyFunWithUniqueness us step
      set = setC `IdxSet.union` setS `IdxSet.union` variableIndices us initial
    in
      ( set
      , \env ->
          let
            env' = invalidate set env
          in
            awhileSimplifyInvariant us (cond' env') (step' env') $ simplifyReturnVars env us initial
      )

variableIndices :: Uniquenesses t -> GroundVars env t -> IdxSet env
variableIndices (TupRsingle Unique) (TupRsingle var) = IdxSet.singleton $ varIdx var
variableIndices (TupRpair u1 u2) (TupRpair v1 v2) = variableIndices u1 v1 `IdxSet.union` variableIndices u2 v2
variableIndices _ _ = IdxSet.empty

simplifyReturnVars :: InfoEnv env -> Uniquenesses t -> GroundVars env t -> GroundVars env t
simplifyReturnVars env (TupRpair u1 u2) (TupRpair v1 v2) =
  simplifyReturnVars env u1 v1 `TupRpair` simplifyReturnVars env u2 v2
simplifyReturnVars env (TupRsingle Shared) v = mapTupR (weaken $ substitute env) v
simplifyReturnVars env (TupRsingle Unique) v = mapTupR (weaken $ substituteOutput env) v
simplifyReturnVars _   TupRunit _ = TupRunit
simplifyReturnVars _   _ _ = internalError "Tuple mismatch"

findConstant :: forall env env' t. WEnv' Info env' env -> ScalarType t -> t -> Maybe (Idx env t)
findConstant env tp1 value1 = go env
  where
    go :: WEnv' Info env2 env1 -> Maybe (Idx env1 t)
    go WEmpty = Nothing
    go (WPushA e (InfoConst tp2 value2))
      | Just idx <- tryMatch tp2 value2 = Just idx
    go (WPushB e (InfoConst tp2 value2))
      | Just idx <- tryMatch tp2 value2 = Just idx
    go (WPushA e _) = SuccIdx <$> go e
    go (WPushB e _) = SuccIdx <$> go e
    go (WWeaken _ e) = go e

    tryMatch :: ScalarType s -> s -> Maybe (Idx (env3, s) t)
    tryMatch tp2 value2
      | Just Refl <- matchScalarType tp1 tp2
      = case tp1 of
          SingleScalarType t
            | SingleDict <- singleDict t -- Gives 'Eq t'
            , value1 == value2 -> Just ZeroIdx
          VectorScalarType (VectorType _ t)
            | SingleDict <- singleDict t
            , value1 == value2 -> Just ZeroIdx
          _ -> Nothing
      | otherwise = Nothing

bindingEnv :: forall op t env env'. SimplifyOperation op => IdxSet env -> GLeftHandSide t env env' -> OperationAcc op env t -> InfoEnv env -> InfoEnv env'
bindingEnv _ lhs (Compute expr) (InfoEnv environment) = InfoEnv $ go weakenId lhs expr environment
  where
    go :: env :> env1 -> GLeftHandSide s env1 env2 -> Exp env s -> WEnv' Info env1 env1 -> WEnv' Info env2 env2
    go k (LeftHandSideSingle _) e env
      | ArrayInstr (Parameter var) _ <- e = wpush env (InfoAlias $ weaken (weakenSucc' k) $ varIdx var)
      | Const tp c <- e = case findConstant env tp c of
        Just idx -> wpush env (InfoAlias $ SuccIdx idx)
        Nothing -> wpush env (InfoConst tp c)
      | otherwise = wpush env InfoNone

    go k (LeftHandSidePair l1 l2) (Pair e1 e2) env
      = go (weakenWithLHS l1 .> k) l2 e2 $ go k l1 e1 env

    go k (LeftHandSideWildcard _) _ env = env

    go _ l _ env = goUnknown l env

    goUnknown :: GLeftHandSide s env1 env2 -> WEnv' Info env1 env1 -> WEnv' Info env2 env2
    goUnknown (LeftHandSideSingle _)   env = wpush env InfoNone
    goUnknown (LeftHandSideWildcard _) env = env
    goUnknown (LeftHandSidePair l1 l2) env = goUnknown l2 $ goUnknown l1 env
bindingEnv _ lhs (Return variables) (InfoEnv environment) = InfoEnv $ weaken (weakenWithLHS lhs) $ go lhs variables environment
  where
    go :: GLeftHandSide s env1 env2 -> GroundVars env s -> WEnv' Info env env1 -> WEnv' Info env env2
    go (LeftHandSideSingle _)   (TupRsingle (Var _ ix)) env = wpush' env $ InfoAlias ix
    go (LeftHandSidePair l1 l2) (TupRpair v1 v2)        env = go l2 v2 $ go l1 v1 env
    go (LeftHandSideWildcard _) _                       env = env
    go _                        _                       _   = internalError "Tuple mismatch"
bindingEnv _ (LeftHandSideSingle _) (Unit (Var _ idx)) (InfoEnv env) = InfoEnv $ wpush env $ InfoBuffer (Just $ SuccIdx idx) Nothing []
bindingEnv outputs (LeftHandSideWildcard _) (Exec op args)      env = foldl' addCopy env $ detectCopy op args
  where
    addCopy :: InfoEnv env -> CopyOperation env -> InfoEnv env
    addCopy env' (CopyOperation input output)
      | input `IdxSet.member` outputs = env' -- The operation both reads and writes to 'input'. We cannot register input and output as copies, as input will get different values
      | otherwise = InfoEnv $ wupdate markCopy input $ wupdate (const $ InfoBuffer Nothing (Just input) []) output $ unInfoEnv env'
      where
        markCopy (InfoBuffer unitScalar copyOf list) = InfoBuffer unitScalar copyOf (output : list)
        markCopy (InfoAlias _) = internalError "Operation contains aliased variable, which should be substituted already"
        markCopy _ = (InfoBuffer Nothing Nothing [output])
bindingEnv _ lhs _ env = bindEnv lhs env

-- Updates the InfoEnv, with the information that the buffers in 'indices' may
-- have been updated. This breaks the 'is-copy-of' relation between buffers.
invalidate :: forall env. IdxSet env -> InfoEnv env -> InfoEnv env
invalidate indices infoEnv@(InfoEnv env1) =
  InfoEnv
    $ wupdateSetWeakened dropCopyTo indicesCopiesOf
    $ wupdateSetWeakened dropCopyOf indicesCopiedTo
    $ wremoveSet InfoNone indices' env1
  where
    indices' :: IdxSet env
    indices' = IdxSet.map (weaken $ substituteOutput infoEnv) indices

    findCopies :: Exists (Idx env) -> (IdxSet env, IdxSet env)
    findCopies (Exists idx) = case infoFor idx infoEnv of
      InfoAlias idx' -> internalError "Alias should be substituted already"
      InfoBuffer _ (Just idx') copies -> (IdxSet.singleton idx', IdxSet.fromList' copies)
      _ -> (IdxSet.empty, IdxSet.empty)

    (indicesCopiesOf', indicesCopiedTo') = unzip $ map findCopies $ IdxSet.toList indices'
    indicesCopiesOf = IdxSet.unions indicesCopiesOf'
    indicesCopiedTo = IdxSet.unions indicesCopiedTo'

    -- Forgets that this buffer is a copy of a buffer in indices'.
    dropCopyOf :: env' :> env -> Info env' t -> Info env' t
    dropCopyOf _ (InfoBuffer unitScalar _ c)
      = InfoBuffer unitScalar Nothing c

    -- Forgets that this buffer is copied to buffers in indices'
    dropCopyTo :: env' :> env -> Info env' t -> Info env' t
    dropCopyTo k (InfoBuffer unitScalar copyOf copiedTo')
      = InfoBuffer unitScalar copyOf $ filter (\idx -> not $ k >:> idx `IdxSet.member` indices) copiedTo'

outputArrays :: Args env args -> IdxSet env
outputArrays = IdxSet.fromList . mapMaybe f . argsVars
  where
    f :: Exists (Var AccessGroundR env) -> Maybe (Exists (Idx env))
    f (Exists (Var (AccessGroundRbuffer In _) _)) = Nothing
    f (Exists (Var (AccessGroundRbuffer _ _) idx)) = Just (Exists idx) -- Out or Mut
    f _ = Nothing

simplifyExp :: forall env t. InfoEnv env -> Exp env t -> Exp env t
simplifyExp env = Exp.simplifyExp . runIdentity . rebuildArrayInstrOpenExp (simplifyArrayInstr env)

simplifyExpFun :: forall env t. InfoEnv env -> Fun env t -> Fun env t
simplifyExpFun env = Exp.simplifyFun . runIdentity . rebuildArrayInstrFun (simplifyArrayInstr env)

simplifyArrayInstr :: InfoEnv env -> RebuildArrayInstr Identity (ArrayInstr env) (ArrayInstr env)
simplifyArrayInstr env instr@(Parameter (Var tp idx)) = case infoFor idx env of
  InfoAlias idx'   -> simplifyArrayInstr env (Parameter $ Var tp idx')
  InfoConst _ c    -> Identity $ const $ Const tp c
  InfoBuffer _ _ _ -> bufferImpossible tp
  InfoNone         -> Identity $ \arg -> ArrayInstr instr arg
simplifyArrayInstr env instr@(Index (Var tp idx)) = case infoFor idx env of
  InfoAlias idx' -> simplifyArrayInstr env (Index $ Var tp idx')
  InfoBuffer (Just idx') _ _ -> Identity $ const $ runIdentity (simplifyArrayInstr env $ Parameter $ Var eltTp idx') Nil -- Unit
  InfoBuffer _ (Just idx') _  -> simplifyArrayInstr env (Index $ Var tp idx') -- Copy
  _              -> Identity $ \arg -> ArrayInstr instr arg
  where
    eltTp = case tp of
      GroundRscalar t -> bufferImpossible t
      GroundRbuffer t -> t

simplifyArg :: InfoEnv env -> Arg env t -> Arg env t
simplifyArg env (ArgVar var)  = ArgVar $ mapTupR (weaken $ substitute env) var
simplifyArg env (ArgExp expr) = ArgExp $ simplifyExp env expr
simplifyArg env (ArgFun fun)  = ArgFun $ simplifyExpFun env fun
simplifyArg env (ArgArray m repr sh buffers)
  = ArgArray m repr (mapTupR (weaken $ substitute env) sh) (mapTupR (weaken $ substituteBuffer env) buffers)
  where
    -- Output buffers may not be substituted by buffers with the same content.
    substituteBuffer
      | In <- m = substitute
      | Out <- m = substituteOutput
      | Mut <- m = const weakenId

bindEnv :: GLeftHandSide t env env' -> InfoEnv env -> InfoEnv env'
bindEnv lhs (InfoEnv env') = InfoEnv $ go lhs $ weaken k env'
  where
    k = weakenWithLHS lhs

    go :: GLeftHandSide t env1 env1' -> WEnv' Info env' env1 -> WEnv' Info env' env1'
    go (LeftHandSideWildcard _) env1 = env1
    go (LeftHandSideSingle _)   env1 = wpush' env1 InfoNone
    go (LeftHandSidePair l1 l2) env1 = go l2 $ go l1 env1

unionSubTupR :: SubTupR t s -> SubTupR t s' -> Exists (SubTupR t)
unionSubTupR SubTupRskip s = Exists s
unionSubTupR s SubTupRskip = Exists s
unionSubTupR (SubTupRpair l1 r1) (SubTupRpair l2 r2)
  | Exists l <- unionSubTupR l1 l2
  , Exists r <- unionSubTupR r1 r2
  = Exists $ subTupRpair l r
unionSubTupR _ _ = Exists SubTupRkeep

-- Detects which parts of the state of an awhile loop are invariant and
-- transforms the program accordingly.
-- For instance, if the state of an awhile loop contains an array whose
-- shape doesn't change throughout the execution of the awhile loop,
-- it will remove the shape from the state of the loop and always refer
-- to the initial shape of the array.
awhileSimplifyInvariant
  :: Uniquenesses a
  -> PreOpenAfun op env (a -> PrimBool)
  -> PreOpenAfun op env (a -> a)
  -> GroundVars     env a
  -> PreOpenAcc  op env a
awhileSimplifyInvariant us cond step initial = case awhileDropInvariantFun step of
  Exists SubTupRkeep -> Awhile us cond step initial
  Exists sub
    | Just Refl <- subTupPreserves tp sub -> Awhile us cond step initial
    | DeclareVars lhs k value <- declareVars $ subTupR sub tp ->
      alet' lhs (subTupR sub us)
        (Awhile (subTupR sub us)
          (subTupFunctionArgument sub initial cond)
          (subTupFunctionArgument sub initial $ subTupFunctionResult sub step)
          (subTupR sub initial))
        (Return $ subTupResult sub (mapTupR (weaken k) initial) (value weakenId))
  where
    tp = case cond of
      Alam lhs _ -> lhsToTupR lhs
      Abody body -> groundFunctionImpossible $ groundsR body

awhileDropInvariantFun :: OperationAfun op env (t -> t) -> Exists (SubTupR t)
awhileDropInvariantFun (Alam lhs (Abody body)) = awhileDropInvariant (lhsMaybeVars lhs) body
awhileDropInvariantFun (Alam lhs (Alam _ _))   = groundFunctionImpossible (lhsToTupR lhs)
awhileDropInvariantFun (Abody body)            = groundFunctionImpossible (groundsR body)

awhileDropInvariant :: MaybeVars GroundR env t -> OperationAcc op env t -> Exists (SubTupR t)
awhileDropInvariant argument = \case
  Return vars
    -> matchReturn argument vars
  Alet (LeftHandSideWildcard _) _ _ body
    -> awhileDropInvariant argument body
  Alet lhs _ _ body
    -> awhileDropInvariant (mapTupR (weaken $ weakenWithLHS lhs) argument) body
  Acond _ t f
    | Exists subTupT <- awhileDropInvariant argument t
    , Exists subTupF <- awhileDropInvariant argument f
    -> unionSubTupR subTupT subTupF
  _ -> Exists SubTupRkeep -- No invariant variables
  where
    matchReturn :: MaybeVars GroundR env t' -> GroundVars env t' -> Exists (SubTupR t')
    matchReturn (TupRpair a1 a2) (TupRpair v1 v2)
      | Exists s1 <- matchReturn a1 v1
      , Exists s2 <- matchReturn a2 v2
      = case (s1, s2) of
          (SubTupRskip, SubTupRskip) -> Exists SubTupRskip
          _ -> Exists $ subTupRpair s1 s2
    matchReturn (TupRsingle (JustVar arg)) (TupRsingle var)
      | Just Refl <- matchVar arg var = Exists SubTupRskip
    matchReturn TupRunit _ = Exists SubTupRskip
    matchReturn _ _ = Exists SubTupRkeep

subTupFunctionResult :: SubTupR t t' -> OperationAfun op env (ta -> t) -> OperationAfun op env (ta -> t')
subTupFunctionResult sub (Alam lhs (Abody body)) = Alam lhs $ Abody $ subTupAcc sub body
subTupFunctionResult _ _ = internalError "Illegal function"

subTupAcc :: SubTupR t t' -> OperationAcc op env t -> OperationAcc op env t'
subTupAcc sub = \case
  Return vars -> Return $ subTupR sub vars
  Alet lhs us bnd body -> Alet lhs us bnd $ subTupAcc sub body
  Acond c t f -> Acond c (subTupAcc sub t) (subTupAcc sub f)
  _ -> internalError "Cannot subTup this program"

subTupFunctionArgument :: SubTupR t t' -> GroundVars env t -> OperationAfun op env (t -> tr) -> OperationAfun op env (t' -> tr)
subTupFunctionArgument sub initial (Alam lhs body)
  | SubTupSubstitution lhs' k <- subTupSubstitution sub lhs initial
  = Alam lhs' $ weaken k body
subTupFunctionArgument _ _ (Abody body) = groundFunctionImpossible $ groundsR body

subTupResult :: SubTupR t t' -> GroundVars env t -> GroundVars env t' -> GroundVars env t
subTupResult SubTupRkeep _ result = result
subTupResult SubTupRskip initial _ = initial
subTupResult (SubTupRpair s1 s2) (TupRpair i1 i2) (TupRpair r1 r2) = subTupResult s1 i1 r1 `TupRpair` subTupResult s2 i2 r2
subTupResult _ _ _ = internalError "Tuple mismatch"

data SubTupSubstitution env env1 t t' where
  SubTupSubstitution
    :: GLeftHandSide t' env1 env2
    -> env :> env2
    -> SubTupSubstitution env env1 t t'

subTupSubstitution :: SubTupR t t' -> GLeftHandSide t env env' -> GroundVars env t -> SubTupSubstitution env' env t t'
subTupSubstitution SubTupRskip lhs vars = SubTupSubstitution (LeftHandSideWildcard TupRunit) (go lhs vars weakenId)
  where
    go :: GLeftHandSide s env1 env2 -> GroundVars env s -> env1 :> env -> env2 :> env
    go (LeftHandSideWildcard _) _ k = k
    go (LeftHandSideSingle _)   (TupRsingle (Var _ ix)) k = Weaken $ \case
      ZeroIdx -> ix
      SuccIdx ix' -> k >:> ix'
    go (LeftHandSidePair l1 l2) (TupRpair v1 v2) k = go l2 v2 $ go l1 v1 k
    go _ _ _ = internalError "Tuple mismatch"
subTupSubstitution SubTupRkeep lhs _ = SubTupSubstitution lhs weakenId
subTupSubstitution (SubTupRpair s1 s2) (LeftHandSidePair l1 l2) (TupRpair v1 v2)
  | SubTupSubstitution l1' k1 <- subTupSubstitution s1 l1 v1
  , Exists l2'' <- rebuildLHS l2
  , SubTupSubstitution l2' k2 <- subTupSubstitution s2 l2'' (mapTupR (weaken $ weakenWithLHS l1') v2)
  = SubTupSubstitution (LeftHandSidePair l1' l2') (k2 .> sinkWithLHS l2 l2'' k1)
subTupSubstitution s (LeftHandSideWildcard t) _
  = SubTupSubstitution (LeftHandSideWildcard $ subTupR s t) weakenId
subTupSubstitution _ _ _ = internalError "Tuple mismatch"
