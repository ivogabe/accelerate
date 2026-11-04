{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MultiWayIf #-}
{-# OPTIONS_HADDOCK hide #-}

-- |
-- Module      : Data.Array.Accelerate.Trafo.Operation.LiveVars
-- Copyright   : [2012..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.Trafo.Operation.LiveVars (
  module Data.Array.Accelerate.Trafo.LiveVars,

  stronglyLiveVariables, stronglyLiveVariablesFun,

  SLVExecute(..), ShrinkExecute(..), ShrunkExecute(..),
  SLVOperation(..), ShrinkOperation(..), ShrunkOperation(..),
  SubArgs(..), SubArg(..),
  reEnvArrayInstr, 
  reEnvArrayDescriptors,
  composeSubArgs,

  defaultSlvGenerate, defaultSlvMap, defaultSlvBackpermute,
) where

import qualified Data.Array.Accelerate.AST.IdxSet as IdxSet
import Data.Array.Accelerate.AST.Idx
import Data.Array.Accelerate.AST.Var
import Data.Array.Accelerate.AST.LeftHandSide
import Data.Array.Accelerate.AST.Operation
import Data.Array.Accelerate.AST.Partitioned
import Data.Array.Accelerate.AST.Environment
import Data.Array.Accelerate.Representation.Array
import Data.Array.Accelerate.Representation.Shape
import Data.Array.Accelerate.Representation.Type
import Data.Array.Accelerate.Trafo.Exp.Substitution
import Data.Array.Accelerate.Trafo.LiveVars
import Data.Array.Accelerate.Error

import Data.Type.Equality
import Data.Maybe (mapMaybe)
import Data.Kind

stronglyLiveVariablesFun :: SLVExecute exe => PreOpenAfun exe () t -> PreOpenAfun exe () t
stronglyLiveVariablesFun acc = acc' ReEnvEnd
  where
    LVAnalysisFun _ acc' = stronglyLiveVariablesFun' emptyLivenessEnv acc

stronglyLiveVariables :: SLVExecute exe => PreOpenAcc exe () t -> PreOpenAcc exe () t
stronglyLiveVariables acc = fromEither' $ acc' ReEnvEnd SubTupRkeep
  where
    LVAnalysis _ acc' = stronglyLiveVariables' emptyLivenessEnv returnImplicationsLive (mapTupR (const Shared) $ groundsR acc) acc

stronglyLiveVariablesFun' :: SLVExecute exe => LivenessEnv env -> PreOpenAfun exe env t -> LVAnalysisFun (PreOpenAfun exe) env t
stronglyLiveVariablesFun' liveness (Alam lhs f)
  | liveness1 <- lEnvPushLHS lhs liveness
  , LVAnalysisFun liveness2 f' <- stronglyLiveVariablesFun' liveness1 f
  , (lhs', liveness3) <- lEnvStrengthenLHS lhs liveness2
  = LVAnalysisFun
      liveness3
      $ \re -> if
        | BindLiveness lhs'' re' <- bind lhs' re ->
          Alam lhs'' $ f' re'
stronglyLiveVariablesFun' liveness (Abody body)
  | LVAnalysis liveness1 body' <- stronglyLiveVariables' liveness returnImplicationsLive (mapTupR (const Shared) $ groundsR body) body
  = LVAnalysisFun
      liveness1
      $ \re -> Abody $ fromEither' $ body' re SubTupRkeep

stronglyLiveVariablesFun'' :: SLVExecute exe => LivenessEnv env -> Uniquenesses t -> PreOpenAfun exe env (s -> t) -> LVAnalysisFun (PreOpenAfun exe) env (s -> t)
stronglyLiveVariablesFun'' liveness us (Alam lhs (Abody body))
  | liveness1 <- lEnvPushLHS lhs liveness
  , LVAnalysis liveness2 body' <- stronglyLiveVariables' liveness1 returnImplicationsLive us body
  , (lhs', liveness3) <- lEnvStrengthenLHS lhs liveness2
  = LVAnalysisFun
      liveness3
      $ \re -> if
        | BindLiveness lhs'' re' <- bind lhs' re ->
          Alam lhs'' $ Abody $ fromEither' $ body' re' SubTupRkeep
stronglyLiveVariablesFun'' _ _ _ = internalError "Expected unary function"

fromEither' :: Either a a -> a
fromEither' (Left  x) = x
fromEither' (Right x) = x

stronglyLiveVariables' :: SLVExecute exe => LivenessEnv env -> ReturnImplications env t -> Uniquenesses t -> PreOpenAcc exe env t -> LVAnalysis (PreOpenAcc exe) env t
stronglyLiveVariables' liveness returns us = \case
  Exec exe args
    | Just (ShrinkExecute shrinkExe) <- slvExecute exe
    -- We can shrink this operation to output to part of its buffers.
    , input <- IdxSet.fromList $ argsInputs args
    , output <- IdxSet.fromList $ argsOutputs args
    , liveness1 <- addLiveImplications output input liveness ->
      LVAnalysis
        liveness1
        $ \re s -> if
          | Refl <- subTupUnit s
          , allDead re output ->
            Right $ Return TupRunit

          | Refl <- subTupUnit s
          , ReEnvSubArgs subArgs args' <- reEnvSubArgs re args
          , ShrunkExecute exe' args'' <- shrinkExe subArgs args' args ->
            Right $ Exec exe' args''

    -- We cannot shrink this operation to only output a part of its buffers.
    -- Hence it's "all or nothing", if we use at least one of the output
    -- buffers, then the entire operation is live.
    | free <- IdxSet.fromList $ map (\(Exists (Var _ idx)) -> Exists idx) $ argsVars args
    , output <- IdxSet.fromList $ argsOutputs args
    , liveness1 <- addLiveImplications output free liveness ->
      LVAnalysis
        liveness1
        $ \re s -> if
          | Refl <- subTupUnit s
          , allDead re output ->
            Right $ Return TupRunit -- All output vars are dead

          | Refl <- subTupUnit s
          , args' <- reEnvArgs re args ->
            Right $ Exec exe args' -- Live
  Return vars
    | liveness1 <- returnVars returns vars liveness ->
      LVAnalysis
        liveness1
        $ \re s -> Right $ Return $ expectJust $ reEnvVars re $ subTupR s vars
  Manifest var
    | liveness1 <- returnVars returns (TupRsingle var) liveness ->
      LVAnalysis
        liveness1
        $ \re s -> case s of
          SubTupRskip -> Right $ Return TupRunit
          SubTupRkeep -> Right $ Manifest $ expectJust $ reEnvVar re var
  Compute expr -> stronglyLiveVariablesComputeLike (const Compute) liveness returns expr
  Aassert msg cond -> stronglyLiveVariablesComputeLike
    (\s -> case s of
      SubTupRkeep -> Aassert msg
      SubTupRskip -> const $ Return TupRunit) -- Should not occur
    liveness returns cond
  Aassume cond -> stronglyLiveVariablesComputeLike
    (\s -> case s of
      SubTupRkeep -> Aassume
      SubTupRskip -> const $ Return TupRunit) -- Should not occur
    liveness returns cond
  Alet lhs us' bnd body
    | liveness1 <- lEnvPushLHS lhs liveness
    , LVAnalysis liveness2 body' <- stronglyLiveVariables' liveness1 (returnImplicationsWeakenByLHS lhs returns) us body
    , (lhs', liveness3, returns') <- lEnvStrengthenLHSReturn lhs liveness2
    , LVAnalysis liveness4 bnd' <- stronglyLiveVariables' liveness3 returns' us' bnd ->
      LVAnalysis
        liveness4
        $ \re s -> case bindSub lhs' re of
          BindLivenessSub subTup' lhsFull lhsSub re' -> case (bnd' re subTup', body' re' s) of
            (Left bnd'',  Left body'')  -> Left  $ mkAlet lhsFull us' bnd'' body''
            (Left bnd'',  Right body'') -> Right $ mkAlet lhsFull us' bnd'' body''
            (Right bnd'', Left body'')  -> Left  $ mkAlet lhsSub (subTupUniqueness subTup' us') bnd'' body''
            (Right bnd'', Right body'') -> Right $ mkAlet lhsSub (subTupUniqueness subTup' us') bnd'' body''
  Alloc shr tp sh
    | free <- IdxSet.fromVars sh
    , liveness1 <- returnIndices returns free liveness ->
      LVAnalysis
        liveness1
        $ \re s ->
          case s of
            SubTupRskip -> Right $ Return TupRunit
            SubTupRkeep -> Right $ Alloc shr tp $ expectJust $ reEnvVars re sh
  Use tp size' buffer ->
    LVAnalysis
      liveness
      $ \_ s ->
        case s of
          SubTupRskip -> Right $ Return TupRunit
          SubTupRkeep -> Right $ Use tp size' buffer
  Unit var
    | free <- IdxSet.singleton $ varIdx var
    , liveness1 <- returnIndices returns free liveness ->
      LVAnalysis
        liveness1
        $ \re s ->
          case s of
            SubTupRskip -> Right $ Return TupRunit
            SubTupRkeep -> Right $ Unit $ expectJust $ reEnvVar re var
  Acond condition true false
    | liveness1 <- setLive (varIdx condition) liveness
    , LVAnalysis liveness2 true'  <- stronglyLiveVariables' liveness1 returns us true
    , LVAnalysis liveness3 false' <- stronglyLiveVariables' liveness2 returns us false ->
      LVAnalysis
        liveness3
        $ \re s ->
          let condition' = expectJust $ reEnvVar re condition
          in case (true' re s, false' re s) of
              (Left  true'', Left  false'') -> Left  $ mkAcond condition' true'' false''
              (Right true'', Right false'') -> Right $ mkAcond condition' true'' false''
              (Left  true'', Right false'')
                | SubTupRkeep <- s     -> Left  $ mkAcond condition' true'' false''
                | DeclareSubVars lhs _ vars <- declareSubVars (groundsR true) s
                -> Right $ Acond condition' (Alet lhs us true'' $ Return $ vars weakenId) false''
              (Right true'', Left  false'')
                | SubTupRkeep <- s     -> Left  $ mkAcond condition' true'' false''
                | DeclareSubVars lhs _ vars <- declareSubVars (groundsR true) s
                -> Right $ Acond condition' true'' (Alet lhs us false'' $ Return $ vars weakenId)
  Awhile us' condition step initial
    | liveness1 <- setVarsLive initial liveness
    , LVAnalysisFun liveness2 condition' <- stronglyLiveVariablesFun'' liveness1 (TupRsingle Shared) condition
    , LVAnalysisFun liveness3 step'      <- stronglyLiveVariablesFun'' liveness2 us' step ->
      LVAnalysis
        liveness3
        $ \re _ ->
          Left $ Awhile us' (condition' re) (step' re) $ expectJust $ reEnvVars re initial
  Atrace msg t
    | free <- arrayDescriptorsIdxSet t
    , liveness1 <- returnIndices returns free liveness ->
      LVAnalysis
        liveness1
        $ \re s -> case s of
          SubTupRkeep -> Right $ Atrace msg $ reEnvArrayDescriptors re t
          SubTupRskip -> Right $ Return TupRunit

  Fence set next
    | liveness1 <- setIdxSetLive set liveness
    , LVAnalysis liveness2 next' <- stronglyLiveVariables' liveness1 returns us next ->
      LVAnalysis
        liveness2
        $ \re s ->
          let set' = reEnvIdxSet re set
          in case next' re s of
              Left  next'' -> Left  $ Fence set' next''
              Right next'' -> Right $ Fence set' next''
  where
    mkAcond :: ExpVar env' PrimBool -> PreOpenAcc exe env' t' -> PreOpenAcc exe env' t' -> PreOpenAcc exe env' t'
    mkAcond _         (Return TupRunit) (Return TupRunit) = Return TupRunit
    mkAcond condition true              false             = Acond condition true false

    mkAlet :: GLeftHandSide bnd subenv subenv' -> Uniquenesses bnd -> PreOpenAcc exe subenv bnd -> PreOpenAcc exe subenv' t -> PreOpenAcc exe subenv t
    mkAlet (LeftHandSideWildcard TupRunit) _ (Return TupRunit) body = body
    mkAlet lhs us' bnd body = Alet lhs us' bnd body

-- Implementation of stronglyLiveVariables' for Compute, Aassert and Aassume
stronglyLiveVariablesComputeLike
  :: SLVExecute exe
  => (forall env' t'. SubTupR t t' -> Exp env' t' -> PreOpenAcc exe env' t')
  -> LivenessEnv env
  -> ReturnImplications env t
  -> Exp env t
  -> LVAnalysis (PreOpenAcc exe) env t
stronglyLiveVariablesComputeLike constructor liveness returns expr
  -- If the LHS of the binding is live, then all free variables of this
  -- expression are live as well.
  | free <- expGroundVars expr
  , liveness1 <- returnIndices returns (IdxSet.fromVarList free) liveness =
    LVAnalysis
      liveness1
      $ \re s ->
        let
          tp = expType expr
          expr' = mapArrayInstr (reEnvArrayInstr re) expr
        in case s of
            SubTupRskip -> Right $ Return TupRunit
            SubTupRkeep -> Right $ constructor s $ expr'
            _ | DeclareSubVars lhs _ vars <- declareSubVars tp s
              -> Right $ constructor s $ Let lhs expr' $ returnExpVars $ vars weakenId

reEnvIdxSet :: ReEnv env subenv -> IdxSet.IdxSet env -> IdxSet.IdxSet subenv
reEnvIdxSet re idxSet =
  IdxSet.fromList $
    mapMaybe (\(Exists ix) -> fmap Exists (reEnvIdx re ix))
             (IdxSet.toList idxSet)

class SLVOperation (op :: Bool -> Type -> Type) where
  slvOperation :: op b f -> Maybe (ShrinkOperation op b f)

class SLVExecute (exe :: Type -> Type) where
  slvExecute :: exe f -> Maybe (ShrinkExecute exe f)

newtype ShrinkOperation (op :: Bool -> Type -> Type) (b :: Bool) f = ShrinkOperation (forall f' env' env. SubArgs f f' -> Args env' f' -> Args env f -> ShrunkOperation op b env')
newtype ShrinkExecute (exe :: Type -> Type) f = ShrinkExecute (forall f' env' env. SubArgs f f' -> Args env' f' -> Args env f -> ShrunkExecute exe env')

-- existential over f: otherwise, you couldn't change the non-array arguments. You need this e.g. for a Generate: smaller array means smaller function.
data ShrunkOperation op b env where
  ShrunkOperation :: op b f -> Args env f -> ShrunkOperation op b env
data ShrunkExecute exe env where
  ShrunkExecute :: exe f -> Args env f -> ShrunkExecute exe env

instance SLVOperation op => SLVExecute (ExecOp op) where
  slvExecute (ExecOp fusible op) = case slvOperation op of
    Just (ShrinkOperation shrinkOp) -> Just $ ShrinkExecute $ \sa args' args ->
      case shrinkOp sa args' args of
        ShrunkOperation op' args'' ->
          ShrunkExecute (ExecOp fusible op') args''
    Nothing -> Nothing

instance SLVOperation op => SLVExecute (ExecCluster op) where
  slvExecute (ExecSingle op) = case slvOperation op of
    Just (ShrinkOperation shrinkOp) -> Just $ ShrinkExecute $ \sa args' args ->
      case shrinkOp sa args' args of
        ShrunkOperation op' args'' ->
          ShrunkExecute (ExecSingle op') args''
    Nothing -> Nothing
  slvExecute (ExecClustered cluster) = Just $ ShrinkExecute $ \ff' a' a ->
    case slvCluster cluster ff' a' a of
      ShrunkOperation' cluster' args ->
        ShrunkExecute (ExecClustered cluster') args

slvClusterArg :: forall f f' t. SubArgs f f' -> ClusterArg (FunToEnv f) t -> ClusterArg (FunToEnv f') t
slvClusterArg subArgs (ClusterArgSingle idx) = case reindexSlv subArgs idx of
  ReindexSlvKeep idx' -> ClusterArgSingle idx'
  _ -> internalError "Expected a preserved variable, as this is not an Out argument"
slvClusterArg subArgs (ClusterArgArray m shr tp buffers) = ClusterArgArray m shr tp $ go buffers
  where
    go :: ClusterArgBuffers (FunToEnv f) m sh e -> ClusterArgBuffers (FunToEnv f') m sh e
    go (ClusterArgBuffersPair a1 a2) = go a1 `ClusterArgBuffersPair` go a2
    go (ClusterArgBuffersDead tp' idx) = case reindexSlv subArgs idx of
      ReindexSlvKeep idx' -> ClusterArgBuffersDead tp' idx'
    go (ClusterArgBuffersLive tp' idx) = case reindexSlv subArgs idx of
      ReindexSlvKeep idx' -> ClusterArgBuffersLive tp' idx'
      ReindexSlvDead idx' -> ClusterArgBuffersDead tp' idx'

reindexSlv :: SubArgs f f' -> Idx (FunToEnv f) t -> ReindexSlv f' t
reindexSlv (SubArgsDead _) ZeroIdx = ReindexSlvDead ZeroIdx
reindexSlv (SubArgsLive arg _) ZeroIdx = case arg of
  SubArgKeep -> ReindexSlvKeep ZeroIdx
  SubArgOut SubTupRkeep -> ReindexSlvKeep ZeroIdx
  _ -> internalError "Expected preserved value"
reindexSlv (SubArgsDead s) (SuccIdx idx) = case reindexSlv s idx of
  ReindexSlvKeep idx' -> ReindexSlvKeep $ SuccIdx idx'
  ReindexSlvDead idx' -> ReindexSlvDead $ SuccIdx idx'
reindexSlv (SubArgsLive _ s) (SuccIdx idx) = case reindexSlv s idx of
  ReindexSlvKeep idx' -> ReindexSlvKeep $ SuccIdx idx'
  ReindexSlvDead idx' -> ReindexSlvDead $ SuccIdx idx'
reindexSlv SubArgsNil idx = case idx of {}

data ReindexSlv f t where
  ReindexSlvKeep :: Idx (FunToEnv f) t -> ReindexSlv f t
  ReindexSlvDead :: Idx (FunToEnv f) (Var' sh) -> ReindexSlv f (Out sh e)

slvCluster :: Cluster op f -> SubArgs f f' -> Args env' f' -> Args env f -> ShrunkOperation' (Cluster op) env' f'
slvCluster (SingleOp (Single op args) label) sub args' _
  = ShrunkOperation' (SingleOp (Single op $ mapArgs (slvClusterArg sub) args) label) args'

slvCluster (Fused fusion leftCluster rightCluster) sub args1' args1 = splitslvstuff fusion sub args1' args1 $
  \f' lsub largs' largs rsub rargs' rargs -> case (slvCluster leftCluster lsub largs' largs, slvCluster rightCluster rsub rargs' rargs) of
    (ShrunkOperation' lop largs'', ShrunkOperation' rop rargs'') ->
      ShrunkOperation' (Fused f' lop rop) (both (\x _ -> outvar x) f' largs'' rargs'')
  where
    splitslvstuff :: Fusion l r a
      -> SubArgs a a'
      -> Args env' a'
      -> Args env a
      -> (forall l' r'. Fusion l' r' a' -> SubArgs l l' -> Args env' l' -> Args env l -> SubArgs r r' -> Args env' r' -> Args env r -> result)
      -> result
    splitslvstuff EmptyF SubArgsNil ArgsNil ArgsNil k = k EmptyF SubArgsNil ArgsNil ArgsNil SubArgsNil ArgsNil ArgsNil
    splitslvstuff _ (SubArgsLive (SubArgOut SubTupRskip) _) _ _ _ = error "completely removed out arg using subtupr" --splitslvstuff f (SubArgsDead subs) args' args k
    splitslvstuff f (SubArgsLive (SubArgOut SubTupRkeep) subs) args' args k = splitslvstuff f (SubArgsLive SubArgKeep subs) args' args k
    splitslvstuff _ (SubArgsLive (SubArgOut SubTupRpair{}) _) (_:>:_) (_:>:_) _ = error "not SOA'd array"
    splitslvstuff (Diagonal   f) (SubArgsDead subs) args' (ArgArray _ r sh _:>:args) k = splitslvstuff (Vertical r f) (SubArgsLive SubArgKeep subs) args' (ArgVar (groundToExpVar (shapeType $ arrayRshape r) sh) :>:args) k
    splitslvstuff (IntroO1    f) (SubArgsDead subs) (arg':>:args') (arg:>:args) k = splitslvstuff f subs args' args $ \g lsubs largs' largs rsubs rargs' rargs -> k (IntroL   g) (SubArgsDead lsubs) (arg':>:largs') (arg:>:largs)              rsubs          rargs'         rargs
    splitslvstuff (IntroO2    f) (SubArgsDead subs) (arg':>:args') (arg:>:args) k = splitslvstuff f subs args' args $ \g lsubs largs' largs rsubs rargs' rargs -> k (IntroR   g)              lsubs          largs'         largs  (SubArgsDead rsubs) (arg':>:rargs') (arg:>:rargs)
    splitslvstuff (IntroL     _) (SubArgsDead _) (_:>:_) (_:>:_) _ = error "out in IntroL/R"
    splitslvstuff (IntroR     _) (SubArgsDead _) (_:>:_) (_:>:_) _ = error "out in IntroL/R"
    splitslvstuff (Vertical r  f) (SubArgsLive SubArgKeep subs) (ArgVar arg':>:args') (ArgVar arg:>:args) k = splitslvstuff f subs args' args $ \g lsubs largs' largs rsubs rargs' rargs -> k (Vertical r g) (SubArgsLive SubArgKeep lsubs) (ArgArray Out r sh' buf :>:largs') (ArgArray Out r sh buf :>:largs) (SubArgsLive SubArgKeep rsubs) (ArgArray In r sh' buf :>:rargs') (ArgArray In r sh buf :>:rargs)
      where
        buf = error "fused away buffer"
        sh = expToGroundVar arg
        sh' = expToGroundVar arg'
    splitslvstuff (Diagonal   f) (SubArgsLive SubArgKeep subs) (arg'@(ArgArray Out r' sh' buf'):>:args') (arg@(ArgArray Out r sh buf):>:args) k = splitslvstuff f subs args' args $ \g lsubs largs' largs rsubs rargs' rargs -> k (Diagonal   g) (SubArgsLive SubArgKeep lsubs) (arg':>:largs') (arg:>:largs) (SubArgsLive SubArgKeep rsubs) (ArgArray In r' sh' buf':>:rargs') (ArgArray In r sh buf:>:rargs)
    splitslvstuff (Horizontal f) (SubArgsLive SubArgKeep subs) (arg':>:args') (arg:>:args) k = splitslvstuff f subs args' args $ \g lsubs largs' largs rsubs rargs' rargs -> k (Horizontal g) (SubArgsLive SubArgKeep lsubs) (       arg':>:largs') (       arg:>:largs) (SubArgsLive SubArgKeep rsubs) (      arg':>:rargs') (      arg:>:rargs)
    splitslvstuff (IntroI1    f) (SubArgsLive SubArgKeep subs) (arg':>:args') (arg:>:args) k = splitslvstuff f subs args' args $ \g lsubs largs' largs rsubs rargs' rargs -> k (IntroI1    g) (SubArgsLive SubArgKeep lsubs) (       arg':>:largs') (       arg:>:largs)                         rsubs                rargs'               rargs
    splitslvstuff (IntroI2    f) (SubArgsLive SubArgKeep subs) (arg':>:args') (arg:>:args) k = splitslvstuff f subs args' args $ \g lsubs largs' largs rsubs rargs' rargs -> k (IntroI2    g)                         lsubs                 largs'                largs  (SubArgsLive SubArgKeep rsubs) (      arg':>:rargs') (      arg:>:rargs)
    splitslvstuff (IntroO1    f) (SubArgsLive SubArgKeep subs) (arg':>:args') (arg:>:args) k = splitslvstuff f subs args' args $ \g lsubs largs' largs rsubs rargs' rargs -> k (IntroO1    g) (SubArgsLive SubArgKeep lsubs) (       arg':>:largs') (       arg:>:largs)                         rsubs                rargs'               rargs
    splitslvstuff (IntroO2    f) (SubArgsLive SubArgKeep subs) (arg':>:args') (arg:>:args) k = splitslvstuff f subs args' args $ \g lsubs largs' largs rsubs rargs' rargs -> k (IntroO2    g)                         lsubs                 largs'                largs  (SubArgsLive SubArgKeep rsubs) (      arg':>:rargs') (      arg:>:rargs)
    splitslvstuff (IntroL     f) (SubArgsLive SubArgKeep subs) (arg':>:args') (arg:>:args) k = splitslvstuff f subs args' args $ \g lsubs largs' largs rsubs rargs' rargs -> k (IntroL     g) (SubArgsLive SubArgKeep lsubs) (       arg':>:largs') (       arg:>:largs)                         rsubs                rargs'               rargs
    splitslvstuff (IntroR     f) (SubArgsLive SubArgKeep subs) (arg':>:args') (arg:>:args) k = splitslvstuff f subs args' args $ \g lsubs largs' largs rsubs rargs' rargs -> k (IntroR     g)                         lsubs                 largs'                largs  (SubArgsLive SubArgKeep rsubs) (      arg':>:rargs') (      arg:>:rargs)

-- Variant of ShrunkOperation where f is not an existential
data ShrunkOperation' op env f where
  ShrunkOperation' :: op f -> Args env f -> ShrunkOperation' op env f


data SubArgs f f' where
  SubArgsNil  :: SubArgs () ()

  -- This Out argument is dead.
  -- Note that implementers of 'slvOperation' may assume that at least one Out
  -- or Mut argument is preserved.
  SubArgsDead :: SubArgs t t'
              -> SubArgs (Out sh e -> t) (Var' sh -> t')

  SubArgsLive :: SubArg  s s'
              -> SubArgs t t'
              -> SubArgs (s -> t) (s' -> t')

infixr 9 `SubArgsLive`

data SubArg t t' where
  SubArgKeep :: SubArg t t

  SubArgOut  :: SubTupR e e'
             -> SubArg (Out sh e) (Out sh e')

defaultSlvGenerate
  :: (forall sh' t'. op b (Fun' (sh' -> t') -> Out sh' t' -> ()))
  -> Maybe (ShrinkOperation op b (Fun' (sh -> t) -> Out sh t -> ()))
defaultSlvGenerate mkGenerate = Just $ ShrinkOperation $ \subArgs args _ -> case subArgs of
  SubArgKeep `SubArgsLive` SubArgKeep `SubArgsLive` SubArgsNil
    -> ShrunkOperation mkGenerate args
  SubArgKeep `SubArgsLive` SubArgOut subTp `SubArgsLive` SubArgsNil
    | ArgFun f :>: array :>: ArgsNil <- args
      -> ShrunkOperation mkGenerate (ArgFun (subTupFun subTp f) :>: array :>: ArgsNil)
  _ `SubArgsLive` SubArgsDead _ -> internalError "At least one output should be preserved"

defaultSlvMap
  :: (forall sh' s' t'. op b (Fun' (s' -> t') -> In sh' s' -> Out sh' t' -> ()))
  -> Maybe (ShrinkOperation op b (Fun' (s -> t) -> In sh s -> Out sh  t -> ()))
defaultSlvMap mkMap = Just $ ShrinkOperation $ \subArgs args _ -> case subArgs of
  SubArgKeep `SubArgsLive` SubArgKeep `SubArgsLive` SubArgKeep `SubArgsLive` SubArgsNil
    -> ShrunkOperation mkMap args
  SubArgKeep `SubArgsLive` SubArgKeep `SubArgsLive` SubArgOut subTp `SubArgsLive` SubArgsNil
    | ArgFun f :>: input :>: output :>: ArgsNil <- args
      -> ShrunkOperation mkMap (ArgFun (subTupFun subTp f) :>: input :>: output :>: ArgsNil)
  _ `SubArgsLive` _ `SubArgsLive` SubArgsDead _ -> internalError "At least one output should be preserved"

defaultSlvBackpermute
  :: (forall sh1' sh2' t'. op b (Fun' (sh2' -> sh1') -> In sh1' t' -> Out sh2' t' -> ()))
  -> Maybe (ShrinkOperation op b (Fun' (sh2 -> sh1) -> In sh1 t -> Out sh2 t -> ()))
defaultSlvBackpermute mkBackpermute = Just $ ShrinkOperation $ \subArgs args _ -> case subArgs of
  SubArgKeep `SubArgsLive` SubArgKeep `SubArgsLive` SubArgKeep `SubArgsLive` SubArgsNil
    -> ShrunkOperation mkBackpermute args
  SubArgKeep `SubArgsLive` SubArgKeep `SubArgsLive` SubArgOut s `SubArgsLive` SubArgsNil
    | f :>: ArgArray In (ArrayR shr r) sh buf :>: output :>: ArgsNil <- args
      -> ShrunkOperation mkBackpermute (f :>: ArgArray In (ArrayR shr (subTupR s r)) sh (subTupDBuf s buf) :>: output :>: ArgsNil)
  _ `SubArgsLive` _ `SubArgsLive` SubArgsDead _ -> internalError "At least one output should be preserved"

reEnvArrayInstr :: ReEnv env subenv -> ArrayInstr env t -> ArrayInstr subenv t
reEnvArrayInstr re (Parameter var) = Parameter $ expectJust $ reEnvVar re var
reEnvArrayInstr re (Index buffer)  = Index $ expectJust $ reEnvVar re buffer

reEnvArgs :: ReEnv env subenv -> Args env t -> Args subenv t
reEnvArgs re (a :>: as) = reEnvArg re a :>: reEnvArgs re as
reEnvArgs _  ArgsNil    = ArgsNil

reEnvArg :: ReEnv env subenv -> Arg env t -> Arg subenv t
reEnvArg re (ArgVar vars) = ArgVar $ expectJust $ reEnvVars re vars
reEnvArg re (ArgExp expr) = ArgExp $ mapArrayInstr (reEnvArrayInstr re) expr
reEnvArg re (ArgFun f)    = ArgFun $ mapArrayInstrFun (reEnvArrayInstr re) f
reEnvArg re (ArgArray m repr sh buffers) = ArgArray m repr (expectJust $ reEnvVars re sh) (expectJust $ reEnvVars re buffers)

reEnvArrayDescriptors :: ReEnv env subenv -> ArrayDescriptors env t -> TupR (ArrayDescriptor subenv) t
reEnvArrayDescriptors re = mapTupR (\(ArrayDescriptor shr sh buffer) -> ArrayDescriptor shr (expectJust $ reEnvVars re sh) (expectJust $ reEnvVars re buffer))

-- Captures existential f'
data ReEnvSubArgs subenv f where
  ReEnvSubArgs :: SubArgs f f'
               -> Args subenv f'
               -> ReEnvSubArgs subenv f

reEnvSubArgs :: ReEnv env subenv -> Args env f -> ReEnvSubArgs subenv f
reEnvSubArgs re (a :>: as)
  | ReEnvSubArgs subs as' <- reEnvSubArgs re as =
    case a of
      ArgArray Out (ArrayR shr tp) sh buffers -> case reEnvSubBuffers re tp buffers of
        ReEnvSubBuffers SubTupRskip _
          -- don't kill unit outputs
          | TupRunit <- tp                   -> ReEnvSubArgs (SubArgsLive SubArgKeep subs) (ArgArray Out (ArrayR shr tp) (expectJust $ reEnvVars re sh) TupRunit :>: as')
          | otherwise                        -> ReEnvSubArgs (SubArgsDead subs) (ArgVar (fromGrounds $ expectJust $ reEnvVars re sh) :>: as')
        ReEnvSubBuffers SubTupRkeep buffers' -> ReEnvSubArgs (SubArgsLive SubArgKeep subs) (ArgArray Out (ArrayR shr tp) (expectJust $ reEnvVars re sh) buffers' :>: as')
        ReEnvSubBuffers sub         buffers' -> ReEnvSubArgs (SubArgsLive (SubArgOut sub) subs) (ArgArray Out (ArrayR shr $ subTupR sub tp) (expectJust $ reEnvVars re sh) buffers' :>: as')
      _ -> ReEnvSubArgs (SubArgsLive SubArgKeep subs) (reEnvArg re a :>: as')
reEnvSubArgs _ ArgsNil = ReEnvSubArgs SubArgsNil ArgsNil

reEnvSubBuffers :: ReEnv env subenv -> TypeR t -> GroundVars env (Buffers t) -> ReEnvSubBuffers subenv t
reEnvSubBuffers _  TupRunit TupRunit = ReEnvSubBuffers SubTupRskip TupRunit
reEnvSubBuffers re (TupRsingle _) (TupRsingle var)
  | Just var' <- reEnvVar re var = ReEnvSubBuffers SubTupRkeep (TupRsingle var')
  | otherwise = ReEnvSubBuffers SubTupRskip TupRunit
reEnvSubBuffers re (TupRpair t1 t2) (TupRpair v1 v2)
  | ReEnvSubBuffers s1 v1' <- reEnvSubBuffers re t1 v1
  , ReEnvSubBuffers s2 v2' <- reEnvSubBuffers re t2 v2
  = case (s1, s2) of
      (SubTupRskip, SubTupRskip) -> ReEnvSubBuffers SubTupRskip TupRunit
      (SubTupRkeep, SubTupRkeep) -> ReEnvSubBuffers SubTupRkeep (TupRpair v1' v2')
      _ -> ReEnvSubBuffers (SubTupRpair s1 s2) (TupRpair v1' v2')
reEnvSubBuffers _ _ _ = internalError "Tuple mismatch"

data ReEnvSubBuffers subenv t where
  ReEnvSubBuffers :: SubTupR t t' -> GroundVars subenv (Buffers t') -> ReEnvSubBuffers subenv t

composeSubArgs :: SubArgs a b -> SubArgs b c -> SubArgs a c
composeSubArgs SubArgsNil SubArgsNil = SubArgsNil
composeSubArgs (SubArgsDead                s1) (SubArgsLive SubArgKeep     s2) = SubArgsDead                                    $ composeSubArgs s1 s2
composeSubArgs (SubArgsLive SubArgKeep     s1) (SubArgsDead                s2) = SubArgsDead                                    $ composeSubArgs s1 s2
composeSubArgs (SubArgsLive (SubArgOut _)  s1) (SubArgsDead                s2) = SubArgsDead                                    $ composeSubArgs s1 s2
composeSubArgs (SubArgsLive SubArgKeep     s1) (SubArgsLive s              s2) = SubArgsLive s                                  $ composeSubArgs s1 s2
composeSubArgs (SubArgsLive (SubArgOut t)  s1) (SubArgsLive SubArgKeep     s2) = SubArgsLive (SubArgOut t)                      $ composeSubArgs s1 s2
composeSubArgs (SubArgsLive (SubArgOut t1) s1) (SubArgsLive (SubArgOut t2) s2) = SubArgsLive (SubArgOut $ composeSubTupR t2 t1) $ composeSubArgs s1 s2

subTupUniqueness :: SubTupR t t' -> Uniquenesses t -> Uniquenesses t'
subTupUniqueness SubTupRskip         _                = TupRunit
subTupUniqueness SubTupRkeep         t                = t
subTupUniqueness (SubTupRpair s1 s2) (TupRpair t1 t2) = subTupUniqueness s1 t1 `TupRpair` subTupUniqueness s2 t2
subTupUniqueness (SubTupRpair s1 s2) (TupRsingle Shared) = TupRpair (subTupUniqueness s1 (TupRsingle Shared)) (subTupUniqueness s2 (TupRsingle Shared)) --TupRsingle Shared
