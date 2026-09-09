{-# LANGUAGE GADTs               #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE TypeOperators       #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# OPTIONS_HADDOCK hide #-}
-- |
-- Module      : Data.Array.Accelerate.Trafo.Schedule.Partial
-- Copyright   : [2012..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.Trafo.Schedule.Partial (
  convertAccPartial, convertAfunPartial,
  PartialSchedule(..), PartialScheduleFun,
  PrePartialSchedule(..), PrePartialScheduleFun(..),
  Parallelism(..),
  Sync(..), SyncEnv,
  SyncSchedule(..), SyncScheduleFun,
  Loop,
  variablesToSyncEnv,

  UnitTuple, UpdateTuple(..), toPartialReturn,

  compileKernel', CompiledKernel(..),
) where

import Data.Array.Accelerate.Analysis.Match
import Data.Array.Accelerate.AST.Environment
import Data.Array.Accelerate.AST.Idx
import Data.Array.Accelerate.AST.IdxSet (IdxSet)
import Data.Array.Accelerate.AST.LeftHandSide
import Data.Array.Accelerate.AST.Kernel
import Data.Array.Accelerate.AST.Schedule.Uniform
import Data.Array.Accelerate.Error
import Data.Array.Accelerate.Representation.Array
import Data.Array.Accelerate.Representation.Shape
import Data.Array.Accelerate.Representation.Type
import Data.Array.Accelerate.Trafo.Var
import Data.Array.Accelerate.Trafo.Substitution
import Data.Array.Accelerate.Trafo.Exp.Substitution
import Data.Array.Accelerate.Type
import qualified Data.Array.Accelerate.AST.IdxSet           as IdxSet
import Data.Array.Accelerate.AST.Partitioned (PartitionedAcc, PartitionedAfun, Clustered)
import qualified Data.Array.Accelerate.AST.Partitioned as C
import Data.Text (Text)
import Data.Kind
import Data.Maybe
import Prelude hiding (id, (.), read)
import Control.Category

import Data.Functor.Identity
-- Constructs a partial schedule. It is partial as many details still need
-- to be filled in for the actual schedule. This schedule does however
-- decide whether the binding and body of a let-binding should be executed
-- in parallel or sequentially.
-- When implemention a schedule, this module may provide a good first step.
convertAccPartial :: IsKernel kernel => PartitionedAcc (KernelOperation kernel) env t -> SyncSchedule kernel env t
convertAccPartial = analyseSyncEnv . rebuild 50 . toPartial

convertAfunPartial :: IsKernel kernel => PartitionedAfun (KernelOperation kernel) env f -> SyncScheduleFun kernel env f
convertAfunPartial (C.Alam lhs f) = Plam lhs $ convertAfunPartial f
convertAfunPartial (C.Abody body) = Pbody $ convertAccPartial body

-- Sync environment
type SyncEnv = PartialEnv Sync

data Sync t where
  SyncRead  :: Sync (Buffer e)
  SyncWrite :: Sync (Buffer e)

instance Eq (Sync t) where
  SyncRead  == SyncRead  = True
  SyncWrite == SyncWrite = True
  _         == _         = False

instance Ord (Sync t) where
  SyncRead < SyncWrite = True
  _        < _         = False

  SyncWrite <= SyncRead = False
  _         <= _        = True

weakenSyncEnv :: GLeftHandSide t env env' -> SyncEnv env' -> SyncEnv env
weakenSyncEnv _                        PEnd          = PEnd
weakenSyncEnv (LeftHandSideWildcard _) env           = env
weakenSyncEnv (LeftHandSideSingle _)   (PPush env _) = env
weakenSyncEnv (LeftHandSideSingle _)   (PNone env)   = env
weakenSyncEnv (LeftHandSidePair l1 l2) env           = weakenSyncEnv l1 $ weakenSyncEnv l2 env

-- Intermediate representation, used during the transformation

data Parallelism
  -- This let-binding is parallel: the binding is spawned in a separate task, and the body is directly executed.
  = Parallel
  -- This let-binding is sequential. The binding is executed before the body.
  | Sequential
  deriving Eq

data PrePartialScheduleFun (schedule :: (Type -> Type) -> Type -> Type -> Type) kernel env t where
  Plam  :: GLeftHandSide s env env'
        -> PrePartialScheduleFun schedule kernel env' t
        -> PrePartialScheduleFun schedule kernel env (s -> t)

  Pbody :: schedule kernel env t
        -> PrePartialScheduleFun schedule kernel env  t

data PrePartialSchedule schedule kernel env t where
  PExec
    :: KernelFun kernel s
    -> SArgs env s
    -> PrePartialSchedule schedule kernel env ()

  PLet
    :: Parallelism -- Should this be executed in parallel?
    -> GLeftHandSide bnd env env'
    -> Uniquenesses bnd
    -> schedule kernel env bnd
    -> schedule kernel env' t
    -> PrePartialSchedule schedule kernel env t

  PAlloc
    :: ShapeR sh
    -> ScalarType e
    -> ExpVars env sh
    -> PrePartialSchedule schedule kernel env (Buffer e)

  PUse
    :: ScalarType e
    -> Int -- Number of elements
    -> Buffer e
    -> PrePartialSchedule schedule kernel env (Buffer e)

  PUnit
    :: ExpVar env e
    -> PrePartialSchedule schedule kernel env (Buffer e)

  PCompute
    :: Exp env e
    -> PrePartialSchedule schedule kernel env e

  -- End of control flow. Returns no values, that happens in PReturnValues
  PReturnEnd
    :: TupR Void' t -- Tuple without TupRsingle
    -> PrePartialSchedule schedule kernel env t

  PReturnValues
    :: UpdateTuple env t1 t2
    -> schedule kernel env t1
    -> PrePartialSchedule schedule kernel env t2

  PAcond
    :: ExpVar env PrimBool
    -> schedule kernel env t
    -> schedule kernel env t
    -> PrePartialSchedule schedule kernel env t

  PAwhile
    :: Uniquenesses t
    -> PrePartialScheduleFun schedule kernel env (t -> Loop t)
    -> GroundVars env t
    -> PrePartialSchedule schedule kernel env t

  PAtrace
    :: Text
    -> ArrayDescriptors env t
    -> PrePartialSchedule schedule kernel env Word8

  -- Signals that this while loop should do another iteration.
  -- The state for the next iteration is computed by the subterm.
  PContinue
    :: schedule kernel env t
    -> PrePartialSchedule schedule kernel env (Loop t)

  -- Stops this while loop. The result value of the loop is
  -- given by the GroundVars.
  PBreak
    :: Uniquenesses t
    -> GroundVars env t
    -> PrePartialSchedule schedule kernel env (Loop t)

  PAssert
    :: Text
    -> Exp env PrimBool
    -> PrePartialSchedule schedule kernel env PrimBool

  PFence
    :: IdxSet env
    -> schedule kernel env t
    -> PrePartialSchedule schedule kernel env t

data Void' a where
data Loop a where

data UpdateTuple env t1 t2 where
  UpdateKeep :: UpdateTuple env t t
  UpdatePair
    :: UpdateTuple env left1 left2
    -> UpdateTuple env right1 right2
    -> UpdateTuple env (left1, right1) (left2, right2)
  UpdateSet
    :: Uniqueness t
    -> GroundVar env t
    -> UpdateTuple env () t

updatePair
  :: UpdateTuple env left1 left2
  -> UpdateTuple env right1 right2
  -> UpdateTuple env (left1, right1) (left2, right2)
updatePair UpdateKeep UpdateKeep = UpdateKeep
updatePair up1 up2 = UpdatePair up1 up2

updateTupVarList :: forall env t1 t2. UpdateTuple env t1 t2 -> [Exists (Idx env)]
updateTupVarList = (`go` [])
  where
    go :: UpdateTuple env s1 s2 -> [Exists (Idx env)] -> [Exists (Idx env)]
    go UpdateKeep accum = accum
    go (UpdateSet _ var) accum = Exists (varIdx var) : accum
    go (UpdatePair up1 up2) accum = go up1 $ go up2 accum

updateTupSync :: forall env t1 t2. UpdateTuple env t1 t2 -> [EnvBinding Sync env]
updateTupSync = (`go` [])
  where
    go :: UpdateTuple env s1 s2 -> [EnvBinding Sync env] -> [EnvBinding Sync env]
    go UpdateKeep accum = accum
    go (UpdateSet Unique var) accum = EnvBinding (varIdx var) SyncWrite : accum
    go (UpdateSet _ (Var (GroundRbuffer _) idx)) accum = EnvBinding idx SyncRead : accum
    go (UpdateSet _ _) accum = accum
    go (UpdatePair up1 up2) accum = go up1 $ go up2 accum

type PartialScheduleFun = PrePartialScheduleFun PartialSchedule
newtype PartialSchedule kernel env t = PartialSchedule (PrePartialSchedule PartialSchedule kernel env t)

type SyncScheduleFun = PrePartialScheduleFun SyncSchedule
data SyncSchedule kernel env t =
  SyncSchedule {
    syncEnv :: SyncEnv env,
    -- Whether this term introduces no branching and no forks
    syncSimple :: Bool,
    syncSchedule :: (PrePartialSchedule SyncSchedule kernel env t)
  }

-- Tuple where all the fields are replaced with unit.
type family UnitTuple t where
  UnitTuple (a, b) = (UnitTuple a, UnitTuple b)
  UnitTuple a = ()

unitTupleForVars :: GroundVars env t -> TupR Void' (UnitTuple t)
unitTupleForVars (TupRpair v1 v2) = unitTupleForVars v1 `TupRpair` unitTupleForVars v2
unitTupleForVars TupRunit = TupRunit
-- Pattern match on the type of the variable to proof that t isn't a pair.
unitTupleForVars (TupRsingle (Var tp _))
  | Refl <- groundNotPair tp = TupRunit

groundNotPair :: GroundR t -> UnitTuple t :~: ()
groundNotPair (GroundRbuffer _) = Refl
groundNotPair (GroundRscalar (VectorScalarType _)) = Refl
groundNotPair (GroundRscalar (SingleScalarType (NumSingleType (IntegralNumType t)))) = case t of
  TypeInt -> Refl
  TypeInt8 -> Refl
  TypeInt16 -> Refl
  TypeInt32 -> Refl
  TypeInt64 -> Refl
  TypeWord -> Refl
  TypeWord8 -> Refl
  TypeWord16 -> Refl
  TypeWord32 -> Refl
  TypeWord64 -> Refl
groundNotPair (GroundRscalar (SingleScalarType (NumSingleType (FloatingNumType t)))) = case t of
  TypeHalf -> Refl
  TypeFloat -> Refl
  TypeDouble -> Refl

data HoistReturn env env' t1 t3 where
  HoistReturn
    :: UpdateTuple env t2 t3
    -> UpdateTuple env' t1 t2
    -> HoistReturn env env' t1 t3

hoistReturn :: GLeftHandSide bnd env env' -> SyncEnv env -> UpdateTuple env' t1 t3 -> HoistReturn env env' t1 t3
hoistReturn lhs bndSyncEnv = \case
  UpdateKeep -> HoistReturn UpdateKeep UpdateKeep
  UpdatePair upL upR
    | HoistReturn upL1 upL2 <- hoistReturn lhs bndSyncEnv upL
    , HoistReturn upR1 upR2 <- hoistReturn lhs bndSyncEnv upR ->
      HoistReturn (updatePair upL1 upR1) (updatePair upL2 upR2)
  UpdateSet u var
    | Just idx <- strengthenWithLHS lhs $ varIdx var
    , canHoist u (prjPartial idx bndSyncEnv) ->
      -- We can hoist this return
      HoistReturn (UpdateSet u $ Var (varType var) idx) UpdateKeep
  up -> HoistReturn UpdateKeep up
  where
    canHoist :: Uniqueness t -> Maybe (Sync t) -> Bool
    canHoist _ Nothing = True -- Variable is not used in this term, so we can hoist the return to before this term.
    canHoist Shared (Just SyncRead) = True -- A shared buffer may still be read after returning it.
    canHoist _ _ = False -- All other combinations are not allowed.

-- A function that gets the available variables (i.e., the variables that don't have to be waited on)
-- and then returns the constructed schedule (PartialSchedule or PartialScheduleFun)
-- together with the set of variables the function directly waits on.
-- These two sets should have no overlap.
-- Also returns whether a term is trivial, meaning that the term is computationally inexpensive.
-- Invariant: If a schedule is trivial, then the directly-awaits set must
-- equal the set of all free variables (minus the already available variables).
type Build p (kernel :: Type -> Type) env t = IdxSet env -> Built p kernel env t

data Built p (kernel :: Type -> Type) env t =
  Built {
    -- Did the program change this iteration, in a way that new information may be available
    -- in the next iteration?
    didChange :: !Bool,
    -- The set of variables that are directly required to start this computation.
    -- I.e., there is no use in starting this computation if some of these variables
    -- are not available yet. This information is used to decide if a let binding
    -- should be executed in parallel or sequentially.
    directlyAwaits :: IdxSet env,
    -- The set of buffer variables that may be written to.
    writes :: IdxSet env,
    -- The set of buffer variables that are released by a term at the end of its execution.
    -- 'Released' here means that the term wrote to those buffers and is only ready writing
    -- to them at the end of the execution.
    -- This should be a subset of 'writes'.
    -- This information can be used to decide if a let binding should be sequential or parallel.
    -- If the binding of a let 'finally releases' a buffer variable and the body 'directly awaits' it,
    -- the let should be executed sequentially.
    finallyReleases :: IdxSet env,
    trivial :: Bool,
    term :: !(p kernel env t)
  }

data Exists' (a :: (Type -> Type -> Type) -> Type) where
  Exists' :: a m -> Exists' a

combineMod :: Modifier m -> Modifier m' -> Exists' Modifier
combineMod In  In  = Exists' In
combineMod Out Out = Exists' Out
combineMod _   _   = Exists' Mut
-- combineMod _   _   = error "Remove this error once we add in place updates"

combineAccessGroundR :: AccessGroundR t -> AccessGroundR t -> AccessGroundR t
combineAccessGroundR (AccessGroundRbuffer m1 tp) (AccessGroundRbuffer m2 _)
  | Exists' m <- combineMod m1 m2 = AccessGroundRbuffer m tp
combineAccessGroundR a _ = a -- Nothing has to be done when combining two scalars; they don't have access modifiers

data CompiledKernel kenv fenv kernel where
  CompiledKernel :: OpenKernelFun kernel kenv f
                 -> SArgs fenv f
                 -> CompiledKernel kenv fenv kernel

compileKernel'
  :: forall fenv kernel args.
     IsKernel kernel
  => Clustered (KernelOperation kernel) args
  -> Args fenv args
  -> CompiledKernel () fenv kernel
compileKernel' cluster args =
  go
    (partialEnvFromList combineAccessGroundR (map (\(Exists (Var tp ix)) -> EnvBinding ix tp) vars))
    weakenId
    Empty
    (\ _ x -> x)
  where
    vars = argsVars args

    go
      :: forall fenv1 kenv.
         PartialEnv AccessGroundR fenv1
      -> (fenv1 :> fenv)
      -> Env AccessGroundR kenv
      -> (forall kenv'. kenv :> kenv' -> PartialEnv (Idx kenv') fenv1 -> PartialEnv (Idx kenv') fenv)
      -> CompiledKernel kenv fenv kernel
    go PEnd _  kenv kSubst =
      CompiledKernel
        (KernelFunBody $ compileKernel kenv cluster args')
        ArgsNil
      where
        kSubst' = kSubst weakenId PEnd
        Identity args' = reindexArgs prjIdx args
        prjIdx :: forall a. Idx fenv a -> Identity (Idx kenv a)
        prjIdx idx = case prjPartial idx kSubst' of
          Nothing -> internalError "Variable not found in environment. The environment was probably built incorrectly, argsVars may have missed this variable?"
          Just idx' -> Identity idx'
    go (PPush env a@(AccessGroundRscalar tp)) k1 kenv kSubstF
      | CompiledKernel kernel sargs <- go env (weakenSucc k1) (kenv `Push` a) (\k2 kSubst -> kSubstF (weakenSucc k2) $ PPush kSubst (k2 >:> ZeroIdx))
      = CompiledKernel (KernelFunLam (KernelArgRscalar tp) kernel) (SArgScalar (Var tp $ k1 >:> ZeroIdx) :>: sargs)
    go (PPush env a@(AccessGroundRbuffer mod' tp)) k1 kenv kSubstF
      | CompiledKernel kernel sargs <- go env (weakenSucc k1) (kenv `Push` a) (\k2 kSubst -> kSubstF (weakenSucc k2) $ PPush kSubst (k2 >:> ZeroIdx))
      = CompiledKernel (KernelFunLam (KernelArgRbuffer mod' tp) kernel) (SArgBuffer mod' (Var (GroundRbuffer tp) $ k1 >:> ZeroIdx) :>: sargs)
    go (PNone env) k1 kenv kSubstF
      = go env (weakenSucc k1) kenv (\k2 kSubst -> kSubstF k2 $ PNone kSubst)

toPartial :: IsKernel kernel => PartitionedAcc (KernelOperation kernel) env t -> PartialSchedule kernel env t
toPartial = snd . toPartial' (TupRsingle Shared)

toPartial' :: IsKernel kernel => Uniquenesses t -> PartitionedAcc (KernelOperation kernel) env t -> (IdxSet env, PartialSchedule kernel env t)
toPartial' us = \case
  C.Exec cluster args
    | CompiledKernel kernel sargs <- compileKernel' cluster args ->
        ( IdxSet.fromList $ sargBufferVars sargs
        , PartialSchedule $ PExec kernel sargs )
  C.Return vars ->
    ( IdxSet.fromVarList $ filter isBuffer $ flattenTupR vars
    , returnValues (toPartialReturn us vars) $ PartialSchedule $ PReturnEnd $ unitTupleForVars vars )
  C.Manifest var -> toPartial' us (C.Return $ TupRsingle var)
  C.Compute expr ->
    ( IdxSet.fromList $ mapMaybe (\(Exists a) -> instrToSync a) $ arrayInstrsInExp expr
    , PartialSchedule $ PCompute expr )
  C.Alet lhs usBnd bnd body
    | (bndFree, bnd') <- toPartial' usBnd bnd
    , (bodyFree, body') <- toPartial' us body ->
      ( bndFree `IdxSet.union` IdxSet.drop' lhs bodyFree
      , PartialSchedule $ PLet Parallel lhs usBnd bnd' body' )
  C.Alloc shr tp sh -> simple $ PAlloc shr tp sh
  C.Use tp sz buf -> simple $ PUse tp sz buf
  C.Unit var -> simple $ PUnit var
  C.Acond var true false
    | (trueFree, true') <- toPartial' us true
    , (falseFree, false') <- toPartial' us false ->
      ( trueFree `IdxSet.union` falseFree
      , PartialSchedule $ PAcond var true' false' )
  C.Awhile us' (C.Alam lhsC (C.Abody cond)) (C.Alam lhsS (C.Abody step)) initial
    | DeclareVars lhs _ vars <- declareVars $ lhsToTupR lhsC
    , (condFree, cond') <- toPartial' (TupRsingle Shared) $ weaken (weakenToFullLHS lhs lhsC) cond
    , (stepFree, step') <- toPartial' (TupRsingle Shared) $ weaken (weakenSucc' $ weakenToFullLHS lhs lhsS) step
    , fn <- PartialSchedule $ PLet Sequential (LeftHandSideSingle (GroundRscalar scalarType)) (TupRsingle Shared) cond'
        $ PartialSchedule $ PAcond (Var scalarType ZeroIdx)
          (PartialSchedule $ PContinue step')
          (PartialSchedule $ PBreak us' $ vars (weakenSucc weakenId))
    ->
      ( IdxSet.drop' lhs condFree `IdxSet.union` IdxSet.drop' lhs (IdxSet.drop stepFree) `IdxSet.union` IdxSet.fromList (groundBufferVars initial)
      , PartialSchedule $ PAwhile us' (Plam lhs $ Pbody fn) initial )
  C.Awhile{} -> internalError "Unary function impossible"
  C.Atrace msg t -> (arrayDescriptorsIdxSet t, PartialSchedule $ PAtrace msg t)
  C.Aassert msg cond ->
    ( IdxSet.fromList $ mapMaybe (\(Exists a) -> instrToSync a) $ arrayInstrsInExp cond
    , PartialSchedule $ PAssert msg cond )
  C.Aassume _ -> toPartial' us $ C.Compute $ Const scalarTypeWord8 0 -- Assumptions are removed at this point
  C.Fence deps next
    | (nextFree, next') <- toPartial' us next ->
      ( deps `IdxSet.union` nextFree
      , PartialSchedule $ PFence deps next' )
  where
    -- For all simple cases, with no free buffer variables.
    simple :: PrePartialSchedule PartialSchedule kernel env t -> (IdxSet env, PartialSchedule kernel env t)
    simple schedule = (IdxSet.empty, PartialSchedule schedule)

    isBuffer :: Exists (GroundVar env) -> Bool
    isBuffer (Exists (Var (GroundRbuffer _) _)) = True
    isBuffer _ = False

    instrToSync :: ArrayInstr env a -> Maybe (Exists (Idx env))
    instrToSync (Index v) = Just $ Exists $ varIdx v
    instrToSync (Parameter _) = Nothing -- Parameter is a scalar variable

weakenToFullLHS
  -- Full LHS
  :: GLeftHandSide t env envFull
  -- Sub LHS
  -> GLeftHandSide t env envSub
  -> envSub :> envFull
weakenToFullLHS = \lhs1 lhs2 -> go lhs1 lhs2 weakenId
  where
    go :: GLeftHandSide t env1 env1' -> GLeftHandSide t env2 env2' -> env2 :> env1 -> env2' :> env1'
    go lhs (LeftHandSideWildcard _) k = weakenWithLHS lhs .> k
    go (LeftHandSidePair lhs1 lhs1') (LeftHandSidePair lhs2 lhs2') k = go lhs1' lhs2' $ go lhs1 lhs2 k
    go (LeftHandSideSingle _) (LeftHandSideSingle _) k = sink k
    go (LeftHandSideWildcard _) _ _ = internalError "Expected second LHS to be contained in first LHS"
    go _ _ _ = internalError "LHS mismatch"

returnValues
  :: UpdateTuple env t1 t2
  -> PartialSchedule kernel env t1
  -> PartialSchedule kernel env t2
returnValues UpdateKeep next = next
returnValues updateTup next = PartialSchedule $ PReturnValues updateTup next

toPartialReturn :: Uniquenesses t -> GroundVars env t -> UpdateTuple env (UnitTuple t) t
toPartialReturn _ TupRunit = UpdateKeep
toPartialReturn us (TupRpair v1 v2) = toPartialReturn us1 v1 `updatePair` toPartialReturn us2 v2
  where
    (us1, us2) = pairUniqueness us
toPartialReturn (TupRsingle u) (TupRsingle var)
  | Refl <- groundNotPair $ varType var
  = UpdateSet u var
toPartialReturn _ _ = internalError "Tuple mismatch"

groundBufferVars :: GroundVars env t -> [Exists (Idx env)]
groundBufferVars = (`go` [])
  where
    go :: GroundVars env t -> [Exists (Idx env)] -> [Exists (Idx env)]
    go (TupRpair v1 v2) accum = go v1 $ go v2 accum
    go (TupRsingle (Var (GroundRbuffer _) idx)) accum = Exists idx : accum
    go _ accum = accum

-- Optimizes the PartialSchedule by rebuilding it. It keeps rebuilding until
-- it reaches a fixed-point, or after it performs n iterations.
-- Assumes n >= 1
rebuild :: Int -> PartialSchedule kernel env t -> PartialSchedule kernel env t
rebuild n t
  | didChange built && n > 1 = rebuild (n - 1) $ term built
  | otherwise = term built
  where
    built = rebuild' t IdxSet.empty

rebuild' :: PartialSchedule kernel env t -> Build PartialSchedule kernel env t
rebuild' (PartialSchedule schedule) = case schedule of
  PExec kernel args -> buildExec kernel args
  PLet parallelism lhs us bnd body -> buildLet parallelism lhs us (rebuild' bnd) (rebuild' body)
  PAlloc shr tp sh -> buildAlloc shr tp sh
  PUse sz tp buf -> buildUse sz tp buf
  PUnit var -> buildUnit var
  PCompute expr -> buildCompute expr
  PReturnEnd tup -> buildReturnEnd tup
  PReturnValues updateTup next -> buildReturnValues updateTup (rebuild' next)
  PAcond var true false -> buildAcond var (rebuild' true) (rebuild' false)
  PAwhile us fn initial -> buildAwhile us (rebuildUnary fn) initial
  PAtrace msg t -> buildTrace msg t
  PContinue next -> buildContinue $ rebuild' next
  PBreak us vars -> buildBreak us vars
  PAssert msg cond -> buildAssert msg cond
  PFence deps next -> buildFence deps $ rebuild' next

rebuildUnary :: PartialScheduleFun kernel env f -> BuildUnary kernel env f
rebuildUnary (Plam lhs (Pbody body)) = BuildUnary lhs $ rebuild' body
rebuildUnary _ = internalError "Expected unary function"

buildExec :: KernelFun kernel s -> SArgs env s -> Build PartialSchedule kernel env ()
buildExec kernel args available =
  Built {
    didChange = False,
    directlyAwaits = IdxSet.fromList (sargVars args) IdxSet.\\ available,
    writes = output,
    finallyReleases = output,
    trivial = False,
    term = PartialSchedule $ PExec kernel args
  }
  where
    output = IdxSet.fromList (sargOutputVars args)

buildLet
  :: Parallelism
  -> GLeftHandSide bnd env env'
  -> Uniquenesses bnd
  -> Build PartialSchedule kernel env bnd
  -> Build PartialSchedule kernel env' t
  -> Build PartialSchedule kernel env t
buildLet parallelismHint lhs us bnd' body' available =
  Built {
    didChange = didChange bnd || didChange body || parallelismHint /= parallelism,
    directlyAwaits = thisAwaits,
    writes = writes bnd `IdxSet.union` IdxSet.drop' lhs (writes body),
    finallyReleases = thisReleases,
    trivial = sequential && trivial bnd && trivial body,
    term =
      PartialSchedule $ PLet
        parallelism
        lhs us (term bnd) (term body)
  }
  where
    bnd = bnd' available
    bodyAvailable
      | sequentialEarlyTest = IdxSet.push' lhs $ available `IdxSet.union` directlyAwaits bnd
      | otherwise = IdxSet.skip' lhs (available IdxSet.\\ writes bnd)
    body = body' bodyAvailable

    bodyAwaitsDropped = IdxSet.drop' lhs (directlyAwaits body)
    bodyReleasesDropped = IdxSet.drop' lhs (finallyReleases body)

    thisAwaits
      | sequential && trivial bnd = IdxSet.union (directlyAwaits bnd) bodyAwaitsDropped
      | sequential = directlyAwaits bnd
      | otherwise = IdxSet.intersect (directlyAwaits bnd) bodyAwaitsDropped

    thisReleases
      | sequential && trivial body = IdxSet.union (finallyReleases bnd) bodyReleasesDropped
      | sequential = bodyReleasesDropped
      | otherwise = IdxSet.empty

    -- Checks if this let-binding should become sequential.
    -- This check happens in two steps:
    -- An early check runs before calling body'. Based on this check,
    -- we pass an availability-set to body'.
    -- A late check runs after calling body'. This uses the information from
    -- body.
    sequentialEarlyTest =
      -- If the hint was to make this Let sequential, make it sequential
      parallelismHint == Sequential
      -- If the binding is trivial and doesn't wait on variables.
      || trivial bnd && IdxSet.null (directlyAwaits bnd)

    thisLhsIndices = lhsIndices lhs

    -- Make it sequential if:
    sequential =
      -- the early test already made it sequential,
      sequentialEarlyTest
      -- the body directly needs all declared variables (and there is at least one such variable),
      || not (IdxSet.isEmpty thisLhsIndices) && thisLhsIndices `IdxSet.isSubsetOf` directlyAwaits body
      -- the binding is trivial and doesn't use other variables than the
      -- body already waits on.
      -- Note that the awaits set contains all free variables (minus the available variables)
      -- if the program is trivial.
      || trivial bnd && directlyAwaits bnd `IdxSet.isSubsetOf` bodyAwaitsDropped
      -- or the binding is trivial and the body directly awaits on the result of this expression.
      || trivial bnd && thisLhsIndices `IdxSet.overlaps` directlyAwaits body

    parallelism = if sequential then Sequential else Parallel

buildAlloc :: ShapeR sh -> ScalarType e -> ExpVars env sh -> Build PartialSchedule kernel env (Buffer e)
buildAlloc shr tp vars available =
  Built{
    didChange = False,
    directlyAwaits = IdxSet.fromVars vars IdxSet.\\ available,
    writes = IdxSet.empty,
    finallyReleases = IdxSet.empty,
    trivial = True,
    term = PartialSchedule $ PAlloc shr tp vars
  }

buildUse :: ScalarType e -> Int -> Buffer e -> Build PartialSchedule kernel env (Buffer e)
buildUse tp sz buf _ =
  Built{
    didChange = False,
    directlyAwaits = IdxSet.empty,
    writes = IdxSet.empty,
    finallyReleases = IdxSet.empty,
    trivial = True,
    term = PartialSchedule $ PUse tp sz buf
  }

buildUnit :: ExpVar env e -> Build PartialSchedule kernel env (Buffer e)
buildUnit var available =
  Built{
    didChange = False,
    directlyAwaits = if var `IdxSet.varMember` available then IdxSet.empty else IdxSet.singletonVar var,
    writes = IdxSet.empty,
    finallyReleases = IdxSet.empty,
    trivial = True,
    term = PartialSchedule $ PUnit var
  }

buildCompute :: Exp env e -> Build PartialSchedule kernel env e
buildCompute expr available =
  Built{
    didChange = False,
    directlyAwaits = IdxSet.fromVarList vars IdxSet.\\ available,
    writes = IdxSet.empty,
    finallyReleases = IdxSet.empty,
    trivial = expIsTrivial (const True) expr,
    term = PartialSchedule $ PCompute expr
  }
  where
    vars = expGroundVars expr

buildReturnEnd :: TupR Void' t -> Build PartialSchedule kernel env t
buildReturnEnd tup _ =
  Built{
    didChange = False,
    directlyAwaits = IdxSet.empty,
    writes = IdxSet.empty,
    finallyReleases = IdxSet.empty,
    trivial = True,
    term = PartialSchedule $ PReturnEnd tup
  }

buildReturnValues :: forall kernel env t1 t2. UpdateTuple env t1 t2 -> Build PartialSchedule kernel env t1 -> Build PartialSchedule kernel env t2
buildReturnValues updateTup next' available =
  Built{
    didChange = didChange next,
    -- A Return can be executed in parallel: if some returned variables are/become available,
    -- they can directly be returned. Others can then later be returned when they become
    -- available. Hence the directly-awaits set is in general empty.
    -- One exception is if the return has only one variable
    directlyAwaits = thisAwaits,
    writes = writes next,
    finallyReleases = if allAvailable then finallyReleases next else IdxSet.empty,
    -- A parallel return is non-trivial. If the return has only one variable, or if
    -- all variables are definitely available here, the return is sequential,
    -- and we can thus treat is as trivial.
    -- If the next instruction is trivial, and the return nor the next do not await on any values,
    -- we can also treat it as trivial.
    trivial = (nextIsEmpty && hasOne) || (allAvailable && trivial next && IdxSet.null (directlyAwaits next)),
    term = PartialSchedule $ PReturnValues updateTup $ term next
  }
  where
    next = next' available
    nextIsEmpty
      | PartialSchedule (PReturnEnd _) <- term next = True
      | otherwise = False

    varsSet = IdxSet.fromList $ updateTupVarList updateTup

    hasOne
      | One <- updateCount updateTup = True
      | otherwise = False

    allAvailable = varsSet `IdxSet.isSubsetOf` available

    thisAwaits
      | hasOne && nextIsEmpty = varsSet IdxSet.\\ available
      | otherwise = IdxSet.empty

buildAcond
  :: ExpVar env PrimBool
  -> Build PartialSchedule kernel env t
  -> Build PartialSchedule kernel env t
  -> Build PartialSchedule kernel env t
buildAcond var true' false' available =
  Built{
    didChange = didChange true || didChange false,
    directlyAwaits = if var `IdxSet.varMember` available then awaits else IdxSet.insertVar var awaits,
    writes = writes true `IdxSet.union` writes false,
    finallyReleases = finallyReleases true `IdxSet.intersect` finallyReleases false,
    -- true and false branch may have different sets of free variables,
    -- hence we cannot treat an it as a trivial term.
    trivial = False,
    term = PartialSchedule $ PAcond var (term true) (term false)
  }
  where
    available' = IdxSet.insertVar var available
    true = true' available'
    false = false' available'
    awaits = directlyAwaits true `IdxSet.intersect` directlyAwaits false

data BuildUnary kernel env f where
  BuildUnary
    :: GLeftHandSide s env env'
    -> Build PartialSchedule kernel env' t
    -> BuildUnary kernel env (s -> t)

buildAwhile
  :: Uniquenesses t
  -> BuildUnary kernel env (t -> Loop t)
  -> GroundVars env t
  -> Build PartialSchedule kernel env t
buildAwhile us (BuildUnary lhs fn') initial available =
  Built{
    didChange = didChange fn,
    directlyAwaits = IdxSet.fromVarList (lhsTake lhs (directlyAwaits fn) initial) `IdxSet.union` IdxSet.drop' lhs (directlyAwaits fn),
    writes = IdxSet.drop' lhs (writes fn),
    finallyReleases = IdxSet.empty,
    trivial = False,
    term = PartialSchedule $ PAwhile
      us
      (Plam lhs $ Pbody $ term fn)
      initial
  }
  where
    fn = fn' (IdxSet.skip' lhs available)

buildTrace ::
  Text ->
  ArrayDescriptors env t ->
  Build PartialSchedule kernel env Word8
buildTrace msg t available =
  Built{
    didChange = False,
    directlyAwaits = arrayDescriptorsIdxSet t IdxSet.\\ available,
    writes = IdxSet.empty,
    finallyReleases = IdxSet.empty,
    trivial = True,
    term = PartialSchedule $ PAtrace msg t
  }

buildContinue
  :: Build PartialSchedule kernel env t
  -> Build PartialSchedule kernel env (Loop t)
buildContinue next' available =
  Built{
    didChange = didChange next,
    directlyAwaits = IdxSet.empty,
    writes = writes next,
    finallyReleases = finallyReleases next,
    trivial = False,
    term = PartialSchedule $ PContinue $ term next
  }
  where
    next = next' available

buildBreak
  :: Uniquenesses t
  -> GroundVars env t
  -> Build PartialSchedule kernel env (Loop t)
buildBreak us vars _ =
  Built{
    didChange = False,
    directlyAwaits = IdxSet.fromVars vars,
    writes = IdxSet.empty,
    finallyReleases = IdxSet.empty,
    trivial = False,
    term = PartialSchedule $ PBreak us vars
  }

buildAssert
  :: Text
  -> Exp env PrimBool
  -> Build PartialSchedule kernel env PrimBool
buildAssert msg cond available =
  Built{
    didChange = False,
    directlyAwaits = IdxSet.fromVarList vars IdxSet.\\ available,
    writes = IdxSet.empty,
    finallyReleases = IdxSet.empty,
    trivial = expIsTrivial (const True) cond,
    term = PartialSchedule $ PAssert msg cond
  }
  where
    vars = expGroundVars cond

buildFence
  :: IdxSet env
  -> Build PartialSchedule kernel env t
  -> Build PartialSchedule kernel env t
buildFence deps next' available =
  Built{
    didChange = didChange next,
    directlyAwaits = deps' `IdxSet.union` directlyAwaits next,
    writes = writes next,
    finallyReleases = finallyReleases next,
    trivial = trivial next,
    term = PartialSchedule $ PFence deps' $ term next
  }
  where
    next = next' (IdxSet.union available deps)
    deps' = deps IdxSet.\\ available

updateCount :: UpdateTuple env t1 t2 -> Count
updateCount UpdateKeep = Zero
updateCount (UpdateSet _ _) = One
updateCount (UpdatePair up1 up2) = updateCount up1 <> updateCount up2

data Count = Zero | One | Many
instance Semigroup Count where
  Zero <> a    = a
  One  <> Zero = One
  _    <> _    = Many

data ToSyncSchedule kernel env t where
  ToSyncSchedule
    :: UpdateTuple env t1 t2
    -> SyncSchedule kernel env t1
    -> ToSyncSchedule kernel env t2

arrayDescriptorsSync :: ArrayDescriptors env t -> SyncEnv env
arrayDescriptorsSync TupRunit = PEnd
arrayDescriptorsSync (TupRsingle a) = arrayDescriptorSync a
arrayDescriptorsSync (TupRpair l r) = unionPartialEnv max (arrayDescriptorsSync l) (arrayDescriptorsSync r)

arrayDescriptorSync :: ArrayDescriptor env t -> SyncEnv env
arrayDescriptorSync (ArrayDescriptor _ _ buffers) = variablesToSyncEnv (mapTupR (const Shared) buffers) buffers

analyseSyncEnv :: PartialSchedule kernel env t -> SyncSchedule kernel env t
analyseSyncEnv sched
  | ToSyncSchedule up sched' <- analyseSyncEnv' sched
  = sReturnValues up sched'

sReturnValues
  :: UpdateTuple env t1 t2
  -> SyncSchedule kernel env t1
  -> SyncSchedule kernel env t2
sReturnValues UpdateKeep sched = sched
sReturnValues up sched = SyncSchedule
  (unionPartialEnv max (syncEnv sched) $ partialEnvFromList noCombine $ updateTupSync up)
  True
  (PReturnValues up sched)

analyseSyncEnv' :: PartialSchedule kernel env t -> ToSyncSchedule kernel env t
analyseSyncEnv' (PartialSchedule sched) = case sched of
  PExec kernel args ->
    let
      bindings = mapMaybe (\(Exists a) -> argToSync a) $ argsToList args
      argToSync :: SArg env a -> Maybe (EnvBinding Sync env)
      argToSync (SArgBuffer In v) = Just $ EnvBinding (varIdx v) SyncRead
      argToSync (SArgBuffer _ v) = Just $ EnvBinding (varIdx v) SyncWrite
      argToSync _ = Nothing
    in
      ToSyncSchedule UpdateKeep
        $ SyncSchedule (partialEnvFromList max bindings) True (PExec kernel args)
  PLet par lhs us bnd body
    | bnd' <- analyseSyncEnv bnd
    , ToSyncSchedule up body' <- analyseSyncEnv' body
    , HoistReturn up1 up2 <- hoistReturn lhs (syncEnv bnd') up ->
      ToSyncSchedule up1 $
        SyncSchedule
          (unionPartialEnv max (syncEnv bnd') $ weakenSyncEnv lhs $ syncEnv body')
          (syncSimple bnd' && syncSimple body' && par == Sequential)
          (PLet par lhs us bnd' $ sReturnValues up2 body')
  PAlloc shr tp sh ->
    noBuffers $ PAlloc shr tp sh
  PUse tp sz buf ->
    noBuffers $ PUse tp sz buf
  PUnit var ->
    noBuffers $ PUnit var
  PCompute expr ->
    let
      bindings = mapMaybe (\(Exists a) -> instrToSync a) $ arrayInstrsInExp expr
    in
      ToSyncSchedule UpdateKeep
        $ SyncSchedule
          (partialEnvFromList const bindings)
          True
          (PCompute expr)
  PReturnEnd tup ->
    noBuffers $ PReturnEnd tup
  PReturnValues updateTup next -> ToSyncSchedule updateTup $ analyseSyncEnv next
  PAcond var true false ->
    let
      true' = analyseSyncEnv true
      false' = analyseSyncEnv false
    in
      ToSyncSchedule UpdateKeep $
        SyncSchedule
          (unionPartialEnv max (syncEnv true') (syncEnv false'))
          False
          (PAcond var true' false')
  PAwhile us (Plam lhs (Pbody body)) initial ->
    let
      body' = analyseSyncEnv body
    in
      ToSyncSchedule UpdateKeep $
        SyncSchedule
          (unionPartialEnv max (weakenSyncEnv lhs $ syncEnv body') $ variablesToSyncEnv us initial)
          False
          (PAwhile us (Plam lhs $ Pbody body') initial)
  PAwhile{} -> internalError "Function impossible"
  PAtrace msg t ->
      ToSyncSchedule UpdateKeep $
        SyncSchedule
          (arrayDescriptorsSync t)
          True
          (PAtrace msg t)
  PContinue next ->
    let
      next' = analyseSyncEnv next
    in
      ToSyncSchedule UpdateKeep $
        SyncSchedule (syncEnv next') False $ PContinue next'
  PBreak us vars ->
    ToSyncSchedule UpdateKeep $ SyncSchedule (variablesToSyncEnv us vars) False $ PBreak us vars
  PAssert msg cond ->
    let
      bindings = mapMaybe (\(Exists a) -> instrToSync a) $ arrayInstrsInExp cond
    in
      ToSyncSchedule UpdateKeep
        $ SyncSchedule
          (partialEnvFromList const bindings)
          True
          (PAssert msg cond)
  PFence deps next ->
    let
      next' = analyseSyncEnv next
    in
      ToSyncSchedule UpdateKeep
        $ SyncSchedule
          (syncEnv next')
          (syncSimple next')
          (PFence deps next')
  where
    noBuffers :: PrePartialSchedule SyncSchedule kernel env t -> ToSyncSchedule kernel env t
    noBuffers = ToSyncSchedule UpdateKeep . SyncSchedule PEnd True

    instrToSync :: ArrayInstr env a -> Maybe (EnvBinding Sync env)
    instrToSync (Index v) = Just $ EnvBinding (varIdx v) SyncRead
    instrToSync (Parameter _) = Nothing -- Parameter is a scalar variable

variablesToSyncEnv :: Uniquenesses t -> GroundVars genv t -> SyncEnv genv
variablesToSyncEnv uniquenesses vars = partialEnvFromList noCombine $ go uniquenesses vars []
  where
    go :: Uniquenesses t -> GroundVars genv t -> [EnvBinding Sync genv] -> [EnvBinding Sync genv]
    go (TupRsingle Unique) (TupRsingle (Var (GroundRbuffer _) ix))
                          accum = EnvBinding ix SyncWrite : accum
    go (TupRsingle Shared) (TupRsingle (Var (GroundRbuffer _) ix))
                          accum = EnvBinding ix SyncRead : accum
    go u (TupRpair v1 v2) accum = go u1 v1 $ go u2 v2 accum
      where (u1, u2) = pairUniqueness u
    go _ _                accum = accum

noCombine :: Sync s -> Sync s -> Sync s
noCombine SyncRead SyncRead = SyncRead
noCombine _        _        = internalError "A writable buffer cannot be aliassed"
