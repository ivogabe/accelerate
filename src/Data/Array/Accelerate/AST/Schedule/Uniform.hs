{-# LANGUAGE EmptyCase            #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE RankNTypes           #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_HADDOCK hide #-}
-- |
-- Module      : Data.Array.Accelerate.AST.Schedule.Uniform
-- Copyright   : [2008..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.AST.Schedule.Uniform (
  UniformSchedule(..), UniformScheduleFun(..),
  SArg(..), SArgs, sargVars, sargOutputVars, sargBufferVars,
  Input, Output, inputSingle, outputSingle, inputR, outputR,
  InputOutputR(..), inputOutputInputR, inputOutputOutputR,
  Binding(..), Effect(..),
  BaseR(..), BasesR, BaseVar, BaseVars, BLeftHandSide,
  Signal(..), SignalResolver(..), Ref(..), OutputRef(..),
  module Operation,
  Cluster,
  await, resolve,
  signalResolverImpossible, scalarSignalResolverImpossible,
  rnfBaseR,
  directlyAwaits1, reorder, trivialBinding, trivialSchedule, trivialEffect,

  -- ** Free variables
  freeVars, funFreeVars, effectFreeVars, bindingFreeVars,
) where

import Data.Array.Accelerate.AST.Exp
import Data.Array.Accelerate.AST.Idx
import Data.Array.Accelerate.AST.IdxSet ( IdxSet )
import qualified Data.Array.Accelerate.AST.IdxSet as IdxSet
import Data.Array.Accelerate.AST.LeftHandSide
import Data.Array.Accelerate.AST.Var
import Data.Array.Accelerate.Type
import Data.Array.Accelerate.Representation.Array
import Data.Array.Accelerate.Representation.Shape
import Data.Array.Accelerate.Representation.Type
import qualified Data.Array.Accelerate.AST.Operation as Operation hiding (PreOpenAcc(..), PreOpenAfun(..))
import Data.Array.Accelerate.AST.Partitioned as Partitioned       hiding (PreOpenAcc(..), PreOpenAfun(..), PartitionedAcc, PartitionedAfun)
import Data.Array.Accelerate.AST.Kernel
import Data.Array.Accelerate.Trafo.Exp.Substitution
import Control.Concurrent.MVar
import Control.Monad
import Data.Either
import Data.IORef
import Data.Typeable                                                ( (:~:)(..) )

-- Generic schedule for a uniform memory space and uniform scheduling.
-- E.g., we don't have host and device memory or scheduling.
-- The schedule will exploit task parallelism.

-- The schedule consists of bindings, effects and (parallel) control flow
--
-- Some schedules/terms may be 'spawn-closed'. These terms guarantee that when
-- the execution of the term finishes, all spawned tasks have also finished.
-- For instance, this program is spawn-closed:
--
-- (s0, s0') = new signal
-- spawn {
--   ...
--   resolve [s0']
-- }
-- ...
-- await [s0]
--
-- However, this term is not self-closed, as the spawned term may outlive the
-- outer term.
--
-- spawn {
--   ...
-- }
-- ...
--
-- Note that not necessarily all subterms of a spawn-closed term as spawn-closed.
-- For instance, consider:
--
-- (s0, s0') = new signal
-- (s1, s1') = new signal
-- spawn {
--   spawn {
--     resolve [s1']
--   }
--   resolve [s0']
-- }
-- await [s0, s1]
-- Here, the first spawned term is not self-closed:
-- its execution may finish before the execution of the inner spawned term ends.
-- The entire term is self-closed, as it waits on the completions of both
-- spawned subterms.
data UniformSchedule kernel env where
  Return  :: UniformSchedule kernel env

  Alet    :: BLeftHandSide t env env'
          -> Binding env t
          -> UniformSchedule kernel env'
          -> UniformSchedule kernel env

  Effect  :: Effect kernel env
          -> UniformSchedule kernel env
          -> UniformSchedule kernel env

  Acond   :: ExpVar env PrimBool
          -> UniformSchedule kernel env -- True branch
          -> UniformSchedule kernel env -- False branch
          -> UniformSchedule kernel env -- Operations after the if-then-else
          -> UniformSchedule kernel env

  -- The step function of the loop outputs a bool to denote whether the loop should
  -- proceed. If true, then the other output values should also be filled, possibly at
  -- a later point in time. If it is false, then no other output values may be filled.
  --
  -- An Awhile loop may be executed in parallel, meaning that we may work on multiple
  -- iterations of the loop in parallel. This may be possible, typically if the state
  -- of the loop consists of multiple variables. Synchronisations are handled via
  -- Signal(Resolver)s in 'input' and 'output'.
  -- A sequential variant is available in AwhileSeq.
  Awhile  :: InputOutputR input output
          -- The body of the while loop.
          -- Should be spawn-closed.
          -> UniformScheduleFun kernel env (input -> Output PrimBool -> output -> ())
          -> BaseVars env input
          -> UniformSchedule kernel env -- Operations after the while loop
          -> UniformSchedule kernel env

  -- Variant of Awhile, that can be executed sequentially. This only applies to
  -- parallelism between iterations of the loop. Within an iteration, parallelism
  -- can be exploited as usual.
  -- Iteration 'i+1' only starts when iteration 'i' is finished. Since the
  -- step function is spawn-closed, this guarantees proper synchronisations.
  -- Hence we don't need Signal(Resolver)s in 'input' or 'output'.
  AwhileSeq
          -- Should not contain InputOutputRsignal
          :: InputOutputR input output
          -- The body of the while loop
          -- Should be spawn-closed.
          -> UniformScheduleFun kernel env (input -> OutputRef PrimBool -> output -> ())
          -> BaseVars env input
          -> UniformSchedule kernel env -- Operations after the while loop
          -> UniformSchedule kernel env

  -- Spawns a task/thread for the first subterm, and continues with the second subterm.
  -- Note that we use the name 'spawn' instead of 'fork', to imply that the first
  -- subterm is not executed directly, but handed over to a different core or queued.
  Spawn   :: UniformSchedule kernel env
          -> UniformSchedule kernel env
          -> UniformSchedule kernel env

data UniformScheduleFun kernel env t where
  Slam  :: BLeftHandSide s env env'
        -> UniformScheduleFun kernel env' t
        -> UniformScheduleFun kernel env  (s -> t)

  Sbody :: UniformSchedule    kernel env
        -> UniformScheduleFun kernel env ()

type family Input t where
  Input ()         = ()
  Input (a, b)     = (Input a, Input b)
  Input t          = (Signal, Ref t)

inputSingle :: forall t. GroundR t -> (Input t, Output t) :~: ((Signal, Ref t), (SignalResolver, OutputRef t))
-- Last case of type family Input and Output.
-- We must pattern match to convince the type checker that
-- t is not () or (a, b).
inputSingle (GroundRbuffer _) = Refl
inputSingle (GroundRscalar (VectorScalarType _)) = Refl
inputSingle (GroundRscalar (SingleScalarType (NumSingleType tp))) = case tp of
  IntegralNumType TypeInt    -> Refl
  IntegralNumType TypeInt8   -> Refl
  IntegralNumType TypeInt16  -> Refl
  IntegralNumType TypeInt32  -> Refl
  IntegralNumType TypeInt64  -> Refl
  IntegralNumType TypeWord   -> Refl
  IntegralNumType TypeWord8  -> Refl
  IntegralNumType TypeWord16 -> Refl
  IntegralNumType TypeWord32 -> Refl
  IntegralNumType TypeWord64 -> Refl
  FloatingNumType TypeHalf   -> Refl
  FloatingNumType TypeFloat  -> Refl
  FloatingNumType TypeDouble -> Refl

inputR :: forall t. GroundsR t -> BasesR (Input t)
inputR TupRunit = TupRunit
inputR (TupRpair t1 t2) = TupRpair (inputR t1) (inputR t2)
inputR (TupRsingle ground)
  -- Last case of type family Input.
  -- We must pattern match to convince the type checker that
  -- t is not () or (a, b).
  | Refl <- inputSingle ground = TupRsingle BaseRsignal `TupRpair` TupRsingle (BaseRref ground)

type family Output t where
  Output ()     = ()
  Output (a, b) = (Output a, Output b)
  Output t      = (SignalResolver, OutputRef t)

data SArg env t where
  SArgScalar :: ExpVar env e
             -> SArg env (Var' e)

  SArgBuffer :: Modifier m
             -> GroundVar env (Buffer e)
             -> SArg env (m DIM1 e)

type SArgs env = PreArgs (SArg env)

outputR :: GroundsR t -> BasesR (Output t)
outputR TupRunit = TupRunit
outputR (TupRpair t1 t2) = TupRpair (outputR t1) (outputR t2)
outputR (TupRsingle ground)
  -- Last case of type family Output.
  -- We must pattern match to convince the type checker that
  -- t is not () or (a, b).
  | Refl <- inputSingle ground = TupRsingle BaseRsignalResolver `TupRpair` TupRsingle (BaseRrefWrite ground)

outputSingle :: GroundR t -> Output t :~: (SignalResolver, OutputRef t)
outputSingle (GroundRbuffer _) = Refl
outputSingle (GroundRscalar (VectorScalarType _)) = Refl
outputSingle (GroundRscalar (SingleScalarType tp)) = case tp of
  NumSingleType (IntegralNumType t) -> case t of
    TypeInt    -> Refl
    TypeInt8   -> Refl
    TypeInt16  -> Refl
    TypeInt32  -> Refl
    TypeInt64  -> Refl
    TypeWord   -> Refl
    TypeWord8  -> Refl
    TypeWord16 -> Refl
    TypeWord32 -> Refl
    TypeWord64 -> Refl
  NumSingleType (FloatingNumType t) -> case t of
    TypeHalf   -> Refl
    TypeFloat  -> Refl
    TypeDouble -> Refl

-- Relation between input and output
data InputOutputR input output where
  InputOutputRsignal  :: InputOutputR Signal SignalResolver
  InputOutputRref     :: GroundR t -> InputOutputR (Ref t) (OutputRef t)
  InputOutputRpair    :: InputOutputR i1 o1
                      -> InputOutputR i2 o2
                      -> InputOutputR (i1, i2) (o1, o2)
  InputOutputRunit    :: InputOutputR () ()

inputOutputInputR :: InputOutputR input output -> BasesR input
inputOutputInputR InputOutputRsignal = TupRsingle BaseRsignal
inputOutputInputR (InputOutputRref tp) = TupRsingle $ BaseRref tp
inputOutputInputR (InputOutputRpair io1 io2) = inputOutputInputR io1 `TupRpair` inputOutputInputR io2
inputOutputInputR InputOutputRunit = TupRunit

inputOutputOutputR :: InputOutputR input output -> BasesR output
inputOutputOutputR InputOutputRsignal = TupRsingle BaseRsignalResolver
inputOutputOutputR (InputOutputRref tp) = TupRsingle $ BaseRrefWrite tp
inputOutputOutputR (InputOutputRpair io1 io2) = inputOutputOutputR io1 `TupRpair` inputOutputOutputR io2
inputOutputOutputR InputOutputRunit = TupRunit

-- Bindings of instructions which have some return value.
-- They cannot perform side effects.
--
data Binding env t where
  Compute       :: Exp env t
                -> Binding env t

  NewSignal     :: String -- Name for easier debugging
                -> Binding env (Signal, SignalResolver)

  NewRef        :: GroundR t
                -> Binding env (Ref t, OutputRef t)

  Alloc         :: ShapeR sh
                -> ScalarType e
                -> ExpVars env sh
                -> Binding env (Buffer e)

  Use           :: ScalarType e
                -> Int
                -> Buffer e
                -> Binding env (Buffer e)

  Unit          :: ExpVar env e
                -> Binding env (Buffer e)

  -- undefined result if the Ref hasn't been written
  RefRead       :: BaseVar env (Ref t) -> Binding env t

-- Effects do not have a return value.
data Effect kernel env where
  Exec          :: KernelMetadata kernel f
                -> KernelFun kernel f
                -> SArgs env f
                -> Effect kernel env

  SignalAwait   :: [Idx env Signal] -> Effect kernel env

  SignalResolve :: [Idx env SignalResolver] -> Effect kernel env

  RefWrite      :: BaseVar env (OutputRef t) -> BaseVar env t -> Effect kernel env

-- A base value in the schedule is a scalar, buffer, a signal (resolver)
-- or a (possibly mutable) reference
--
data BaseR t where
  BaseRground         :: GroundR t -> BaseR t
  BaseRsignal         :: BaseR Signal
  BaseRsignalResolver :: BaseR SignalResolver
  BaseRref            :: GroundR t -> BaseR (Ref t)
  BaseRrefWrite       :: GroundR t -> BaseR (OutputRef t)

instance Distributes BaseR where
  reprIsSingle (BaseRground tp) = reprIsSingle tp
  reprIsSingle BaseRsignal = Refl
  reprIsSingle BaseRsignalResolver = Refl
  reprIsSingle (BaseRref _) = Refl
  reprIsSingle (BaseRrefWrite _) = Refl

  pairImpossible (BaseRground tp) = pairImpossible tp
  unitImpossible (BaseRground tp) = unitImpossible tp

-- Tuples of base values
type BasesR = TupR BaseR

type BaseVar      = Var BaseR
type BaseVars env = Vars BaseR env

type BLeftHandSide = LeftHandSide BaseR

newtype Signal = Signal (MVar ())
newtype SignalResolver = SignalResolver (MVar ())

-- Note: Refs should only be assigned once. They start undefined, and are at some point resolved to a value
newtype Ref t  = Ref (IORef t)
newtype OutputRef t = OutputRef (IORef t)

await :: [Idx env Signal] -> UniformSchedule kernel env -> UniformSchedule kernel env
await []      schedule = schedule
await _       Return   = Return
await signals (Effect (SignalAwait signals') schedule)
                       = Effect (SignalAwait $ signals ++ signals') schedule
await signals schedule = Effect (SignalAwait signals) schedule

resolve :: [Idx env SignalResolver] -> UniformSchedule kernel env -> UniformSchedule kernel env
resolve []      schedule = schedule
resolve signals (Effect (SignalResolve signals') schedule)
                         = Effect (SignalResolve $ signals ++ signals') schedule
resolve signals schedule = Effect (SignalResolve signals) schedule

freeVars :: UniformSchedule kernel env -> IdxSet env
freeVars Return = IdxSet.empty
freeVars (Alet lhs bnd s) = bindingFreeVars bnd `IdxSet.union` IdxSet.drop' lhs (freeVars s)
freeVars (Effect effect s) = effectFreeVars effect `IdxSet.union` freeVars s
freeVars (Acond c t f s)
  = IdxSet.insertVar c
  $ IdxSet.union (freeVars t)
  $ IdxSet.union (freeVars f)
  $ freeVars s
freeVars (Awhile _ step ini continuation)
  = IdxSet.union (funFreeVars step)
  $ IdxSet.union (IdxSet.fromVarList $ flattenTupR ini)
  $ freeVars continuation
freeVars (AwhileSeq _ step ini continuation)
  = IdxSet.union (funFreeVars step)
  $ IdxSet.union (IdxSet.fromVarList $ flattenTupR ini)
  $ freeVars continuation
freeVars (Spawn s1 s2) = freeVars s1 `IdxSet.union` freeVars s2

funFreeVars :: UniformScheduleFun kernel env t -> IdxSet env
funFreeVars (Sbody s)    = freeVars s
funFreeVars (Slam lhs f) = IdxSet.drop' lhs $ funFreeVars f

bindingFreeVars :: Binding env t -> IdxSet env
bindingFreeVars (NewSignal _)  = IdxSet.empty
bindingFreeVars (NewRef _)     = IdxSet.empty
bindingFreeVars (Alloc _ _ sh) = IdxSet.fromVarList $ flattenTupR sh
bindingFreeVars (Use _ _ _)    = IdxSet.empty
bindingFreeVars (Unit var)     = IdxSet.singletonVar var
bindingFreeVars (RefRead var)  = IdxSet.singletonVar var
bindingFreeVars (Compute e)    = IdxSet.fromList $ map f $ arrayInstrsInExp e
  where
    f :: Exists (ArrayInstr env) -> Exists (Idx env)
    f (Exists (Index (Var _ idx)))     = Exists idx
    f (Exists (Parameter (Var _ idx))) = Exists idx

effectFreeVars :: Effect kernel env -> IdxSet env
effectFreeVars (Exec _ _ args)           = IdxSet.fromList $ sargVars args
effectFreeVars (SignalAwait signals)     = IdxSet.fromList $ map Exists $ signals
effectFreeVars (SignalResolve resolvers) = IdxSet.fromList $ map Exists resolvers
effectFreeVars (RefWrite ref value)      = IdxSet.insertVar ref $ IdxSet.singletonVar value

sargVar :: SArg env t -> Exists (Idx env)
sargVar (SArgScalar   v) = Exists $ varIdx v
sargVar (SArgBuffer _ v) = Exists $ varIdx v

sargVars :: SArgs env t -> [Exists (Idx env)]
sargVars (a :>: as) = sargVar a : sargVars as
sargVars ArgsNil    = []

sargOutputVar :: SArg env t -> Maybe (Exists (Idx env))
sargOutputVar (SArgScalar    _) = Nothing
sargOutputVar (SArgBuffer In _) = Nothing
sargOutputVar (SArgBuffer _  v) = Just $ Exists $ varIdx v

sargOutputVars :: SArgs env t -> [Exists (Idx env)]
sargOutputVars (a :>: as) = maybe id (:) (sargOutputVar a) $ sargOutputVars as
sargOutputVars ArgsNil    = []

sargBufferVar :: SArg env t -> Maybe (Exists (Idx env))
sargBufferVar (SArgScalar   _) = Nothing
sargBufferVar (SArgBuffer _ v) = Just $ Exists $ varIdx v

sargBufferVars :: SArgs env t -> [Exists (Idx env)]
sargBufferVars (a :>: as) = maybe id (:) (sargBufferVar a) $ sargBufferVars as
sargBufferVars ArgsNil    = []

signalResolverImpossible :: GroundsR SignalResolver -> a
signalResolverImpossible (TupRsingle (GroundRscalar tp)) = scalarSignalResolverImpossible tp

scalarSignalResolverImpossible :: ScalarType SignalResolver -> a
scalarSignalResolverImpossible (SingleScalarType (NumSingleType (IntegralNumType tp))) = case tp of {}
scalarSignalResolverImpossible (SingleScalarType (NumSingleType (FloatingNumType tp))) = case tp of {}

rnfBaseR :: BaseR t -> ()
rnfBaseR (BaseRground ground)   = rnfGroundR ground
rnfBaseR BaseRsignal            = ()
rnfBaseR BaseRsignalResolver    = ()
rnfBaseR (BaseRref ground)      = rnfGroundR ground
rnfBaseR (BaseRrefWrite ground) = rnfGroundR ground

-- Returns a list of signals on which the schedule waits before doing any
-- work. Assumes that the schedule starts with SignalAwait; the schedule
-- can be reordered to assure this by using 'reorder'.
directlyAwaits1 :: UniformSchedule kernel env -> ([Idx env Signal], UniformSchedule kernel env)
directlyAwaits1 (Effect (SignalAwait signals) next) = (signals, next)
directlyAwaits1 schedule = ([], schedule)

-- Reorders a schedule.
-- Moves SignalAwait to the front of the schedule if possible.
-- Stops at a Spawn, making it safe to call this function while
-- constructing a schedule in different parts of the tree,
-- without causing quadratic traversal costs.
reorder :: forall kernel env. UniformSchedule kernel env -> UniformSchedule kernel env
reorder = uncurry await . go Just
  where
    go :: env' :?> env -> UniformSchedule kernel env' -> ([Idx env Signal], UniformSchedule kernel env')
    -- Try to move SignalAwait to the front of the schedule
    go k (Effect (SignalAwait awaits) next) = (rs ++ signals, await ls next')
      where
        (ls, rs) = partitionEithers $ map (try k) awaits
        (signals, next') = go k next
    -- Write may be postponed: a write doesn't do synchronisation,
    -- that is done by a signal(resolver).
    go k (Effect effect@RefWrite{} next) = (signals, Effect effect next')
      where
        (signals, next') = go k next
    go k (Alet lhs bnd next)
      | trivialBinding bnd = (signals, Alet lhs bnd next')
      where
        (signals, next') = go (k <=< strengthenWithLHS lhs) next
    go _ sched = ([], sched)

    try :: env' :?> env -> Idx env' t -> Either (Idx env' t) (Idx env t)
    try k ix = case k ix of
      Just ix' -> Right ix'
      Nothing  -> Left ix

-- If a binding will only take little time to execute, we say it's trivial and
-- move it (usually postpone) in the schedule.
trivialBinding :: Binding env t -> Bool
trivialBinding (NewSignal _)       = True
trivialBinding (NewRef _)          = True
trivialBinding (Alloc _ _ _)       = True
trivialBinding (Use _ _ _)         = True
trivialBinding (Unit _)            = True
trivialBinding (RefRead _)         = True
trivialBinding (Compute e)         = expIsTrivial (const True) e

-- If a schedule does not do blocking or slow operations, we say it's trivial
-- and don't need to spawn it as we do not gain much task parallelism from it.
trivialSchedule :: UniformSchedule kernel env -> Bool
trivialSchedule (Effect effect next)      = trivialEffect effect && trivialSchedule next
trivialSchedule (Alet _ bnd next)         = trivialBinding bnd && trivialSchedule next
trivialSchedule Return                    = True
trivialSchedule (Acond _ true false next) = trivialSchedule true && trivialSchedule false && trivialSchedule next
trivialSchedule _                         = False

trivialEffect :: Effect kernel env -> Bool
trivialEffect SignalResolve{} = True
trivialEffect RefWrite{}      = True
trivialEffect _               = False
