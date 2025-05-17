{-# LANGUAGE ConstraintKinds     #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE ImpredicativeTypes  #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE MultiWayIf          #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE PatternGuards       #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}
{-# LANGUAGE TypeFamilies        #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# OPTIONS_HADDOCK hide #-}

-- |
-- Module      : Data.Array.Accelerate.Trafo.Schedule.Uniform
-- Copyright   : [2012..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.Trafo.Schedule.Uniform (
  -- Exports the instance IsSchedule UniformScheduleFun

  compileKernel', CompiledKernel(..), rnfSArg, rnfSArgs,
) where

import Data.Array.Accelerate.Analysis.Match
import Data.Array.Accelerate.AST.Environment
import Data.Array.Accelerate.AST.Idx
import Data.Array.Accelerate.AST.IdxSet (IdxSet(..))
import qualified Data.Array.Accelerate.AST.IdxSet           as IdxSet
import Data.Array.Accelerate.AST.LeftHandSide
import Data.Array.Accelerate.AST.Kernel
import Data.Array.Accelerate.AST.Schedule
import Data.Array.Accelerate.AST.Schedule.Uniform
import Data.Array.Accelerate.AST.Var
import Data.Array.Accelerate.Error
import Data.Array.Accelerate.Representation.Ground
import Data.Array.Accelerate.Representation.Shape
import Data.Array.Accelerate.Representation.Type
import Data.Array.Accelerate.Trafo.Exp.Substitution
import Data.Array.Accelerate.Trafo.Substitution
import Data.Array.Accelerate.Trafo.Var
import Data.Array.Accelerate.Trafo.Schedule.Partial
import Data.Array.Accelerate.Trafo.Schedule.Uniform.Future
import Data.Array.Accelerate.Trafo.Schedule.Uniform.Simplify
import Data.Array.Accelerate.Trafo.Schedule.Uniform.LiveVars
import Data.Array.Accelerate.Trafo.SkipEnvironment
import Data.Array.Accelerate.Type
import Data.Array.Accelerate.AST.Partitioned (PartitionedAfun)
import qualified Data.Array.Accelerate.AST.Partitioned as C
import Data.Maybe
import Prelude hiding (id, (.), read)
import Control.Category
import Control.DeepSeq hiding (Unit(..))
import Control.Concurrent
import Data.IORef
import System.IO.Unsafe (unsafePerformIO)

instance IsSchedule UniformScheduleFun where
  type ScheduleInput  UniformScheduleFun a = Input a
  type ScheduleOutput UniformScheduleFun a = Output a

  convertScheduleFun = transformAfun

  rnfSchedule (Slam lhs s) = rnfLeftHandSide rnfBaseR lhs `seq` rnfSchedule s
  rnfSchedule (Sbody s) = rnfSchedule' s

  callScheduledFun (GFunctionRbody repr) f
    | Refl <- reprIsBody @UniformScheduleFun repr = do
      (output, result) <- bindOutput repr
      f output
      return result
    where
      bindOutput :: GroundsR t -> IO (Output t, t)
      bindOutput TupRunit = return ((), ())
      bindOutput (TupRpair tp1 tp2) = do
        (out1, result1) <- bindOutput tp1
        (out2, result2) <- bindOutput tp2
        return ((out1, out2), (result1, result2))
      bindOutput (TupRsingle tp)
        | Refl <- outputSingle tp = do
          ref <- newIORef $ internalError "Illegal schedule: Read from ref without value. Some synchronization might be missing."
          mvar <- newEmptyMVar
          -- We return the result lazily, as the value is not yet available
          let value = unsafePerformIO $ do
                readMVar mvar
                readIORef ref
          return ((SignalResolver mvar, OutputRef ref), value)
  callScheduledFun (GFunctionRlam arg ret) f = do
    return $ \a -> do
      input <- bindInput arg a
      callScheduledFun @UniformScheduleFun ret $ f input
    where
      bindInput :: GroundsR t -> t -> IO (Input t)
      bindInput TupRunit _ = return ()
      bindInput (TupRpair tp1 tp2) (val1, val2) = do
        in1 <- bindInput tp1 val1
        in2 <- bindInput tp2 val2
        return (in1, in2)
      bindInput (TupRsingle tp) value
        | Refl <- inputSingle tp = do
          ref <- newIORef $ internalError "Illegal schedule: Read from ref without value. Some synchronization might be missing."
          mvar <- newEmptyMVar
          -- We consume the result lazily. The computation can already start
          -- asynchronously, and some parts/threads of the computation may at
          -- some point block on the input to be available.
          _ <- forkIO $ do
            -- In a separate thread, evaluate to WHNF
            value `seq` return ()
            -- and write value to reference and resolve signal
            writeIORef ref value
            putMVar mvar ()
          return (Signal mvar, Ref ref)

transformAfun
  :: IsKernel kernel
  => PartitionedAfun (KernelOperation kernel) () f
  -> UniformScheduleFun kernel () (Scheduled UniformScheduleFun f)
transformAfun afun = simplify $ stronglyLiveVariablesFun $ simplify $ stronglyLiveVariablesFun $ simplify $ stronglyLiveVariablesFun $ makeFunSpawnClosed $ funConstruct (go FEnvEnd afun) weakenId BEmpty
  where
    go
      :: IsKernel kernel
      => FutureEnv fenv genv
      -> PartitionedAfun (KernelOperation kernel) genv f
      -> BuildScheduleFun kernel fenv (Scheduled UniformScheduleFun f)
    go env (C.Alam lhs f)
      | DeclareInput _ lhs' env' <- declareInput lhs env
      = buildFunLam lhs' $ go env' f
    go env (C.Abody body)
      | Refl <- reprIsBody @UniformScheduleFun $ groundsR body
      , schedule <- convertAccPartial body
      , DeclareOutput skip lhs dest <- declareOutput $ groundsR body
      = buildFunLam lhs $ buildFunBody $
          transformSub (fenvFSkipMany skip env) Parallel (CtxNormal $ dest SkipNone) schedule

-- Transforms a SyncSchedule to a UniformSchedule.
-- Assumes that the FutureEnv corresponds with the syncEnv of the schedule.
transform
  :: IsKernel kernel
  => FutureEnv fenv genv -- Mapping from ground environment to future environment
  -> Parallelism -- Whether the returns should happen in parallel or sequential.
  -> Context kernel fenv t -- The destinations for the output
  -> SyncSchedule kernel genv t -- The SyncSchedule that should be transformed to a UniformSchedule
  -> BuildSchedule kernel fenv
transform env parallelism ctx schedule = case transform' schedule of
  TransformSchedule f -> f env parallelism ctx
  TransformBinding f
    | TransformToBinding tp skip instr resolvers binding <- f env
    , DeclareVars lhs k vars <- declareVars tp -> 
      case ctx of
        CtxLoop{} -> internalError "Loop impossible"
        CtxNormal dest ->
          instr
            $ buildLet (mapLeftHandSide BaseRground lhs) binding
            $ buildEffect (SignalResolve $ weaken (weakenWithLHS lhs) <$> resolvers)
            $ writeOutput (mapTupR (weaken k . weaken (skipWeakenIdx skip)) dest) (vars weakenId)

-- Variant of 'transform' that also performs the subenvironment rule:
-- transform assumes that the FutureEnv corresponds with the syncEnv of the schedule,
-- but transformSub correctly handles redundant entries in the FutureEnv.
transformSub
  :: IsKernel kernel
  => FutureEnv fenv genv -- Mapping from ground environment to future environment
  -> Parallelism
  -> Context kernel fenv t
  -> SyncSchedule kernel genv t -- The SyncSchedule that should be transformed to a UniformSchedule
  -> BuildSchedule kernel fenv
transformSub env parallelism dest schedule = buildSpawn actions
  $ transform env' parallelism dest schedule
  where
    (env', actions) = subFutureEnvironment env (syncEnv schedule)

data Transform kernel genv t where
  TransformSchedule
    :: (forall fenv. FutureEnv fenv genv -> Parallelism -> Context kernel fenv t -> BuildSchedule kernel fenv)
    -> Transform kernel genv t

  TransformBinding
    :: (forall fenv. FutureEnv fenv genv -> (TransformToBinding kernel fenv t))
    -> Transform kernel genv t

-- Captures existential fenv'
data TransformToBinding kernel fenv t where
  TransformToBinding
    :: GroundsR t
    -> Skip fenv' fenv
    -> (BuildSchedule kernel fenv' -> BuildSchedule kernel fenv)
    -> [Idx fenv' SignalResolver]
    -> Binding fenv' t
    -> TransformToBinding kernel fenv t

-- Invariants:
-- - If 'simple' then Parallelism (argument of TransformSchedule) is Sequential.
-- - If 'simple' then we may not introduce forks for this term.
-- - Parallelism is not SequentialInNextParallel
transform'
  :: IsKernel kernel
  => SyncSchedule kernel genv t -- The SyncSchedule that should be transformed to a UniformSchedule
  -> Transform kernel genv t
transform' (SyncSchedule _ simple schedule) = case schedule of
  -- Return & return values
  PReturnEnd _ -> TransformSchedule $ \_ _ _ -> buildReturn
  PReturnValues updateTup next -> TransformSchedule $ \fenv parallelism ctx ->
    case ctx of
      CtxLoop{} -> internalError "Loop impossible"
      CtxNormal dest
        | (dest', instr) <- returnValues fenv parallelism updateTup dest
        , next' <- transformSub fenv parallelism (CtxNormal dest') next ->
          instr next'

  -- Effects
  PExec kernel args -> TransformSchedule $ \fenv _ _ ->
    case acquireArgs fenv args of
      AcquireArgs skip signals resolvers instr args' ->
        buildEffect (SignalAwait signals)
          $ instr
          $ buildEffect (Exec (kernelMetadata kernel) kernel $ args' SkipNone)
          $ buildEffect (SignalResolve $ map (weaken $ skipWeakenIdx skip) resolvers) buildReturn

  -- Bindings
  PAlloc shr tp sh -> TransformBinding $ \fenv ->
    case acquireVars fenv sh of
      AcquireVars skip instr sh' ->
        TransformToBinding (TupRsingle $ GroundRbuffer tp) skip instr [] $ Alloc shr tp $ sh' SkipNone
  PUse tp sz buf -> TransformBinding $ \_ ->
    TransformToBinding (TupRsingle $ GroundRbuffer tp) SkipNone id [] $ Use tp sz buf
  PUnit var -> TransformBinding $ \fenv ->
    case fprj (varIdx var) fenv of
      Just (FutureScalar tp signal (Left idx)) ->
        TransformToBinding (TupRsingle $ GroundRbuffer tp) SkipNone (buildAwait [signal]) [] $ Unit $ Var tp idx
      Just (FutureScalar tp signal (Right idx)) ->
        TransformToBinding
          (TupRsingle $ GroundRbuffer tp)
          (SkipSucc SkipNone)
          (buildAwait [signal]
            . buildLet (LeftHandSideSingle $ BaseRground $ GroundRscalar tp) (RefRead $ Var (BaseRref $ GroundRscalar tp) idx))
          []
          (Unit $ Var tp ZeroIdx)
      _ -> variableMissing
  PCompute expr -> TransformBinding $ \fenv ->
    case acquireSome fenv $ IdxSet.fromVarList $ expGroundVars expr of
      AcquireSome skip signals resolvers instr mapping'
        | mapping <- mapping' SkipNone ->
          TransformToBinding
            (mapTupR GroundRscalar $ expType expr)
            skip
            (buildEffect (SignalAwait signals) . instr)
            (weaken (skipWeakenIdx skip) <$> resolvers)
            (Compute $ mapArrayInstr
              (weaken (Weaken $ \idx ->
                fromMaybe (internalError "Variable missing after acquireSome") $ prjPartial idx mapping))
              expr)

  PLet bndParallelism (LeftHandSideWildcard tp) _ bnd body -> TransformSchedule $ \fenv parallelism ctx ->
    case chainFutureEnvironmentSeqIf (bndParallelism == Sequential && simple) fenv (syncEnv bnd) (syncEnv body) of
      ChainFutureEnv instr skip bndEnv bodyEnv ->
        let
          bnd' = transform bndEnv bndParallelism (CtxNormal $ mapTupR (const DestinationIgnore) tp) bnd
          body' = transform bodyEnv parallelism (weaken (skipWeakenIdx skip) ctx) body
        in instr $ buildSeqOrSpawn bndParallelism bnd' body'

  PLet Parallel lhs us bnd body -> TransformSchedule $ \fenv parallelism ctx ->
    case chainFutureEnvironment SkipNone fenv (syncEnv bnd) (environmentDropLHS (syncEnv body) lhs) of
      ChainFutureEnv instr1 skip1 bndEnv bodyEnv
        | DeclareDestinations skip2 instr2 bndDestinations bodyEnv' <- declareDestinations Parallel bodyEnv lhs us
        , bodyEnv'' <- restrictEnvForLHS lhs bodyEnv' $ syncEnv body ->
          let
            k = skipWeakenIdx skip2 .> skipWeakenIdx skip1
            bnd' = transform (fenvFSkipMany skip2 bndEnv) Parallel (CtxNormal $ bndDestinations SkipNone) bnd
            body' = transform bodyEnv'' parallelism (weaken k ctx) body
          in instr1 $ instr2 $ buildSpawn bnd' body'

  PLet Sequential lhs us bnd body -> TransformSchedule $ \fenv parallelism ctx ->
    case chainFutureEnvironmentSeqIf simple fenv (syncEnv bnd) (environmentDropLHS (syncEnv body) lhs) of
      ChainFutureEnv instr1 skip1 bndEnv bodyEnv ->
        case transform' bnd of
          TransformBinding f
            | TransformToBinding _ skip2 instr2 resolvers binding <- f bndEnv
            , Exists lhs' <- rebuildLHS lhs
            , bodyEnv' <- fenvPushLHS lhs lhs' us $ fenvFSkipMany skip2 bodyEnv
            , bodyEnv'' <- restrictEnvForLHS lhs bodyEnv' $ syncEnv body ->
              instr1 $ instr2
                $ buildLet (mapLeftHandSide BaseRground lhs') binding
                $ buildEffect (SignalResolve $ weaken (weakenWithLHS lhs') <$> resolvers)
                $ transform bodyEnv'' parallelism (weaken (weakenWithLHS lhs' .> skipWeakenIdx skip2 .> skipWeakenIdx skip1) ctx) body
          TransformSchedule f
            | DeclareDestinations skip2 instr2 bndDestinations bodyEnv' <- declareDestinations Parallel bodyEnv lhs us
            , bodyEnv'' <- restrictEnvForLHS lhs bodyEnv' $ syncEnv body
            , MakeAvailable skip3 bodyEnv''' instr3 <- makeAvailable lhs bodyEnv'' ->
              instr1 $ instr2 $ buildSpawn
                (f (fenvFSkipMany skip2 bndEnv) Sequential $ CtxNormal $ bndDestinations SkipNone)
                $ instr3
                $ transform bodyEnv''' parallelism (weaken (skipWeakenIdx' skip3 .> skipWeakenIdx skip2 .> skipWeakenIdx skip1) ctx) body

  -- Control flow
  PAcond cond true false -> TransformSchedule $ \fenv parallelism dest ->
    case fprj (varIdx cond) fenv of
      Just (FutureScalar tp signal ref) ->
        buildAwait [signal] $
          withRef (GroundRscalar tp) ref $ \skip var ->
            buildAcond (Var (varType cond) (varIdx var))
              (weaken' (skipWeakenIdx skip) $ transformSub fenv parallelism dest true)
              (weaken' (skipWeakenIdx skip) $ transformSub fenv parallelism dest false)
              buildReturn
      _ -> variableMissing
  
  PAwhile us fn initial -> TransformSchedule $ \fenv _ ctx ->
    transformWhile fenv us fn initial ctx

  PContinue next -> TransformSchedule $ \fenv parallelism ctx -> 
    case ctx of
      CtxNormal _ -> internalError "Loop impossible"
      CtxLoop _ destBool dest _ ->
        buildSeq
          (writeLoopCondition destBool True)
          (transform fenv parallelism (CtxNormal dest) next)

  PBreak us vars -> TransformSchedule $ \fenv _ ctx ->
    case ctx of
      CtxNormal _ -> internalError "Loop impossible"
      CtxLoop release destBool _ dest ->
        buildSeq
          (writeLoopCondition destBool False)
          $ buildSpawn
            release
            $ snd (returnValues fenv Parallel (toPartialReturn us vars) dest) buildReturn

transformWhile
  :: IsKernel kernel =>
     FutureEnv fenv genv
  -> Uniquenesses t
  -> SyncScheduleFun kernel genv (t -> Loop t)
  -> GroundVars genv t
  -> Context kernel fenv t
  -> BuildSchedule kernel fenv
transformWhile _ _ _ _ CtxLoop{} = internalError "Impossible nesting of loops"
transformWhile fenv us (Plam lhs (Pbody step)) groundInitial (CtxNormal finalDest)
  | fenv' <- FEnvFSkip $ FEnvFSkip fenv -- Add two bindings to the environment for a new signal and resolver.
  -- Split the environment into an environment for the initial state and an environment for the step function.
  , ChainFutureEnv instr1 skip1 initialEnv stepEnv
    <- chainFutureEnvironment SkipNone fenv' (variablesToSyncEnv us groundInitial) (environmentDropLHS (syncEnv step) lhs)
  -- The index of an already resolved signal. Used to construct the initial state.
  , resolved <- weaken (skipWeakenIdx skip1) $ SuccIdx ZeroIdx
  -- Creates the environment for the free variables of the step function.
  , LoopFutureEnv io1 initial1 localR body <- loopFutureEnv resolved stepEnv
  -- Extend the environment with the arguments of the function,
  -- And prepare the destination for the result of the function (state for next iteration).
  , AwhileInputOutput io2 skip2 instr2 initial2 extendStepEnv' makeContinueDest
    <- awhileInputOutput initialEnv resolved lhs us groundInitial
  , io <- InputOutputRpair io1 io2
  -- Given the computed types, construct the left hand sides for the function.
  , DeclareVars lhsInput _ varsInput <- declareVars $ inputOutputInputR io
  , DeclareVars lhsOutput k2 varsOutput <- declareVars $ inputOutputOutputR io
  , DeclareVars lhsLocal k3 varsLocal <- declareVars $ localBaseR localR
  -- Compose the Skips for all left hand sides of the function.
  , funSkip <- lhsSkip lhsLocal
    `chainSkip` SkipSucc (SkipSucc $ lhsSkip lhsOutput)
    `chainSkip` lhsSkip lhsInput
  -- Compose that with the Skips of instr1 and instr2.
  , fullSkip <- funSkip `chainSkip` skip2 `chainSkip` (SkipSucc $ SkipSucc skip1)
  -- Separate the input into an input for loopFutureEnv (input1) and awhileInputOutput (input2)
  , (input1, input2) <- expectPair $ varsInput (k3 .> (weakenSucc $ weakenSucc k2))
  -- Also separate the output
  , (output1, output2) <- expectPair $ varsOutput k3
  -- Using this input and output, construct the things regarding loopFutureEnv for within the step function
  , LoopFutureEnvInner instr3 release stepEnv' <- body (funSkip `chainSkip` skip2) (mapTupR varIdx input1) (mapTupR varIdx output1)
    $ mapTupR varIdx $ varsLocal $ weakenId
  -- Construct the destination and context for the step function
  , ctx <- CtxLoop
      release
      (weaken (skipWeakenIdx (lhsSkip lhsLocal `chainSkip` lhsSkip lhsOutput))
        $ DestinationShared ZeroIdx $ SuccIdx ZeroIdx)
      (makeContinueDest output2)
      (mapTupR
        (weaken $ skipWeakenIdx fullSkip)
        finalDest)
  = buildLet lhsSignal (NewSignal "resolved signal for while")
    $ buildEffect (SignalResolve [ZeroIdx])
    $ instr1
    $ instr2
    $ buildAwhile
      io
      (buildFunLam lhsInput
        $ buildFunLam (LeftHandSidePair (LeftHandSideSingle BaseRsignalResolver) (LeftHandSideSingle $ BaseRrefWrite $ GroundRscalar scalarType))
        $ buildFunLam lhsOutput
        $ buildFunBody
        $ declareSignals localR lhsLocal
        $ buildSpawn instr3
        $ transform (extendStepEnv' input2 stepEnv') Parallel ctx step
      )
      (TupRpair (mapTupR (weaken $ skipWeakenIdx skip2) initial1) (initial2 SkipNone))
      buildReturn
  where
    expectPair :: TupR s (t1, t2) -> (TupR s t1, TupR s t2)
    expectPair (TupRpair t1 t2) = (t1, t2)
    expectPair _ = internalError "Pair impossible"
transformWhile _ _ _ _ _ = internalError "Function impossible"

writeOutput
  :: Destinations fenv t
  -> GroundVars fenv t
  -> BuildSchedule kernel fenv
writeOutput (TupRsingle dest) (TupRsingle (Var tp idx))
  | Just ref <- destRef dest =
    buildEffect (RefWrite (Var (BaseRrefWrite tp) ref) (Var (BaseRground tp) idx))
      $ buildEffect (SignalResolve $ catMaybes [destResolver dest, destResolverWrite dest]) buildReturn
  | otherwise = buildReturn -- This return value is ignored (e.g., via LeftHandSideWildcard)
writeOutput (TupRpair dest1 dest2) (TupRpair vars1 vars2) =
  buildSeq (writeOutput dest1 vars1) (writeOutput dest2 vars2)
writeOutput TupRunit TupRunit = buildReturn
writeOutput _ _ = internalError "Tuple mismatch"

writeLoopCondition
  :: Destination fenv PrimBool
  -> Bool
  -> BuildSchedule kernel fenv
writeLoopCondition dest value =
  buildLet (LeftHandSideSingle $ BaseRground tp)
    (Compute $ Const scalarType $ if value then 1 else 0)
    $ writeOutput (TupRsingle $ weaken (weakenSucc weakenId) dest) (TupRsingle $ Var tp ZeroIdx)
  where
    tp = GroundRscalar scalarType

returnValues
  :: FutureEnv fenv genv
  -> Parallelism
  -> UpdateTuple genv t1 t2
  -> Destinations fenv t2
  -> (Destinations fenv t1, BuildSchedule kernel fenv -> BuildSchedule kernel fenv)
returnValues fenv par tup dest = (dest', \next -> foldr (buildSeqOrSpawn par) next terms)
  where
    (dest', terms) = returnValuesSpawns fenv tup dest

returnValuesSpawns
  :: FutureEnv fenv genv
  -> UpdateTuple genv t1 t2
  -> Destinations fenv t2
  -> (Destinations fenv t1, [BuildSchedule kernel fenv])
returnValuesSpawns _ UpdateKeep dest = (dest, [])
returnValuesSpawns env (UpdateSet u var) (TupRsingle dest) = 
  (TupRunit, [returnValue env u var dest])
returnValuesSpawns env (UpdatePair up1 up2) (TupRpair dest1 dest2)
  | (dest1', s1) <- returnValuesSpawns env up1 dest1
  , (dest2', s2) <- returnValuesSpawns env up2 dest2
  = (TupRpair dest1' dest2', s1 ++ s2)
returnValuesSpawns _ _ _ = internalError "Tuple mismatch"

returnValue
  :: FutureEnv fenv genv
  -> Uniqueness t
  -> GroundVar genv t
  -> Destination fenv t
  -> BuildSchedule kernel fenv
returnValue env u var dest
  | Just outRef <- destRef dest = case fprj (varIdx var) env of
    Nothing -> variableMissing
    -- Return scalar value
    Just (FutureScalar tp signal ref) ->
      buildAwait [signal]
        $ withRef (GroundRscalar tp) ref
        $ \skip var' -> buildEffect (RefWrite (weaken (skipWeakenIdx skip) $ Var (BaseRrefWrite $ GroundRscalar tp) outRef) var')
        $ buildEffect (SignalResolve $ catMaybes [weaken (skipWeakenIdx skip) <$> destResolver dest])
        buildReturn
    -- Return shared buffer
    Just (FutureBuffer tp ref read Nothing)
      | Unique <- u -> internalError "Error in construction of schedule: shared buffer returned as unique buffer"
      | otherwise ->
        buildAwait [lockSignal read]
          $ withRef (GroundRbuffer tp) ref
          $ \skip var' -> buildEffect (RefWrite (weaken (skipWeakenIdx skip) $ Var (BaseRrefWrite $ GroundRbuffer tp) outRef) var')
          $ buildEffect (SignalResolve $ catMaybes [weaken (skipWeakenIdx skip) <$> destResolver dest])
          buildReturn
    Just (FutureBuffer tp ref read (Just write))
      | Shared <- u -> internalError "Error in construction of schedule: unique buffer returned as shared buffer"
      | otherwise ->
        buildAwait [lockSignal read]
          $ withRef (GroundRbuffer tp) ref
          $ \skip var' -> buildEffect (RefWrite (weaken (skipWeakenIdx skip) $ Var (BaseRrefWrite $ GroundRbuffer tp) outRef) var')
          $ buildEffect (SignalResolve $ catMaybes [weaken (skipWeakenIdx skip) <$> destResolver dest])
          $ buildAwait [weaken (skipWeakenIdx skip) <$> lockSignal write]
          $ buildEffect (SignalResolve $ catMaybes [weaken (skipWeakenIdx skip) <$> destResolverWrite dest])
          buildReturn
  | otherwise = buildReturn

buildSeqOrSpawn :: Parallelism -> BuildSchedule kernel fenv -> BuildSchedule kernel fenv -> BuildSchedule kernel fenv
buildSeqOrSpawn Sequential = buildSeq
buildSeqOrSpawn _ = buildSpawn

data Destination fenv t
  = DestinationIgnore
  -- In sequential mode, we only use a Ref to store the result.
  -- No synchronisation for this result is needed as the next term starts after
  -- this term.
  | DestinationSequential (Idx fenv (OutputRef t))
  -- Destination of a shared resource, in parallel mode.
  -- Signal that the resource is available. The Ref is then filled,
  -- and in case of a buffer, grants read access.
  | DestinationShared (Idx fenv (OutputRef t)) (Idx fenv SignalResolver)
  -- Destination of a unique buffer, in parallel mode.
  -- Compared to DestinationShared, it now also gets a signal to grant write
  -- access.
  | DestinationUnique  (Idx fenv (OutputRef t)) (Idx fenv SignalResolver) (Idx fenv SignalResolver)

destRef :: Destination fenv t -> Maybe (Idx fenv (OutputRef t))
destRef (DestinationSequential r) = Just r
destRef (DestinationShared r _)   = Just r
destRef (DestinationUnique r _ _) = Just r
destRef _ = Nothing

destResolver :: Destination fenv t -> MaybeSignalResolver fenv
destResolver (DestinationShared _ s) = Just s
destResolver (DestinationUnique _ s _) = Just s
destResolver _ = Nothing

destResolverWrite :: Destination fenv t -> MaybeSignalResolver fenv
destResolverWrite (DestinationUnique _ _ s) = Just s
destResolverWrite _ = Nothing

instance Sink Destination where
  weaken _ DestinationIgnore = DestinationIgnore
  weaken k (DestinationSequential ref) = DestinationSequential (weaken k ref)
  weaken k (DestinationShared ref s1) = DestinationShared (weaken k ref) (weaken k s1)
  weaken k (DestinationUnique ref s1 s2) = DestinationUnique (weaken k ref) (weaken k s1) (weaken k s2)

type Destinations fenv = TupR (Destination fenv)

data Context kernel fenv t where
  CtxNormal
    :: Destinations fenv t
    -> Context kernel fenv t
  CtxLoop
    :: BuildSchedule kernel fenv
    -> Destination fenv PrimBool -- Condition (true = another iteration)
    -> Destinations fenv t -- State for next iteration
    -> Destinations fenv t -- Result of loop
    -> Context kernel fenv (Loop t)

instance Sink (Context kernel) where
  weaken k (CtxNormal dest) = CtxNormal $ mapTupR (weaken k) dest
  weaken k (CtxLoop release destCond destContinue destBreak) = CtxLoop
    (weaken' k release)
    (weaken k destCond)
    (mapTupR (weaken k) destContinue)
    (mapTupR (weaken k) destBreak)

data DeclareDestinations kernel fenv genv t where
  DeclareDestinations
    :: Skip fenv' fenv
    -> (BuildSchedule kernel fenv' -> BuildSchedule kernel fenv)
    -> (forall fenv''. Skip fenv'' fenv' -> Destinations fenv'' t)
    -> FutureEnv fenv' genv
    -> DeclareDestinations kernel fenv genv t

declareDestinations :: Parallelism -> FutureEnv fenv genv -> GLeftHandSide t genv genv' -> Uniquenesses t -> DeclareDestinations kernel fenv genv' t
declareDestinations Sequential env (LeftHandSideSingle tp) (TupRsingle u) =
  DeclareDestinations
    (SkipSucc $ SkipSucc $ SkipNone)
    (buildLet (lhsRef tp) $ NewRef tp)
    (\skip' -> TupRsingle $ DestinationSequential $ weaken (skipWeakenIdx skip') ZeroIdx)
    (FEnvPush (FEnvFSkip $ FEnvFSkip env) future)
  where
    future = case tp of
      GroundRscalar t -> FutureScalar t Nothing (Right $ SuccIdx ZeroIdx)
      GroundRbuffer t
        | Shared <- u -> FutureBuffer t (Right $ SuccIdx ZeroIdx) (Move Nothing) Nothing
        | otherwise -> FutureBuffer t (Right $ SuccIdx ZeroIdx) (Move Nothing) (Just $ Move Nothing)
declareDestinations Parallel env (LeftHandSideSingle tp) (TupRsingle Shared) =
  DeclareDestinations
    (SkipSucc $ SkipSucc $ SkipSucc $ SkipSucc $ SkipNone)
    (buildLet lhsSignal (NewSignal "declareDeclarations (Shared)") . buildLet (lhsRef tp) (NewRef tp))
    (\skip' -> TupRsingle $ DestinationShared
      (weaken (skipWeakenIdx skip') ZeroIdx)
      (weaken (skipWeakenIdx skip') $ SuccIdx $ SuccIdx ZeroIdx))
    (FEnvPush (FEnvFSkip $ FEnvFSkip $ FEnvFSkip $ FEnvFSkip env) future)
  where
    future = case tp of
      GroundRscalar t -> FutureScalar t (Just $ SuccIdx $ SuccIdx $ SuccIdx ZeroIdx) (Right $ SuccIdx ZeroIdx)
      GroundRbuffer t -> FutureBuffer t (Right $ SuccIdx ZeroIdx) (Move $ Just $ SuccIdx $ SuccIdx $ SuccIdx ZeroIdx) Nothing
declareDestinations Parallel env (LeftHandSideSingle tp@(GroundRbuffer t)) (TupRsingle Unique) =
  DeclareDestinations
    (SkipSucc $ SkipSucc $ SkipSucc $ SkipSucc $ SkipSucc $ SkipSucc $ SkipNone)
    (buildLet lhsSignal (NewSignal "declareDeclarations (Unique, 1)") . buildLet lhsSignal (NewSignal "declareDeclarations (Unique, 2)") . buildLet (lhsRef tp) (NewRef tp))
    (\skip' -> TupRsingle $ DestinationUnique
      (weaken (skipWeakenIdx skip') ZeroIdx)
      (weaken (skipWeakenIdx skip') $ SuccIdx $ SuccIdx ZeroIdx)
      (weaken (skipWeakenIdx skip') $ SuccIdx $ SuccIdx $ SuccIdx $ SuccIdx ZeroIdx))
    (FEnvPush (FEnvFSkip $ FEnvFSkip $ FEnvFSkip $ FEnvFSkip $ FEnvFSkip $ FEnvFSkip env) future)
  where
    future = FutureBuffer t
      (Right $ SuccIdx ZeroIdx)
      (Move $ Just $ SuccIdx $ SuccIdx $ SuccIdx ZeroIdx)
      (Just $ Move $ Just $ SuccIdx $ SuccIdx $ SuccIdx $ SuccIdx $ SuccIdx ZeroIdx)
declareDestinations _ env (LeftHandSideWildcard tp) _ =
  DeclareDestinations
    SkipNone
    id
    (const $ mapTupR (const DestinationIgnore) tp)
    env
declareDestinations par env (LeftHandSidePair lhs1 lhs2) us
  | DeclareDestinations skip1 instr1 dest1 env1 <- declareDestinations par env lhs1 us1
  , DeclareDestinations skip2 instr2 dest2 env2 <- declareDestinations par env1 lhs2 us2
  = DeclareDestinations
      (chainSkip skip2 skip1)
      (instr1 . instr2)
      (\skip -> dest1 (chainSkip skip skip2) `TupRpair` dest2 skip)
      env2
  where
    (us1, us2) = pairUniqueness us
declareDestinations _ _ _ _ = internalError "Tuple mismatch between LHS and uniqueness"

data AcquireArgs kernel fenv f where
  -- Captures existential fenv'.
  AcquireArgs
    :: Skip fenv' fenv
    -> [Idx fenv Signal]
    -> [Idx fenv SignalResolver]
    -> (BuildSchedule kernel fenv' -> BuildSchedule kernel fenv)
    -> (forall fenv''. Skip fenv'' fenv' -> SArgs fenv'' f)
    -> AcquireArgs kernel fenv f

acquireArgs :: forall kernel fenv genv f. FutureEnv fenv genv -> SArgs genv f -> AcquireArgs kernel fenv f
acquireArgs env (a :>: as)
  | AcquireArgs skip2 signals2 resolvers2 instr2 as' <- acquireArgs env as
  , AcquireArg  skip1 signals1 resolvers1 instr1 a'  <- acquireArg env skip2 a
  = AcquireArgs
      (chainSkip skip1 skip2)
      (catMaybes signals1 ++ signals2)
      (catMaybes resolvers1 ++ resolvers2)
      (instr2 . instr1)
      (\skip -> a' skip :>: as' (chainSkip skip skip1))
acquireArgs _ ArgsNil = AcquireArgs SkipNone [] [] id $ const ArgsNil

data AcquireArg kernel fenv fenv1 f where
  -- Captures existential fenv'.
  AcquireArg
    :: Skip fenv' fenv1
    -> [MaybeSignal fenv]
    -> [MaybeSignalResolver fenv]
    -> (BuildSchedule kernel fenv' -> BuildSchedule kernel fenv1)
    -> (forall fenv''. Skip fenv'' fenv' -> SArg fenv'' f)
    -> AcquireArg kernel fenv fenv1 f

acquireArg :: FutureEnv fenv genv -> Skip fenv1 fenv -> SArg genv t -> AcquireArg kernel fenv fenv1 t
acquireArg env skip (SArgScalar var) = case fprj (varIdx var) env of
  Just (FutureScalar _ signal (Left idx)) ->
    AcquireArg
      SkipNone
      [signal]
      []
      id
      (\skip' -> SArgScalar $ Var (varType var) $
        weaken (skipWeakenIdx skip') $ weaken (skipWeakenIdx skip) idx)
  Just (FutureScalar tp signal (Right ref)) ->
    AcquireArg
      (SkipSucc SkipNone)
      [signal]
      []
      (buildRead (GroundRscalar tp) $ weaken (skipWeakenIdx skip) ref)
      (\skip' -> SArgScalar $ Var (varType var) $ weaken (skipWeakenIdx skip') ZeroIdx)
  _ -> variableMissing
acquireArg env skip (SArgBuffer modifier var)
  | Just (FutureBuffer tp idxOrRef read mwrite) <- fprj (varIdx var) env
  , (signals, resolvers) <- bufferSignals modifier read mwrite = case idxOrRef of
    Left idx ->
      AcquireArg
        SkipNone
        signals
        resolvers
        id
        (\skip' -> SArgBuffer modifier $ Var (varType var) $
          weaken (skipWeakenIdx skip') $ weaken (skipWeakenIdx skip) idx)
    Right ref ->
      AcquireArg
        (SkipSucc SkipNone)
        signals
        resolvers
        (buildRead (GroundRbuffer tp) $ weaken (skipWeakenIdx skip) ref)
        (\skip' -> SArgBuffer modifier $ Var (varType var) $ weaken (skipWeakenIdx skip') ZeroIdx)
  | otherwise = variableMissing
  where
    bufferSignals :: Modifier m -> Lock fenv -> Maybe (Lock fenv) -> ([MaybeSignal fenv], [MaybeSignalResolver fenv])
    bufferSignals In (Lock signal resolver) _ = ([signal], [resolver])
    bufferSignals _ (Lock signal resolver) (Just (Lock wsignal wresolver)) = ([signal, wsignal], [resolver, wresolver])
    bufferSignals _ _ _ = internalError "Expected buffer with write permissions"

data AcquireVars kernel fenv t where
  -- Captures existential fenv'.
  AcquireVars
    :: Skip fenv' fenv
    -> (BuildSchedule kernel fenv' -> BuildSchedule kernel fenv)
    -> (forall fenv''. Skip fenv'' fenv' -> ExpVars fenv'' t)
    -> AcquireVars kernel fenv t

acquireVars :: forall kernel fenv genv t. FutureEnv fenv genv -> ExpVars genv t -> AcquireVars kernel fenv t
acquireVars env = go SkipNone
  where
    go :: Skip fenv1 fenv -> ExpVars genv s -> AcquireVars kernel fenv1 s
    go skip (TupRpair vars1 vars2)
      | AcquireVars skip1 instr1 vars1' <- go skip vars1
      , AcquireVars skip2 instr2 vars2' <- go (chainSkip skip1 skip) vars2
      = AcquireVars
          (chainSkip skip2 skip1)
          (instr1 . instr2)
          (\skip' -> vars1' (chainSkip skip' skip2) `TupRpair` vars2' skip')
    go _ TupRunit = AcquireVars SkipNone id (const TupRunit)
    go skip (TupRsingle var) = case fprj (varIdx var) env of
      Just (FutureScalar _ signal (Left idx)) ->
        AcquireVars
          SkipNone
          (buildAwait [weaken (skipWeakenIdx skip) <$> signal])
          (\skip' ->
            TupRsingle $ Var (varType var) $
              weaken (skipWeakenIdx skip') $ weaken (skipWeakenIdx skip) idx
          )
      Just (FutureScalar tp signal (Right ref)) ->
        AcquireVars
          (SkipSucc SkipNone)
          (buildAwait [weaken (skipWeakenIdx skip) <$> signal] .
            buildLet (LeftHandSideSingle $ BaseRground $ GroundRscalar tp) (RefRead $ Var (BaseRref $ GroundRscalar tp) $ weaken (skipWeakenIdx skip) ref))
          (\skip' -> TupRsingle $ Var (varType var) $ weaken (skipWeakenIdx skip') ZeroIdx)
      _ -> variableMissing

data AcquireSome kernel fenv fenv1 genv where
  AcquireSome
    :: Skip fenv' fenv1
    -> [Idx fenv Signal]
    -> [Idx fenv SignalResolver]
    -> (BuildSchedule kernel fenv' -> BuildSchedule kernel fenv1)
    -> (forall fenv''. Skip fenv'' fenv' -> PartialEnv (Idx fenv'') genv)
    -> AcquireSome kernel fenv fenv1 genv

-- Assumes that buffers are only require read access.
acquireSome :: forall kernel fenv genv. FutureEnv fenv genv -> IdxSet genv -> AcquireSome kernel fenv fenv genv
acquireSome = go SkipNone SkipNone
  where
    go :: Skip fenv fenv0 -> Skip fenv1 fenv -> FutureEnv fenv0 genv' -> IdxSet genv' -> AcquireSome kernel fenv fenv1 genv'
    go _ _ _ (IdxSet PEnd) = AcquireSome SkipNone [] [] id (const PEnd)
    go envSkip skip (FEnvFSkip env) indices = go (SkipSucc envSkip) skip env indices
    go envSkip skip env (IdxSet (PNone indices))
      | AcquireSome skip1 signals resolvers instr penv <- go envSkip skip env' (IdxSet indices) =
        AcquireSome skip1 signals resolvers instr (\skip' -> PNone $ penv skip')
      where
        env' = case env of
          FEnvPush e _ -> e
          FEnvGSkip e -> e
          -- FEnvFSkip impossible, already handled in previous case of 'go'.
          _ -> FEnvEnd
    go envSkip skip (FEnvPush env future) (IdxSet (PPush indices _))
      | AcquireSome skip1 signals resolvers instr penv <- go envSkip skip env (IdxSet indices) =
        case future of
          FutureScalar _ signal (Left idx) ->
            AcquireSome
              skip1
              (appendMaybe (weaken (skipWeakenIdx envSkip) <$> signal) signals)
              resolvers
              instr
              (\skip' -> PPush (penv skip') $
                weaken (skipWeakenIdx skip') $ weaken (skipWeakenIdx skip1)
                  $ weaken (skipWeakenIdx skip) $ weaken (skipWeakenIdx envSkip) idx)
          FutureScalar tp signal (Right ref) ->
            AcquireSome
              (chainSkip (SkipSucc SkipNone) skip1)
              (appendMaybe (weaken (skipWeakenIdx envSkip) <$> signal) signals)
              resolvers
              (instr . buildRead (GroundRscalar tp)
                (weaken (skipWeakenIdx skip1)  $ weaken (skipWeakenIdx skip) $ weaken (skipWeakenIdx envSkip) ref))
              (\skip' -> PPush (penv $ SkipSucc skip') $ weaken (skipWeakenIdx skip') ZeroIdx)
          FutureBuffer _ _ _ (Just _) -> internalError "Expected read-only buffer"
          FutureBuffer _ (Left idx) (Lock signal resolver) Nothing ->
            AcquireSome
              skip1
              (appendMaybe (weaken (skipWeakenIdx envSkip) <$> signal) signals)
              (appendMaybe (weaken (skipWeakenIdx envSkip) <$> resolver) resolvers)
              instr
              (\skip' -> PPush (penv skip') $
                weaken (skipWeakenIdx skip') $ weaken (skipWeakenIdx skip1)
                  $ weaken (skipWeakenIdx skip) $ weaken (skipWeakenIdx envSkip) idx)
          FutureBuffer tp (Right ref) (Lock signal resolver) Nothing ->
            AcquireSome
              (chainSkip (SkipSucc SkipNone) skip1)
              (appendMaybe (weaken (skipWeakenIdx envSkip) <$> signal) signals)
              (appendMaybe (weaken (skipWeakenIdx envSkip) <$> resolver) resolvers)
              (instr . buildRead (GroundRbuffer tp)
                (weaken (skipWeakenIdx skip1)  $ weaken (skipWeakenIdx skip) $ weaken (skipWeakenIdx envSkip) ref))
              (\skip' -> PPush (penv $ SkipSucc skip') $ weaken (skipWeakenIdx skip') ZeroIdx)
    go _ _ _ _ = variableMissing

data DeclareOutput kernel fenv t where
  DeclareOutput :: Skip fenv' fenv
                -> BLeftHandSide (Output t) fenv fenv'
                -> (forall fenv''. Skip fenv'' fenv' -> Destinations fenv'' t)
                -> DeclareOutput kernel fenv t

declareOutput :: GroundsR t -> DeclareOutput kernel fenv t
declareOutput (TupRpair t1 t2)
  | DeclareOutput skip1 lhs1 dest1 <- declareOutput t1
  , DeclareOutput skip2 lhs2 dest2 <- declareOutput t2
  = DeclareOutput
      (chainSkip skip2 skip1)
      (LeftHandSidePair lhs1 lhs2)
      (\skip -> dest1 (chainSkip skip skip2) `TupRpair` dest2 skip)
declareOutput (TupRsingle tp)
  | Refl <- inputSingle tp
  = DeclareOutput
      (SkipSucc $ SkipSucc SkipNone)
      (LeftHandSidePair (LeftHandSideSingle $ BaseRsignalResolver) (LeftHandSideSingle $ BaseRrefWrite tp))
      $ \skip -> TupRsingle $ DestinationShared
        (weaken (skipWeakenIdx skip) ZeroIdx)
        (weaken (skipWeakenIdx skip) $ SuccIdx ZeroIdx)
declareOutput TupRunit
  = DeclareOutput
      SkipNone
      (LeftHandSideWildcard TupRunit)
      $ \_ -> TupRunit

data DeclareInput fenv genv genv' t where
  DeclareInput
    :: Skip fenv' fenv
    -> BLeftHandSide (Input t) fenv fenv'
    -> FutureEnv fenv' genv'
    -> DeclareInput fenv genv genv' t

declareInput :: GLeftHandSide t genv genv' -> FutureEnv fenv genv -> DeclareInput fenv genv genv' t
declareInput (LeftHandSidePair lhs1 lhs2) fenv
  | DeclareInput skip1 lhs1' fenv1 <- declareInput lhs1 fenv
  , DeclareInput skip2 lhs2' fenv2 <- declareInput lhs2 fenv1
  = DeclareInput (chainSkip skip2 skip1) (LeftHandSidePair lhs1' lhs2') fenv2
declareInput (LeftHandSideWildcard tp) fenv =
  DeclareInput
    SkipNone
    (LeftHandSideWildcard $ inputR tp)
    fenv
declareInput (LeftHandSideSingle tp) fenv
  | Refl <- inputSingle tp =
    DeclareInput
      (SkipSucc $ SkipSucc SkipNone)
      (LeftHandSideSingle BaseRsignal `LeftHandSidePair` LeftHandSideSingle (BaseRref tp))
      $ FEnvPush (FEnvFSkip $ FEnvFSkip fenv)
      $ case tp of
        GroundRscalar t -> FutureScalar t (Just $ SuccIdx ZeroIdx) (Right ZeroIdx)
        GroundRbuffer t -> FutureBuffer t (Right ZeroIdx) (Move $ Just $ SuccIdx ZeroIdx) Nothing

data AwhileInputOutput kernel fenv genv genv' t where
  AwhileInputOutput
    :: InputOutputR input output
    -- Initial state (& instructions to acquire initial state)
    -> Skip fenv1 fenv
    -> (BuildSchedule kernel fenv1 -> BuildSchedule kernel fenv)
    -> (forall fenv'. Skip fenv' fenv1 -> BaseVars fenv' input)
    -- Info for iteration function (ie the body of the loop)
    -> (forall fenv'. BaseVars fenv' input -> FutureEnv fenv' genv -> FutureEnv fenv' genv')
    -> (forall fenv'. BaseVars fenv' output -> Destinations fenv' t)
    -> AwhileInputOutput kernel fenv genv genv' t

awhileInputOutput
  :: FutureEnv fenv genv0
  -- A signal that is already resolved.
  -> Idx fenv Signal
  -- Left hand side of the iteration function of the while loop.
  -> GLeftHandSide t genv genv'
  -- The uniquenesses of the state of the loop.
  -> Uniquenesses t
  -- The initial values of the loop, in the ground environment.
  -> GroundVars genv0 t
  -> AwhileInputOutput kernel fenv genv genv' t
awhileInputOutput _ _ (LeftHandSideWildcard TupRunit) _ _ =
  AwhileInputOutput InputOutputRunit SkipNone id (const TupRunit) (flip const) (const TupRunit)
awhileInputOutput env resolved (LeftHandSidePair lhs1 lhs2) us (TupRpair vars1 vars2)
  | AwhileInputOutput io1 skip1 instr1 initial1 env1 dest1
    <- awhileInputOutput env resolved lhs1 us1 vars1
  , AwhileInputOutput io2 skip2 instr2 initial2 env2 dest2
    <- awhileInputOutput (fenvFSkipMany skip1 env) (weaken (skipWeakenIdx skip1) resolved) lhs2 us2 vars2 =
  AwhileInputOutput
    (InputOutputRpair io1 io2)
    (chainSkip skip2 skip1)
    (instr1 . instr2)
    (\skip -> initial1 (chainSkip skip skip2) `TupRpair` initial2 skip)
    (\case
      TupRpair v1 v2 -> env2 v2 . env1 v1
      _ -> internalError "Pair impossible")
    (\case
      TupRpair v1 v2 -> dest1 v1 `TupRpair` dest2 v2
      _ -> internalError "Pair impossible")
  where
    (us1, us2) = pairUniqueness us
awhileInputOutput env resolved (LeftHandSideWildcard (TupRpair t1 t2)) us vars =
  awhileInputOutput env resolved (LeftHandSidePair (LeftHandSideWildcard t1) (LeftHandSideWildcard t2)) us vars
-- Unique buffer
awhileInputOutput env resolved (LeftHandSideSingle _) (TupRsingle Unique) (TupRsingle var) = case fprj (varIdx var) env of
  Just (FutureBuffer tp ref (Move readSignal) (Just (Move writeSignal))) ->
    let
      -- Signal for read access and signal for write access
      ioSignals = InputOutputRpair InputOutputRsignal InputOutputRsignal
      io = InputOutputRpair ioSignals (InputOutputRref $ GroundRbuffer tp)

      -- Based on 'ref', fill in the first fields of AwhileInputOutput
      firstFields = case ref of
        Right idx ->
          AwhileInputOutput io SkipNone id
            (\skip -> TupRpair
              (TupRpair
                (TupRsingle $ Var BaseRsignal $ weaken (skipWeakenIdx skip) $ fromMaybe resolved readSignal)
                (TupRsingle $ Var BaseRsignal $ weaken (skipWeakenIdx skip) $ fromMaybe resolved writeSignal)
              )
              (TupRsingle $ Var (BaseRref $ GroundRbuffer tp) $ weaken (skipWeakenIdx skip) idx))
        Left idx ->
          AwhileInputOutput io (SkipSucc $ SkipSucc SkipNone)
            -- Store value in a reference, to ensure uniform representation in the body of the loop.
            (buildLet (lhsRef $ GroundRbuffer tp) (NewRef $ GroundRbuffer tp)
              . buildEffect (RefWrite (Var (BaseRrefWrite $ GroundRbuffer tp) ZeroIdx) $ Var (BaseRground $ GroundRbuffer tp)
                $ weaken (weakenSucc $ weakenSucc weakenId) idx))
            (\skip -> TupRpair
              (TupRpair
                -- Weaken the existing signals by 2
                (TupRsingle $ Var BaseRsignal $ weaken (skipWeakenIdx $ SkipSucc $ SkipSucc skip) $ fromMaybe resolved readSignal)
                (TupRsingle $ Var BaseRsignal $ weaken (skipWeakenIdx $ SkipSucc $ SkipSucc skip) $ fromMaybe resolved writeSignal)
              )
              -- Pass the newly constructed reference
              (TupRsingle $ Var (BaseRref $ GroundRbuffer tp) $ weaken (skipWeakenIdx skip) $ SuccIdx ZeroIdx))
    in
      firstFields
        (\case
          TupRpair (TupRpair (TupRsingle signal1) (TupRsingle signal2)) (TupRsingle ref') ->
            let future = FutureBuffer tp (Right $ varIdx ref') (Move $ Just $ varIdx signal1) $ Just $ Move $ Just $ varIdx signal2
            in (`FEnvPush` future)
          _ -> internalError "Input tuple impossible")
        (\case
          TupRpair (TupRpair (TupRsingle resolver1) (TupRsingle resolver2)) (TupRsingle ref') ->
            TupRsingle $ DestinationUnique (varIdx ref') (varIdx resolver1) (varIdx resolver2)
          _ -> internalError "Output tuple impossible")
  Just (FutureBuffer _ _ _ Nothing) -> internalError "FutureBuffer with write lock expected"
  Just (FutureBuffer _ _ _ _) -> internalError "FutureBuffer with Move locks expected"
  Just (FutureScalar tp _ _) -> bufferImpossible tp
  Nothing -> variableMissing
-- Shared buffer
awhileInputOutput env resolved (LeftHandSideSingle (GroundRbuffer _)) _ (TupRsingle var) = case fprj (varIdx var) env of
  Just (FutureBuffer tp ref (Move readSignal) Nothing) ->
    let
      -- Only a signal for read access
      ioSignals = InputOutputRsignal
      io = InputOutputRpair ioSignals (InputOutputRref $ GroundRbuffer tp)

      -- Based on 'ref', fill in the first fields of AwhileInputOutput
      firstFields = case ref of
        Right idx ->
          AwhileInputOutput io SkipNone id
            (\skip -> TupRpair
              (TupRsingle $ Var BaseRsignal $ weaken (skipWeakenIdx skip) $ fromMaybe resolved readSignal)
              (TupRsingle $ Var (BaseRref $ GroundRbuffer tp) $ weaken (skipWeakenIdx skip) idx))
        Left idx ->
          AwhileInputOutput io (SkipSucc $ SkipSucc SkipNone)
            -- Store value in a reference, to ensure uniform representation in the body of the loop.
            (buildLet (lhsRef $ GroundRbuffer tp) (NewRef $ GroundRbuffer tp)
              . buildEffect (RefWrite (Var (BaseRrefWrite $ GroundRbuffer tp) ZeroIdx) $ Var (BaseRground $ GroundRbuffer tp)
                $ weaken (weakenSucc $ weakenSucc weakenId) idx))
            (\skip -> TupRpair
              -- Weaken the existing signals by 2
              (TupRsingle $ Var BaseRsignal $ weaken (skipWeakenIdx $ SkipSucc $ SkipSucc skip) $ fromMaybe resolved readSignal)  
              -- Pass the newly constructed reference
              (TupRsingle $ Var (BaseRref $ GroundRbuffer tp) $ weaken (skipWeakenIdx skip) $ SuccIdx ZeroIdx))
    in
      firstFields
        (\case
          TupRpair (TupRsingle signal1) (TupRsingle ref') ->
            let future = FutureBuffer tp (Right $ varIdx ref') (Move $ Just $ varIdx signal1) $ Nothing
            in (`FEnvPush` future)
          _ -> internalError "Input tuple impossible")
        (\case
          TupRpair (TupRsingle resolver1) (TupRsingle ref') ->
            TupRsingle $ DestinationShared (varIdx ref') (varIdx resolver1)
          _ -> internalError "Output tuple impossible")
  Just (FutureBuffer _ _ _ Just{}) -> internalError "FutureBuffer without write lock expected"
  Just (FutureBuffer _ _ _ _) -> internalError "FutureBuffer with Move locks expected"
  Just (FutureScalar tp _ _) -> bufferImpossible tp
  Nothing -> variableMissing
-- Scalar
awhileInputOutput env resolved (LeftHandSideSingle (GroundRscalar tp')) _ (TupRsingle var) = case fprj (varIdx var) env of
  Just (FutureScalar tp signal ref) ->
    let
      -- Only a signal to announce that the reference is filled.
      ioSignals = InputOutputRsignal
      io = InputOutputRpair ioSignals (InputOutputRref $ GroundRscalar tp)

      -- Based on 'ref', fill in the first fields of AwhileInputOutput
      firstFields = case ref of
        Right idx ->
          AwhileInputOutput io SkipNone id
            (\skip -> TupRpair
              (TupRsingle $ Var BaseRsignal $ weaken (skipWeakenIdx skip) $ fromMaybe resolved signal)
              (TupRsingle $ Var (BaseRref $ GroundRscalar tp) $ weaken (skipWeakenIdx skip) idx))
        Left idx ->
          AwhileInputOutput io (SkipSucc $ SkipSucc SkipNone)
            -- Store value in a reference, to ensure uniform representation in the body of the loop.
            (buildLet (lhsRef $ GroundRscalar tp) (NewRef $ GroundRscalar tp)
              . buildEffect (RefWrite (Var (BaseRrefWrite $ GroundRscalar tp) ZeroIdx) $ Var (BaseRground $ GroundRscalar tp)
                $ weaken (weakenSucc $ weakenSucc weakenId) idx))
            (\skip -> TupRpair
              -- Weaken the existing signals by 2
              (TupRsingle $ Var BaseRsignal $ weaken (skipWeakenIdx $ SkipSucc $ SkipSucc skip) $ fromMaybe resolved signal)  
              -- Pass the newly constructed reference
              (TupRsingle $ Var (BaseRref $ GroundRscalar tp) $ weaken (skipWeakenIdx skip) $ SuccIdx ZeroIdx))
    in
      firstFields
        (\case
          TupRpair (TupRsingle signal1) (TupRsingle ref') ->
            let future = FutureScalar tp (Just $ varIdx signal1) (Right $ varIdx ref')
            in (`FEnvPush` future)
          _ -> internalError "Input tuple impossible")
        (\case
          TupRpair (TupRsingle resolver1) (TupRsingle ref') ->
            TupRsingle $ DestinationShared (varIdx ref') (varIdx resolver1)
          _ -> internalError "Output tuple impossible")
  Just (FutureBuffer _ _ _ _) -> bufferImpossible tp'
  Nothing -> variableMissing
awhileInputOutput env resolved (LeftHandSideWildcard (TupRsingle tp)) us var
  | AwhileInputOutput io skip instr initial _ dest <- awhileInputOutput env resolved (LeftHandSideSingle tp) us var
  = AwhileInputOutput io skip instr initial (flip const) dest
awhileInputOutput _ _ _ _ _ = internalError "Tuple mismatch"

data MakeAvailable kernel fenv genv' where
  -- Captures existential fenv'
  MakeAvailable
    :: Skip' fenv' fenv
    -> FutureEnv fenv' genv'
    -> (BuildSchedule kernel fenv' -> BuildSchedule kernel fenv)
    -> MakeAvailable kernel fenv genv'

makeAvailable :: GLeftHandSide t genv genv' -> FutureEnv fenv genv' -> MakeAvailable kernel fenv genv'
makeAvailable lhs = go (lhsSkip' lhs) SkipNone
  where
    go :: Skip' genv' genv -> Skip fenv2 fenv1 -> FutureEnv fenv1 genv' -> MakeAvailable kernel fenv2 genv'
    go SkipNone' envSkip env = MakeAvailable SkipNone' (fenvFSkipMany envSkip env) id
    go skip envSkip (FEnvFSkip env) = go skip (SkipSucc envSkip) env
    go _ _ FEnvEnd = MakeAvailable SkipNone' FEnvEnd id
    go (SkipSucc' skip) envSkip (FEnvGSkip env)
      | MakeAvailable s env' instr <- go skip envSkip env
      = MakeAvailable s (FEnvGSkip env') instr
    go (SkipSucc' skip) envSkip (FEnvPush env future)
      | MakeAvailable s env' instr <- go skip envSkip env
      = case future of
          FutureScalar tp signal (Right ref) ->
            MakeAvailable
              (SkipSucc' s)
              (FEnvPush (FEnvFSkip env') $ FutureScalar tp Nothing $ Left ZeroIdx)
              (instr
                . buildAwait [weaken (skipWeakenIdx' s) . weaken (skipWeakenIdx envSkip) <$> signal]
                . buildRead (GroundRscalar tp) (weaken (skipWeakenIdx' s) $ weaken (skipWeakenIdx envSkip) ref))
          FutureBuffer tp (Right ref) (Lock signal resolver) Nothing ->
            MakeAvailable
              (SkipSucc' s)
              (FEnvPush (FEnvFSkip env') $ FutureBuffer tp (Left ZeroIdx)
                (Lock Nothing $ weaken (skipWeakenIdx' $ SkipSucc' s) . weaken (skipWeakenIdx envSkip) <$> resolver)
                Nothing)
              (instr
                . buildAwait [weaken (skipWeakenIdx' s) . weaken (skipWeakenIdx envSkip) <$> signal]
                . buildRead (GroundRbuffer tp) (weaken (skipWeakenIdx' s) $ weaken (skipWeakenIdx envSkip) ref))
          FutureBuffer tp (Right ref) (Lock signal resolver) (Just (Lock wsignal wresolver)) ->
            MakeAvailable
              (SkipSucc' s)
              (FEnvPush (FEnvFSkip env') $ FutureBuffer tp (Left ZeroIdx)
                (Lock Nothing $ weaken (skipWeakenIdx' $ SkipSucc' s) . weaken (skipWeakenIdx envSkip) <$> resolver)
                (Just $ Lock Nothing $ weaken (skipWeakenIdx' $ SkipSucc' s) . weaken (skipWeakenIdx envSkip) <$> wresolver))
              (instr
                . buildAwait (fmap (fmap $ weaken (skipWeakenIdx' s) . weaken (skipWeakenIdx envSkip)) [signal, wsignal])
                . buildRead (GroundRbuffer tp) (weaken (skipWeakenIdx' s) $ weaken (skipWeakenIdx envSkip) ref))
          _ -> MakeAvailable s (FEnvPush env' $ weaken (skipWeakenIdx' s .> skipWeakenIdx envSkip) future) instr

environmentDropLHS :: PartialEnv f env1 -> LeftHandSide s t env env1 -> PartialEnv f env
environmentDropLHS env (LeftHandSideWildcard _) = env
environmentDropLHS env (LeftHandSideSingle _)   = partialEnvTail env
environmentDropLHS env (LeftHandSidePair l1 l2) = environmentDropLHS (environmentDropLHS env l2) l1

appendMaybe :: Maybe a -> [a] -> [a]
appendMaybe = maybe id (:)

variableMissing :: HasCallStack => a
variableMissing = internalError "Variable missing in FutureEnv (and possibly in SyncEnv)"

rnfSchedule' :: IsKernel kernel => UniformSchedule kernel env -> ()
rnfSchedule' Return                        = ()
rnfSchedule' (Alet lhs bnd body)           = rnfLeftHandSide rnfBaseR lhs `seq` rnfBinding bnd `seq` rnfSchedule' body
rnfSchedule' (Effect eff next)             = rnfEffect eff `seq` rnfSchedule' next
rnfSchedule' (Acond c true false next)     = rnfExpVar c `seq` rnfSchedule' true `seq` rnfSchedule' false `seq` rnfSchedule' next
rnfSchedule' (Awhile io body initial next) = rnfInputOutputR io `seq` rnfSchedule body `seq` rnfTupR rnfBaseVar initial `seq` rnfSchedule' next
rnfSchedule' (AwhileSeq io body ini  next) = rnfInputOutputR io `seq` rnfSchedule body `seq` rnfTupR rnfBaseVar ini     `seq` rnfSchedule' next
rnfSchedule' (Spawn a b)                   = rnfSchedule' a `seq` rnfSchedule' b

rnfBinding :: Binding env t -> ()
rnfBinding (Compute e)       = rnfOpenExp e
rnfBinding (NewSignal _)     = ()
rnfBinding (NewRef r)        = rnfGroundR r
rnfBinding (Alloc shr tp sz) = rnfShapeR shr `seq` rnfScalarType tp `seq` rnfTupR rnfExpVar sz
rnfBinding (Use tp n buffer) = buffer `seq` n `seq` rnfScalarType tp
rnfBinding (Unit var)        = rnfExpVar var
rnfBinding (RefRead r)       = rnfBaseVar r

rnfEffect :: IsKernel kernel => Effect kernel env -> ()
rnfEffect (Exec md kernel args)   = rnf' md `seq` rnf' kernel `seq` rnfSArgs args
rnfEffect (SignalAwait signals)   = rnf signals
rnfEffect (SignalResolve signals) = rnf signals
rnfEffect (RefWrite ref value)    = rnfBaseVar ref `seq` rnfBaseVar value

rnfBaseVar :: BaseVar env t -> ()
rnfBaseVar = rnfVar rnfBaseR

rnfSArgs :: SArgs env args -> ()
rnfSArgs ArgsNil = ()
rnfSArgs (arg :>: args) = rnfSArg arg `seq` rnfSArgs args

rnfSArg :: SArg env t -> ()
rnfSArg (SArgScalar var)      = rnfExpVar var
rnfSArg (SArgBuffer mod' var) = mod' `seq` rnfGroundVar var

rnfInputOutputR :: InputOutputR input output -> ()
rnfInputOutputR (InputOutputRpair io1 io2) = rnfInputOutputR io1 `seq` rnfInputOutputR io2
rnfInputOutputR _ = () -- all other options have no information

makeFunSpawnClosed :: UniformScheduleFun kernel env t -> UniformScheduleFun kernel env t
makeFunSpawnClosed = makeFunSpawnClosed' weakenId

makeFunSpawnClosed' :: env :> env' -> UniformScheduleFun kernel env t -> UniformScheduleFun kernel env' t
makeFunSpawnClosed' k (Slam lhs f) 
  | Exists lhs' <- rebuildLHS lhs
  , k' <- sinkWithLHS lhs lhs' k =
    Slam lhs' $ makeFunSpawnClosed' k' f
makeFunSpawnClosed' k (Sbody s) = Sbody $ makeSpawnClosed' k PEnd s

-- Maybe we should make this a core utility, if we need this on more locations
type TypedIdxSet t = PartialEnv ((:~:) t)

makeSpawnClosed' :: env :> env' -> TypedIdxSet Signal env' -> UniformSchedule kernel env -> UniformSchedule kernel env'
makeSpawnClosed' k awaitEnd = \case
  Return -> case toList awaitEnd of
    [] -> Return
    list -> Effect (SignalAwait list) Return
  Alet lhs bnd next
    | Exists lhs' <- rebuildLHS lhs
    , k' <- sinkWithLHS lhs lhs' k ->
      Alet lhs' (weaken k bnd) $ makeSpawnClosed' k' (partialEnvSkipLHS lhs' awaitEnd ) next
  Effect effect next ->
    Effect (weaken' k effect) $ makeSpawnClosed' k awaitEnd next
  Acond var true false next
    | (trueCount, true') <- addSync true
    , (falseCount, false') <- addSync false ->
      bindSignals (trueCount `max` falseCount) $
        \skip signals resolvers ->
          let
            k2 = skipWeakenIdx' skip .> k
            resolvers' = toList resolvers
          in
            Acond
              (weaken k2 var)
              (resolve (drop trueCount resolvers')
                $ true' k2 weakenId (take trueCount resolvers'))
              (resolve (drop falseCount resolvers')
                $ false' k2 weakenId (take falseCount resolvers'))
              (makeSpawnClosed' k2
                (unionPartialEnv const signals $ skipWeakenPartialEnv' skip awaitEnd) next)
    -- Acond (weaken k var) (makeSpawnClosed' k PEnd true) (makeSpawnClosed' k PEnd false) (makeSpawnClosed' k awaitEnd next)
  Awhile io step initial next ->
    Awhile io (makeFunSpawnClosed' k step) (mapTupR (weaken k) initial) $ makeSpawnClosed' k awaitEnd next
  AwhileSeq io step initial next ->
    AwhileSeq io (makeFunSpawnClosed' k step) (mapTupR (weaken k) initial) $ makeSpawnClosed' k awaitEnd next
  Spawn a b
    | (count, a') <- addSync a ->
      -- Bind signals for all spawns in 'a', and this current spawn.
      bindSignals (count + 1) $
        \skip signals resolvers ->
          Spawn
            (a' (skipWeakenIdx' skip .> k) weakenId (toList resolvers))
            (makeSpawnClosed' (skipWeakenIdx' skip .> k)
              (unionPartialEnv const signals $ skipWeakenPartialEnv' skip awaitEnd) b)
  where
    bindSignals
      :: Int
      -> (forall env2. Skip' env2 env1 -> TypedIdxSet Signal env2 -> TypedIdxSet SignalResolver env2 -> UniformSchedule kernel env2)
      -> UniformSchedule kernel env1
    bindSignals 0 f = f SkipNone' PEnd PEnd
    bindSignals n f = bindSignals (n - 1) $ \skip signals resolvers ->
      Alet lhsSignal (NewSignal "Synchronisation to make schedule spawn-closed") $
        f (SkipSucc' $ SkipSucc' skip) (PNone $ PPush signals Refl) (PPush (PNone resolvers) Refl)

    -- Returns the number of spawns and adds synchronisation points to the end of all Spawns.
    addSync
      :: UniformSchedule kernel env
      -> ( Int -- Number of spawns, excluding spawns in the step function of Awhile loops
         -- Function to do the actual transformation
         -- The list of SignalResolvers is either as long as the number of spawns,
         -- or one longer.
         -- If the latter is the case, then the final Return of this term should resolve one of these SignalResolvers.
         -- If the former is the case, then no such SignalResolver should be resolved at the end;
         -- the SignalResolvers are then only needed for any spawned terms.
         , forall env1 env2. env :> env1 -> env2 :> env1 -> [Idx env2 SignalResolver] -> UniformSchedule kernel env1)
    addSync Return =
      ( 0
      , \_ k2 -> \case
          [] -> Return
          [s] -> Effect (SignalResolve [weaken k2 s]) Return
          _ -> internalError "makeSpawnClosed: number of Signals is incorrect."
      )
    addSync (Alet lhs bnd next) =
      ( count
      , \k1 k2 resolvers -> if
        | Exists lhs' <- rebuildLHS lhs
        , k1' <- sinkWithLHS lhs lhs' k1
        , k2' <- weakenWithLHS lhs' .> k2 ->
          Alet lhs' (weaken k1 bnd) $ next' k1' k2' resolvers
      )
      where
        (count, next') = addSync next
    addSync (Effect effect next) =
      ( count
      , \k1 k2 resolvers ->
        Effect (weaken' k1 effect) $ next' k1 k2 resolvers
      )
      where
        (count, next') = addSync next
    addSync (Acond var true false next) =
      -- Since only 'true' or 'false' is executed, not both,
      -- we take the maximum of both counts
      ( (trueCount `max` falseCount) + nextCount
      , \k1 k2 resolvers ->
        let
          (branchResolvers, nextResolvers) = splitAt (trueCount `max` falseCount) resolvers
        in
          Acond (weaken k1 var)
            -- If the true branch requires fewer signals than the false branch,
            -- resolve all the extra signals here.
            ( resolve (map (weaken k2) $ drop trueCount branchResolvers)
              $ true' k1 k2 (take trueCount branchResolvers)
            )
            -- If the false branch requires fewer signals than the true branch,
            -- resolve all the extra signals here.
            ( resolve (map (weaken k2) $ drop falseCount branchResolvers)
              $ false' k1 k2 (take falseCount branchResolvers)
            )
            ( next' k1 k2 nextResolvers )
      )
      where
        (trueCount, true') = addSync true
        (falseCount, false') = addSync false
        (nextCount, next') = addSync next
    addSync (Awhile io f initial next) =
      ( count
      , \k1 k2 resolvers ->
          Awhile
            io
            (makeFunSpawnClosed' k1 f)
            (mapTupR (weaken k1) initial)
            $ next' k1 k2 resolvers
      )
      where
        (count, next') = addSync next
    addSync (AwhileSeq io f initial next) =
      ( count
      , \k1 k2 resolvers ->
          AwhileSeq
            io
            (makeFunSpawnClosed' k1 f)
            (mapTupR (weaken k1) initial)
            $ next' k1 k2 resolvers
      )
      where
        (count, next') = addSync next
    addSync (Spawn a b) =
      -- +1 for this Spawn
      ( aCount + bCount + 1
      , \k1 k2 resolvers ->
        Spawn
          -- Give the first (aCount + 1) resolvers to term 'a', the others to 'b'.
          -- Note that 'b' gets either bCount or (bCount + 1) resolvers,
          -- see the comment at the start of 'addSync'.
          (a' k1 k2 (take (aCount + 1) resolvers))
          (b' k1 k2 (drop (aCount + 1) resolvers))
      )
      where
        (aCount, a') = addSync a
        (bCount, b') = addSync b

    toList :: TypedIdxSet t env -> [Idx env t]
    toList = map (\(EnvBinding idx Refl) -> idx) . partialEnvToList
