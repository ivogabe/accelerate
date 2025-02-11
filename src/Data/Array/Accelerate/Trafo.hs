{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE CPP                 #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# OPTIONS_HADDOCK hide #-}
-- |
-- Module      : Data.Array.Accelerate.Trafo
-- Copyright   : [2012..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.Trafo (

  -- * HOAS -> de Bruijn conversion
  -- ** Array computations
  convertAcc, convertAccWith,

  -- ** Array functions
  Afunction, ArraysFunctionR,
  convertAfun, convertAfunWith,

  -- ** Sequence computations
  -- convertSeq, convertSeqWith,

  -- ** Scalar expressions
  Function, EltFunctionR,
  convertExp, convertFun,

  test, testWithObjective, testBench, convertAccWithObj, convertAfunWithObj, convertAccBench, convertAfunBench,
) where

import Data.Array.Accelerate.Sugar.Array                  ( ArraysR )
import Data.Array.Accelerate.Sugar.Elt                    ( EltR )
import Data.Array.Accelerate.Smart
import Data.Array.Accelerate.Trafo.Config
-- import Data.Array.Accelerate.Trafo.Delayed
import Data.Array.Accelerate.Trafo.Sharing                ( Afunction, ArraysFunctionR, Function, EltFunctionR )
import qualified Data.Array.Accelerate.AST                as AST
import Data.Array.Accelerate.AST.Kernel
import Data.Array.Accelerate.AST.Schedule
import qualified Data.Array.Accelerate.AST.Partitioned    as Partitioned
-- import qualified Data.Array.Accelerate.Trafo.Fusion       as Fusion
import qualified Data.Array.Accelerate.Trafo.LetSplit     as LetSplit
import qualified Data.Array.Accelerate.Trafo.Exp.Simplify as Rewrite
import qualified Data.Array.Accelerate.Trafo.Sharing      as Sharing
import qualified Data.Array.Accelerate.Trafo.Operation.LiveVars as Operation
import qualified Data.Array.Accelerate.Trafo.Operation.Simplify as Operation
-- import qualified Data.Array.Accelerate.Trafo.Vectorise    as Vectorise

import Control.DeepSeq
import qualified Data.Array.Accelerate.Trafo.Partitioning.ILP.Graph as Partitioning
import Data.Array.Accelerate.Representation.Ground (DesugaredArrays, DesugaredAfun)
import Data.Array.Accelerate.Trafo.Desugar (DesugarAcc, desugar, desugarAfun)
import qualified Data.Array.Accelerate.Trafo.NewNewFusion as NewNewFusion
import Prettyprinter                                      as Pretty
import qualified Data.Array.Accelerate.Pretty             as Pretty
import qualified Data.Array.Accelerate.Pretty.Operation   as Pretty
import qualified Data.Array.Accelerate.Pretty.Schedule    as Pretty
import Data.Array.Accelerate.Pretty (prettyOpenAcc)
import Data.Array.Accelerate.Pretty.Partitioned ()
import Data.String (fromString)
import Data.Char (toUpper)
import qualified Data.Array.Accelerate.AST.Operation as Operation
import qualified Data.Array.Accelerate.Trafo.Partitioning.ILP.Graph as Graph
import Data.Array.Accelerate.Pretty.Print (configPlain, Val (Empty))

import Data.Array.Accelerate.Trafo.Partitioning.ILP.Solve (Objective(..))
import Data.Array.Accelerate.Trafo.NewNewFusion (Benchmarking)
import Data.Array.Accelerate.Trafo.Partitioning.ILP (FusionType(..), defaultObjective)
import Control.Monad.Trans.Writer (runWriter, Writer, writer)
import Control.Monad ((>=>))
import Data.Array.Accelerate.Pretty.Exp (context0)

-- TODO: so much duplication here, and I keep worrying that there are differences hiding in one of them.
-- need to abstract a bit!

test
  :: forall sched kernel f. (Afunction f, DesugarAcc (KernelOperation kernel), Operation.SimplifyOperation (KernelOperation kernel), Operation.SLVOperation (KernelOperation kernel), Partitioning.MakesILP (KernelOperation kernel), Partitioned.SetOpIndices (KernelOperation kernel), Pretty.PrettyOp (KernelOperation kernel), Pretty.PrettyKernel kernel, IsSchedule sched, IsKernel kernel, Pretty.PrettySchedule sched, Operation.ShrinkArg (Partitioning.BackendClusterArg (KernelOperation kernel)), Operation.NFData' (Graph.BackendClusterArg (KernelOperation kernel)),  Operation.ShrinkArg (Partitioning.BackendClusterArg (KernelOperation kernel)))
  => f
  -> String
test = snd . convertAfunFullOptions @sched @kernel defaultOptions defaultObjective Pretty.renderForTerminal

-- TODO: simplifications commented out, because they REMOVE PERMUTE
testWithObjective
  :: forall sched kernel f. (Afunction f, DesugarAcc (KernelOperation kernel), Operation.SimplifyOperation (KernelOperation kernel), Operation.SLVOperation (KernelOperation kernel), Partitioning.MakesILP (KernelOperation kernel), Partitioned.SetOpIndices (KernelOperation kernel), Pretty.PrettyOp (KernelOperation kernel), Pretty.PrettyKernel kernel, IsSchedule sched, IsKernel kernel, Pretty.PrettySchedule sched, Operation.ShrinkArg (Partitioning.BackendClusterArg (KernelOperation kernel)), Operation.NFData' (Graph.BackendClusterArg (KernelOperation kernel)),  Operation.ShrinkArg (Partitioning.BackendClusterArg (KernelOperation kernel)))
  => Objective
  -> f
  -> String
testWithObjective obj = snd . convertAfunFullOptions @sched @kernel defaultOptions (Fusion obj) Pretty.renderForTerminal


testBench
  :: forall sched kernel f. (Afunction f, DesugarAcc (KernelOperation kernel), Operation.SimplifyOperation (KernelOperation kernel), Operation.SLVOperation (KernelOperation kernel), Partitioning.MakesILP (KernelOperation kernel), Partitioned.SetOpIndices (KernelOperation kernel), Pretty.PrettyOp (KernelOperation kernel), Pretty.PrettyKernel kernel, IsSchedule sched, IsKernel kernel, Pretty.PrettySchedule sched, Operation.ShrinkArg (Partitioning.BackendClusterArg (KernelOperation kernel)), Operation.NFData' (Graph.BackendClusterArg (KernelOperation kernel)),  Operation.ShrinkArg (Partitioning.BackendClusterArg (KernelOperation kernel)))
  => Benchmarking
  -> f
  -> String
testBench bench = snd . convertAfunFullOptions @sched @kernel defaultOptions (Benchmarking bench) Pretty.renderForTerminal




-- HOAS -> de Bruijn conversion
-- ----------------------------

-- | Convert a closed array expression to de Bruijn form while also
--   incorporating sharing observation and array fusion.
--
convertAcc
  :: forall sched kernel arrs.
     (DesugarAcc (KernelOperation kernel), Operation.SLVOperation (KernelOperation kernel), Operation.SimplifyOperation (KernelOperation kernel), Partitioning.MakesILP (KernelOperation kernel), Partitioned.SetOpIndices (KernelOperation kernel), Pretty.PrettyOp (KernelOperation kernel), IsSchedule sched, IsKernel kernel, Operation.NFData' (Graph.BackendClusterArg (KernelOperation kernel)),  Operation.ShrinkArg (Partitioning.BackendClusterArg (KernelOperation kernel)), Pretty.PrettySchedule sched, Pretty.PrettyKernel kernel)
  => Acc arrs
  -> sched kernel () (ScheduleOutput sched (DesugaredArrays (ArraysR arrs)) -> ())
convertAcc = convertAccWith defaultOptions

convertAccWith
  :: forall sched kernel arrs.
     (DesugarAcc (KernelOperation kernel), Operation.SLVOperation (KernelOperation kernel), Operation.SimplifyOperation (KernelOperation kernel), Partitioning.MakesILP (KernelOperation kernel), Partitioned.SetOpIndices (KernelOperation kernel), Pretty.PrettyOp (KernelOperation kernel), IsSchedule sched, IsKernel kernel, Operation.NFData' (Graph.BackendClusterArg (KernelOperation kernel)),  Operation.ShrinkArg (Partitioning.BackendClusterArg (KernelOperation kernel)), Pretty.PrettySchedule sched, Pretty.PrettyKernel kernel)
  => Config
  -> Acc arrs
  -> sched kernel () (ScheduleOutput sched (DesugaredArrays (ArraysR arrs)) -> ())
convertAccWith config = fst . convertAccFullOptions config defaultObjective (const ())

convertAccBench
  :: forall sched kernel arrs.
     (Pretty.PrettySchedule sched, Pretty.PrettyKernel kernel, DesugarAcc (KernelOperation kernel), Operation.SLVOperation (KernelOperation kernel), Operation.SimplifyOperation (KernelOperation kernel), Partitioning.MakesILP (KernelOperation kernel), Partitioned.SetOpIndices (KernelOperation kernel), Pretty.PrettyOp (KernelOperation kernel), IsSchedule sched, IsKernel kernel, Operation.NFData' (Graph.BackendClusterArg (KernelOperation kernel)),  Operation.ShrinkArg (Partitioning.BackendClusterArg (KernelOperation kernel)))
  => NewNewFusion.Benchmarking
  -> Acc arrs
  -> sched kernel () (ScheduleOutput sched (DesugaredArrays (ArraysR arrs)) -> ())
convertAccBench b = fst . convertAccFullOptions defaultOptions (Benchmarking b) (const ())

convertAfunBench
  :: forall sched kernel f.
     (Pretty.PrettySchedule sched, Pretty.PrettyKernel kernel, Afunction f, DesugarAcc (KernelOperation kernel), Operation.SLVOperation (KernelOperation kernel), Operation.SimplifyOperation (KernelOperation kernel), Partitioning.MakesILP (KernelOperation kernel), Partitioned.SetOpIndices (KernelOperation kernel), Pretty.PrettyOp (KernelOperation kernel), IsSchedule sched, IsKernel kernel, Operation.NFData' (Graph.BackendClusterArg (KernelOperation kernel)),  Operation.ShrinkArg (Partitioning.BackendClusterArg (KernelOperation kernel)))
  => NewNewFusion.Benchmarking
  -> f
  -> sched kernel () (Scheduled sched (DesugaredAfun (ArraysFunctionR f)))
convertAfunBench b = fst . convertAfunFullOptions defaultOptions (Benchmarking b) (const ())


convertAccWithObj
  :: forall sched kernel arrs.
     (DesugarAcc (KernelOperation kernel), Operation.SLVOperation (KernelOperation kernel), Operation.SimplifyOperation (KernelOperation kernel), Partitioning.MakesILP (KernelOperation kernel), Partitioned.SetOpIndices (KernelOperation kernel), Pretty.PrettyOp (KernelOperation kernel), IsSchedule sched, IsKernel kernel, Operation.NFData' (Graph.BackendClusterArg (KernelOperation kernel)),  Operation.ShrinkArg (Partitioning.BackendClusterArg (KernelOperation kernel)), Pretty.PrettySchedule sched, Pretty.PrettyKernel kernel)
  => Objective
  -> Acc arrs
  -> sched kernel () (ScheduleOutput sched (DesugaredArrays (ArraysR arrs)) -> ())
convertAccWithObj obj = fst . convertAccFullOptions defaultOptions (Fusion obj) (const ())


-- | Convert a unary function over array computations, incorporating sharing
--   observation and array fusion
--
convertAfun
  :: forall sched kernel f.
     (Pretty.PrettyKernel kernel, Pretty.PrettySchedule sched, Afunction f, DesugarAcc (KernelOperation kernel), Operation.SLVOperation (KernelOperation kernel), Operation.SimplifyOperation (KernelOperation kernel), Partitioned.SetOpIndices (KernelOperation kernel), Partitioning.MakesILP (KernelOperation kernel), Pretty.PrettyOp (KernelOperation kernel), IsSchedule sched, IsKernel kernel, Operation.NFData' (Graph.BackendClusterArg (KernelOperation kernel)),  Operation.ShrinkArg (Partitioning.BackendClusterArg (KernelOperation kernel)))
  => f
  -> sched kernel () (Scheduled sched (DesugaredAfun (ArraysFunctionR f)))
convertAfun = convertAfunWith defaultOptions

convertAfunWith
  :: forall sched kernel f.
     (Pretty.PrettyKernel kernel, Pretty.PrettySchedule sched, Afunction f, DesugarAcc (KernelOperation kernel), Operation.SLVOperation (KernelOperation kernel), Operation.SimplifyOperation (KernelOperation kernel), Partitioned.SetOpIndices (KernelOperation kernel), Partitioning.MakesILP (KernelOperation kernel), Pretty.PrettyOp (KernelOperation kernel), IsSchedule sched, IsKernel kernel, Operation.NFData' (Graph.BackendClusterArg (KernelOperation kernel)),  Operation.ShrinkArg (Partitioning.BackendClusterArg (KernelOperation kernel)))
  => Config
  -> f
  -> sched kernel () (Scheduled sched (DesugaredAfun (ArraysFunctionR f)))
convertAfunWith config = fst . convertAfunFullOptions config defaultObjective (const ())

convertAfunWithObj
  :: forall sched kernel f.
     (Afunction f, DesugarAcc (KernelOperation kernel), Operation.SLVOperation (KernelOperation kernel), Operation.SimplifyOperation (KernelOperation kernel), Partitioning.MakesILP (KernelOperation kernel), Partitioned.SetOpIndices (KernelOperation kernel), Pretty.PrettyOp (KernelOperation kernel), IsSchedule sched, IsKernel kernel, Operation.NFData' (Graph.BackendClusterArg (KernelOperation kernel)),  Operation.ShrinkArg (Partitioning.BackendClusterArg (KernelOperation kernel)), Pretty.PrettySchedule sched, Pretty.PrettyKernel kernel)
  => Objective
  -> f
  -> sched kernel () (Scheduled sched (DesugaredAfun (ArraysFunctionR f)))
convertAfunWithObj obj = fst . convertAfunFullOptions defaultOptions (Fusion obj) (const ())


convertAccFullOptions
  :: forall sched kernel arrs m.
     (Monoid m, DesugarAcc (KernelOperation kernel), Operation.SLVOperation (KernelOperation kernel), Operation.SimplifyOperation (KernelOperation kernel), Partitioning.MakesILP (KernelOperation kernel), Partitioned.SetOpIndices (KernelOperation kernel), Pretty.PrettyOp (KernelOperation kernel), IsSchedule sched, IsKernel kernel, Operation.NFData' (Graph.BackendClusterArg (KernelOperation kernel)),  Operation.ShrinkArg (Partitioning.BackendClusterArg (KernelOperation kernel)), Pretty.PrettySchedule sched, Pretty.PrettyKernel kernel)
  => Config -> FusionType -> (Pretty.Adoc -> m)
  -> Acc arrs -> (sched kernel () (ScheduleOutput sched (DesugaredArrays (ArraysR arrs)) -> ()), m)
convertAccFullOptions config ft pprint acc = runWriter $
  (   phase'' "sharing-recovery"    (Sharing.convertAccWith config)                              (Pretty.prettyPreOpenAcc configPlain context0 prettyOpenAcc AST.runOpenAcc Empty . AST.runOpenAcc)
  >=> phase'' "array-split-lets"    LetSplit.convertAcc                                          (Pretty.prettyPreOpenAcc configPlain context0 prettyOpenAcc AST.runOpenAcc Empty . AST.runOpenAcc)
  >=> phase'' "desugar"             (Operation.simplify . desugar)                                Pretty.prettyAcc
  >=> phase'' "operation-live-vars" (Operation.simplify . Operation.stronglyLiveVariables)        Pretty.prettyAcc
  >=> phase'' "array-fusion"        (Operation.simplify . NewNewFusion.convertAccWith config ft)  Pretty.prettyAcc
  >=> phase'' "partition-live-vars" (Operation.simplify . Operation.stronglyLiveVariables)        Pretty.prettyAcc
  >=> (\x -> let y = phase' "codegen" rnfSchedule convertSchedule x in writer (y, pprint $ vsep ["CODEGEN", Pretty.prettySchedule y]))
  ) acc
  where
    phase'' :: NFData b => String -> (a -> b) -> (b -> Pretty.Adoc) -> a -> Writer m b
    phase'' name f pp a = let b = phase name f a in writer (b, pprint $ Pretty.vsep [fromString $ map toUpper name, pp b, mempty, mempty])

convertAfunFullOptions
  :: forall sched kernel f m.
     (Monoid m, Afunction f, DesugarAcc (KernelOperation kernel), Operation.SimplifyOperation (KernelOperation kernel), Operation.SLVOperation (KernelOperation kernel), Partitioning.MakesILP (KernelOperation kernel), Partitioned.SetOpIndices (KernelOperation kernel), Pretty.PrettyOp (KernelOperation kernel), Pretty.PrettyKernel kernel, IsSchedule sched, IsKernel kernel, Pretty.PrettySchedule sched, Operation.ShrinkArg (Partitioning.BackendClusterArg (KernelOperation kernel)), Operation.NFData' (Graph.BackendClusterArg (KernelOperation kernel)),  Operation.ShrinkArg (Partitioning.BackendClusterArg (KernelOperation kernel)))
  => Config -> FusionType -> (Pretty.Adoc -> m)
  -> f -> (sched kernel () (Scheduled sched (DesugaredAfun (ArraysFunctionR f))), m)
convertAfunFullOptions config ft pprint f = runWriter $
  (   phase'' "sharing-recovery"    (Sharing.convertAfunWith config)                                (Pretty.prettyPreOpenAfun configPlain prettyOpenAcc Empty)
  >=> phase'' "array-split-lets"    LetSplit.convertAfun                                            (Pretty.prettyPreOpenAfun configPlain prettyOpenAcc Empty)
  >=> phase'' "desugar"             (Operation.simplifyFun . desugarAfun)                            Pretty.prettyAfun
  >=> phase'' "operation-live-vars" (Operation.simplifyFun . Operation.stronglyLiveVariablesFun)     Pretty.prettyAfun
  >=> phase'' "array-fusion"        (Operation.simplifyFun . NewNewFusion.convertAfunWith config ft) Pretty.prettyAfun
  >=> phase'' "partition-live-vars" (Operation.simplifyFun . Operation.stronglyLiveVariablesFun)     Pretty.prettyAfun
  >=> (\x -> let y = phase' "codegen" rnfSchedule convertScheduleFun x in writer (y, pprint $ vsep ["CODEGEN", Pretty.prettySchedule y]))
  ) f
  where
    phase'' :: NFData b => String -> (a -> b) -> (b -> Pretty.Adoc) -> a -> Writer m b
    phase'' name g pp a = let b = phase name g a in writer (b, pprint $ Pretty.vsep [fromString $ map toUpper name, pp b, mempty, mempty])



-- | Convert a closed scalar expression, incorporating sharing observation and
--   optimisation.
--
convertExp :: Exp e -> AST.Exp () (EltR e)
convertExp
  = phase "exp-simplify"     Rewrite.simplifyExp
  . phase "sharing-recovery" Sharing.convertExp


-- | Convert closed scalar functions, incorporating sharing observation and
--   optimisation.
--
convertFun :: Function f => f -> AST.Fun () (EltFunctionR f)
convertFun
  = phase "exp-simplify"     Rewrite.simplifyFun
  . phase "sharing-recovery" Sharing.convertFun


-- Debugging
-- ---------

-- Execute a phase of the compiler and (possibly) print some timing/gc
-- statistics.
--
phase :: NFData b => String -> (a -> b) -> a -> b
phase n = phase' n rnf

-- Execute a phase of the compiler and (possibly) print some timing/gc
-- statistics.
--
phase' :: String -> (b -> ()) -> (a -> b) -> a -> b
#ifdef ACCELERATE_DEBUG
phase' n rnf'' f x = unsafePerformIO $ do
  enabled <- getFlag dump_phases
  if enabled
    then timed dump_phases (now ("phase " <> fromString n <> ": ") % elapsed) (let y = f x in rnf'' y `seq` return y)
    else return (f x)
#else
phase' _ _ f = f
#endif
