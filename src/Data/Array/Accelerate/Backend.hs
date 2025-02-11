{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE PatternGuards       #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE TypeOperators       #-}

-- |
-- Module      : Data.Array.Accelerate.Backend
-- Copyright   : [2012..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--
-- This module defines the interface for kernels, to be implemented
-- in other modules.
--

module Data.Array.Accelerate.Backend (
  Backend(..),
  run, runWith,
  run1, run1With,
  runN, runNWith,

  -- Type classes that a backend should implement:
  Desugar.DesugarAcc(..),

  Operation.SLVOperation(..),
  Operation.SubArgs(..), Operation.SubArg(..),
  Operation.defaultSlvGenerate, Operation.defaultSlvMap, Operation.defaultSlvBackpermute,
  Operation.EncodeOperation(..), Operation.hashOperation,

  Operation.SimplifyOperation(..),
  Operation.CopyOperation(..),
  Operation.detectMapCopies, Operation.detectBackpermuteCopies, Operation.copyOperationsForArray,

  Pretty.PrettyKernel(..), Pretty.PrettyKernelStyle(..),

  Partitioning.MakesILP(..),
  IsSchedule(..),
  IsKernel(..),
  Pretty.PrettyOp(..),
  Execute(..),
  Operation.NFData'(..),
  Operation.ShrinkArg(..), runWithObj, runNWithObj, runNBench, Benchmarking
) where

import qualified Data.Array.Accelerate.Smart as Smart
import Data.Array.Accelerate.AST.Schedule
import Data.Array.Accelerate.AST.Kernel
import Data.Array.Accelerate.AST.Execute
import qualified Data.Array.Accelerate.AST.Partitioned as Partitioned
import qualified Data.Array.Accelerate.Sugar.Array as Sugar
import Data.Array.Accelerate.Representation.Array
import Data.Array.Accelerate.Representation.Ground
import Data.Array.Accelerate.Trafo
import Data.Array.Accelerate.Trafo.Config
import qualified Data.Array.Accelerate.Trafo.Operation.LiveVars as Operation
import qualified Data.Array.Accelerate.Trafo.Operation.Simplify as Operation
import qualified Data.Array.Accelerate.Analysis.Hash.Operation  as Operation

import Data.Array.Accelerate.Trafo.Sharing (Afunction(..), AfunctionRepr(..), afunctionGroundR, afunctionRepr)
import qualified Data.Array.Accelerate.Trafo.Desugar as Desugar
import qualified Data.Array.Accelerate.Trafo.Partitioning.ILP.Graph as Partitioning
import qualified Data.Array.Accelerate.Pretty.Operation as Pretty
import qualified Data.Array.Accelerate.Pretty.Schedule as Pretty
import Data.Kind
import Data.Type.Equality
import System.IO.Unsafe (unsafePerformIO)
import qualified Data.Array.Accelerate.AST.Operation as Operation
import qualified Data.Array.Accelerate.Trafo.Partitioning.ILP.Graph as Graph
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Solve (Objective)
import Data.Array.Accelerate.Trafo.Partitioning.ILP (Benchmarking)


class
  ( Desugar.DesugarAcc (Operation backend)
  , Operation.SLVOperation (Operation backend)
  , Operation.SimplifyOperation (Operation backend)
  , Partitioning.MakesILP (Operation backend)
  , Partitioned.SetOpIndices (Operation backend)
  , IsSchedule (Schedule backend)
  , IsKernel (Kernel backend)
  , Pretty.PrettyOp (Operation backend)
  , Pretty.PrettyKernel (Kernel backend)
  , Pretty.PrettySchedule (Schedule backend)
  , Execute (Schedule backend) (Kernel backend)
  , Operation.NFData' (Graph.BackendClusterArg (KernelOperation (Kernel backend)))
  , Operation.ShrinkArg (Partitioning.BackendClusterArg (KernelOperation (Kernel backend)))
  , Operation.EncodeOperation (Operation backend)
  ) => Backend backend where

  type Schedule backend :: (Type -> Type) -> Type -> Type -> Type
  type Kernel backend :: Type -> Type

type Operation backend = KernelOperation (Kernel backend)

-- Backend can be chosen with an explicit type application, for instance:
--   run @Interpreter acc
run :: forall backend t. (Sugar.Arrays t, Backend backend) => Smart.Acc t -> t
run = runWith @backend defaultOptions

runWith :: forall backend t. (Sugar.Arrays t, Backend backend) => Config -> Smart.Acc t -> t
runWith config acc
  = Sugar.toArr $ sugarArrays repr $ unsafePerformIO $ executeAcc (desugarArraysR repr) program
  where
    repr = Sugar.arraysR @t
    schedule = convertAccWith @(Schedule backend) @(Kernel backend) config acc
    program = linkAfunSchedule schedule

runWithObj :: forall backend t. (Sugar.Arrays t, Backend backend) => Objective -> Smart.Acc t -> t
runWithObj obj acc = Sugar.toArr $ sugarArrays repr $ unsafePerformIO $ executeAcc (desugarArraysR repr) program
  where
    repr = Sugar.arraysR @t
    schedule = convertAccWithObj @(Schedule backend) @(Kernel backend) obj acc
    program = linkAfunSchedule schedule

run1
  :: forall backend s t.
     (Sugar.Arrays s, Sugar.Arrays t, Backend backend)
  => (Smart.Acc s -> Smart.Acc t)
  -> s -> t
run1 = runN @backend

run1With
  :: forall backend s t.
     (Sugar.Arrays s, Sugar.Arrays t, Backend backend)
  => Config
  -> (Smart.Acc s -> Smart.Acc t)
  -> s -> t
run1With = runNWith @backend

runN
  :: forall backend f.
     (Afunction f, Backend backend)
  => f
  -> AfunctionR f
runN = runNWith @backend defaultOptions

runNWith
  :: forall backend f.
     (Afunction f, Backend backend)
  => Config
  -> f
  -> AfunctionR f
runNWith config f = program `seq` sugarFunction (afunctionRepr @f) $ executeAfun (afunctionGroundR @f) program
  where
    schedule = convertAfunWith @(Schedule backend) @(Kernel backend) config f
    program = linkAfunSchedule schedule

runNWithObj
  :: forall backend f.
     (Afunction f, Backend backend)
  => Objective
  -> f
  -> AfunctionR f
runNWithObj obj f = program `seq` sugarFunction (afunctionRepr @f) $ executeAfun (afunctionGroundR @f) program
  where
    schedule = convertAfunWithObj @(Schedule backend) @(Kernel backend) obj f
    program = linkAfunSchedule schedule

runNBench
  :: forall backend f.
     (Afunction f, Backend backend)
  => Benchmarking
  -> f
  -> AfunctionR f
runNBench b f = program `seq` sugarFunction (afunctionRepr @f) $ executeAfun (afunctionGroundR @f) program
  where
    schedule = convertAfunBench @(Schedule backend) @(Kernel backend) b f
    program = linkAfunSchedule schedule

sugarFunction
  :: forall f.
     AfunctionRepr f (AfunctionR f) (ArraysFunctionR f)
  -> IOFun (DesugaredAfun (ArraysFunctionR f))
  -> AfunctionR f
sugarFunction AfunctionReprBody a
  | Refl <- desugaredAfunIsBody repr
  , Refl <- reprIsBody (desugarArraysR repr) = Sugar.toArr $ sugarArrays repr $ unsafePerformIO a
  where
    repr = Sugar.arraysR @(AfunctionR f)
sugarFunction (AfunctionReprLam r) f = sugarFunction r . f . desugarArrays repr . Sugar.fromArr
  where
    repr :: forall a b. f ~ (Smart.Acc a -> b) => ArraysR (Sugar.ArraysR a)
    repr = Sugar.arraysR @a
