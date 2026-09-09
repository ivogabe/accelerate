{-# LANGUAGE FlexibleContexts     #-}
-- |
-- Module      : Data.Array.Accelerate.Trafo.NewNewFusion
-- Copyright   : [2012..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--
-- This module should implement fusion.
--

module Data.Array.Accelerate.Trafo.NewNewFusion (

  convertAfun, convertAfunWith,

  Benchmarking(..)

) where

import Data.Array.Accelerate.AST.Operation
import Data.Array.Accelerate.AST.Partitioned
import Data.Array.Accelerate.Trafo.Config
import Data.Array.Accelerate.Error
import Data.Array.Accelerate.Trafo.Operation.Simplify
import Data.Array.Accelerate.Trafo.Partitioning.ILP
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Graph (MakesILP)
import qualified Data.Array.Accelerate.Pretty.Operation as Pretty
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Solve (Objective (..))






-- Array Fusion
-- ============

defaultSolver :: Solver
defaultSolver =
  MIPSolver CBC

-- | Apply the fusion transformation to a function of array arguments
--
convertAfun :: (HasCallStack, MakesILP op, SimplifyOperation op, Pretty.PrettyOp (Cluster op)) => FusionType -> OperationAfun op () f -> PartitionedAfun op () f
convertAfun = convertAfunWith defaultOptions

convertAfunWith :: (HasCallStack, MakesILP op, SimplifyOperation op, Pretty.PrettyOp (Cluster op)) => Config -> FusionType -> OperationAfun op () f -> PartitionedAfun op () f
convertAfunWith _ (Fusion o)       = withSimplStats (ilpFusionF'' defaultSolver o)
convertAfunWith _ (Benchmarking b) = withSimplStats (benchF b FusedEdges)


withSimplStats :: a -> a
-- #ifdef ACCELERATE_DEBUG
-- withSimplStats x = unsafePerformIO Stats.resetSimplCount `seq` x
-- #else
withSimplStats x = x
-- #endif

-- dontFuse :: op args -> Args env args -> Cluster' op args
-- dontFuse = unfused
