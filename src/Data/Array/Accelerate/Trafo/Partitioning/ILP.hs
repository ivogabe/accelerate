{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
module Data.Array.Accelerate.Trafo.Partitioning.ILP where

import Data.Array.Accelerate.Trafo.Partitioning.ILP.Limp
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Graph
    ( MakesILP, Information(Info), makeFullGraph ) 
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Solve
    ( interpretSolution, makeILP ) 
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Clustering 
    ( reconstruct )
import Data.Array.Accelerate.AST.Partitioned
    ( OperationAcc, PartitionedAcc )
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Solver
    ( ILPSolver(solve) )

import System.IO.Unsafe (unsafePerformIO)
import Data.Maybe (fromJust)

limpFusion :: MakesILP op => OperationAcc op () a -> PartitionedAcc op () a
limpFusion = ilpfusion @LIMP

ilpfusion :: forall ilp op a. (MakesILP op, ILPSolver ilp op) => OperationAcc op () a -> PartitionedAcc op () a
ilpfusion acc = fusedAcc
  where
    (info@(Info graph _ _), constrM) = makeFullGraph acc
    ilp                              = makeILP info
    solution                         = solve' ilp
    labelClusters                    = interpretSolution @ilp solution
    fusedAcc                         = reconstruct graph labelClusters constrM
    solve' = fromJust . unsafePerformIO . solve @ilp

