{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE LambdaCase #-}
module Data.Array.Accelerate.Trafo.Partitioning.ILP where

import Data.Array.Accelerate.Trafo.Partitioning.ILP.Graph
    ( MakesILP (), Information(Info), makeFullGraph, Construction, makeFullGraphF, Graph, backendConstruc, fusibleEdges, Edge (..), constr, fused, infusibleEdges ) 
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Solve
    ( interpretSolution, makeILP, splitExecs, ClusterLs, Objective (..) ) 
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Clustering
    ( reconstruct, reconstructF )
import Data.Array.Accelerate.AST.Partitioned
    ( PartitionedAcc, PartitionedAfun, Cluster, groundsR )
import Data.Array.Accelerate.AST.Operation
    ( OperationAcc, OperationAfun )
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Solver
    ( ILPSolver, solve, (.==.), int )
import Data.Array.Accelerate.Trafo.Partitioning.ILP.MIP
    ( cbc, cplex, glpsol, gurobiCl, lpSolve, scip, MIP(..) )

import System.IO.Unsafe (unsafePerformIO)
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Labels (Label)
import Data.Map (Map)
import qualified Data.Array.Accelerate.Pretty.Operation as Pretty
import Data.Function ((&))
import qualified Data.Set as Set
import Lens.Micro ((^.), (<>~))
import Data.Maybe (isJust)
-- import Data.Array.Accelerate.Trafo.Partitioning.ILP.HiGHS

data Benchmarking = GreedyUp | GreedyDown | NoFusion
  deriving (Show, Eq, Bounded, Enum)

data FusionType = Fusion Objective | Benchmarking Benchmarking

defaultObjective :: FusionType
defaultObjective = Fusion IntermediateArrays

-- data type that should probably be in the options
newtype Solver = MIPSolver MIPSolver
data MIPSolver = CBC | Gurobi | CPLEX | GLPSOL | LPSOLVE | SCIP

ilpFusion'' :: (MakesILP op, Pretty.PrettyOp (Cluster op)) => Solver -> Objective -> OperationAcc op () a -> PartitionedAcc op () a
ilpFusion'' (MIPSolver s) = case s of
  CBC     -> ilpFusion (MIP cbc)
  Gurobi  -> ilpFusion (MIP gurobiCl)
  CPLEX   -> ilpFusion (MIP cplex)
  GLPSOL  -> ilpFusion (MIP glpsol)
  LPSOLVE -> ilpFusion (MIP lpSolve)
  SCIP    -> ilpFusion (MIP scip)


ilpFusionF'' :: (MakesILP op, Pretty.PrettyOp (Cluster op)) => Solver -> Objective -> OperationAfun op () a -> PartitionedAfun op () a
ilpFusionF'' (MIPSolver s) = case s of
  CBC     -> ilpFusionF (MIP cbc)
  Gurobi  -> ilpFusionF (MIP gurobiCl)
  CPLEX   -> ilpFusionF (MIP cplex)
  GLPSOL  -> ilpFusionF (MIP glpsol)
  LPSOLVE -> ilpFusionF (MIP lpSolve)
  SCIP    -> ilpFusionF (MIP scip)


ilpFusion  :: (MakesILP op, ILPSolver s op, Pretty.PrettyOp (Cluster op)) => s -> Objective -> OperationAcc  op () a -> PartitionedAcc op () a
ilpFusion solver objective acc = ilpFusion' makeFullGraph  (reconstruct (groundsR acc) False) solver objective acc

ilpFusionF :: (MakesILP op, ILPSolver s op, Pretty.PrettyOp (Cluster op)) => s -> Objective -> OperationAfun op () a -> PartitionedAfun op () a
ilpFusionF solver objective fun = ilpFusion' makeFullGraphF (reconstructF fun False) solver objective fun

ilpFusion' :: (MakesILP op, ILPSolver s op) 
           => (x -> (Information op, Map Label (Construction op))) 
           -> (Graph -> [ClusterLs] -> Map Label [ClusterLs] -> Map Label (Construction op) -> y) 
           -> s 
           -> Objective
           -> x 
           -> y
ilpFusion' k1 k2 s obj acc = fusedAcc
  where
    (info@(Info graph _ _), constrM') = k1 acc
    constrM = backendConstruc solution constrM'
    ilp                               = makeILP obj info
    solution                          = solve' ilp
    interpreted                       = interpretSolution solution
    (labelClusters, labelClustersM)   = splitExecs interpreted constrM
    fusedAcc                          = k2 graph labelClusters labelClustersM constrM
    solve' x = unsafePerformIO (solve s x) & \case
      Nothing -> error "Accelerate: No ILP solution found"
      Just y -> y

-- for benchmarking: make all edges infusible
-- note: does allow for horizontal fusion!
-- more rigorous is to change 'topSort' in Clustering.hs into separating each cluster completely
noFusion' :: (MakesILP op, ILPSolver s op) 
           => (x -> (Information op, Map Label (Construction op))) 
           -> (Graph -> [ClusterLs] -> Map Label [ClusterLs] -> Map Label (Construction op) -> y) 
           -> s 
           -> Objective
           -> x 
           -> y
noFusion' k1 k2 s obj acc = fusedAcc
  where
    (info@(Info graph' _ _), constrM') = k1 acc
    graph = graph'&infusibleEdges<>~graph'^.fusibleEdges
    constrM = backendConstruc solution constrM'
    ilp                               = makeILP obj info
    solution                          = solve' ilp
    interpreted                       = interpretSolution solution
    (labelClusters, labelClustersM)   = splitExecs interpreted constrM
    fusedAcc                          = k2 graph labelClusters labelClustersM constrM
    solve' x = unsafePerformIO (solve s x) & \case
      Nothing -> error "Accelerate: No ILP solution found"
      Just y -> y

-- for benchmarking: greedily fuse edges
-- this search is clearly inefficient, but just an easy implementation. We only benchmark its runtime.
-- note that this is perhaps still too generous. For example, anything that can fuse into 1 loop will still be fully fused!
-- it's perhaps more of an 'alternative' than a 'baseline'
greedyFusion' :: forall s op x y. (MakesILP op, ILPSolver s op)
                    => (x -> (Information op, Map Label (Construction op))) 
                    -> (Graph -> [ClusterLs] -> Map Label [ClusterLs] -> Map Label (Construction op) -> y) 
                    -> s
                    -> Benchmarking
                    -> Objective
                    -> x 
                    -> y
greedyFusion' k1 k2 s b obj acc = fusedAcc
  where
    (info'@(Info graph _ _), constrM') = k1 acc
    nedges = (graph^.fusibleEdges) Set.\\ (graph^.infusibleEdges) & Set.size
    go :: Int -> Information op -> Information op
    go n info -- loop over all fusible edges. Try to set the current one to fused, if there's still a legal solution, keep it fused and continue.
      | n >= nedges = info
      | otherwise = let
        i:->j = (graph^.fusibleEdges) Set.\\ (graph^.infusibleEdges)&Set.elemAt (case b of
          GreedyUp -> n 
          GreedyDown -> nedges - n - 1
          _ -> error "nope")
        info'' = info&constr<>~(fused i j .==. int 0)
        in go (n+1) $ if check info'' then info'' else info
    check :: Information op -> Bool
    check info = let
      ilp = makeILP @op obj info
      in isJust $ unsafePerformIO (solve s ilp)
    info = go 0 info'
    ilp                               = makeILP FusedEdges info

    constrM = backendConstruc solution constrM'
    solution                          = solve' ilp
    interpreted                       = interpretSolution solution
    (labelClusters, labelClustersM)   = splitExecs interpreted constrM
    fusedAcc                          = k2 graph labelClusters labelClustersM constrM
    solve' x = unsafePerformIO (solve s x) & \case
      Nothing -> error "Accelerate: No ILP solution found"
      Just y -> y

bench :: (MakesILP op, Pretty.PrettyOp (Cluster op)) => Benchmarking -> Objective -> OperationAcc op () a -> PartitionedAcc op () a
bench NoFusion = no
bench b = greedy b
benchF :: (MakesILP op, Pretty.PrettyOp (Cluster op)) => Benchmarking -> Objective -> OperationAfun op () a -> PartitionedAfun op () a
benchF NoFusion = noF
benchF b = greedyF b
greedy :: (MakesILP op, Pretty.PrettyOp (Cluster op)) => Benchmarking -> Objective -> OperationAcc op () a -> PartitionedAcc op () a
greedy = greedyFusion (MIP gurobiCl)
no :: (MakesILP op, Pretty.PrettyOp (Cluster op)) => Objective -> OperationAcc op () a -> PartitionedAcc op () a
no = noFusion (MIP gurobiCl)
greedyF :: (MakesILP op, Pretty.PrettyOp (Cluster op)) => Benchmarking -> Objective -> OperationAfun op () a -> PartitionedAfun op () a
greedyF = greedyFusionF (MIP gurobiCl)
noF :: (MakesILP op, Pretty.PrettyOp (Cluster op)) => Objective -> OperationAfun op () a -> PartitionedAfun op () a
noF = noFusionF (MIP gurobiCl)
greedyFusion  :: (MakesILP op, ILPSolver s op, Pretty.PrettyOp (Cluster op)) => s -> Benchmarking -> Objective -> OperationAcc  op () a -> PartitionedAcc op () a
greedyFusion  solver b objective acc = greedyFusion' makeFullGraph  (reconstruct (groundsR acc) False) solver b objective acc
greedyFusionF :: (MakesILP op, ILPSolver s op, Pretty.PrettyOp (Cluster op)) => s -> Benchmarking -> Objective -> OperationAfun op () a -> PartitionedAfun op () a
greedyFusionF solver b objective fun = greedyFusion' makeFullGraphF (reconstructF fun False) solver b objective fun
noFusion      :: (MakesILP op, ILPSolver s op, Pretty.PrettyOp (Cluster op)) => s -> Objective -> OperationAcc  op () a -> PartitionedAcc op () a
noFusion      solver objective acc =     noFusion' makeFullGraph  (reconstruct (groundsR acc) True) solver objective acc
noFusionF     :: (MakesILP op, ILPSolver s op, Pretty.PrettyOp (Cluster op)) => s -> Objective -> OperationAfun op () a -> PartitionedAfun op () a
noFusionF     solver objective fun =     noFusion' makeFullGraphF (reconstructF fun True) solver objective fun
