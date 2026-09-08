{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Data.Array.Accelerate.Trafo.Partitioning.ILP where
-- No joke, this really needs to get a massive refactor...

import Data.Array.Accelerate.Trafo.Partitioning.ILP.Graph
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Encoding
    ( interpretClusters, makeILP, splitExecs, ClusterLs, Objective (..), interpretReadDirs, interpretInplaceUpdates )
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Clustering
    ( reconstruct, reconstructF, ReadDirM, InplaceM )
import Data.Array.Accelerate.AST.Partitioned
    ( PartitionedAcc, PartitionedAfun, Cluster, groundsR )
import Data.Array.Accelerate.AST.Operation
    ( OperationAcc, OperationAfun )
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Solver
    ( ILPSolver, solve, Solution )
import Data.Array.Accelerate.Trafo.Partitioning.ILP.MIP
    ( cbc, cplex, glpsol, gurobiCl, lpSolve, scip, MIP(..) )

import System.IO.Unsafe (unsafePerformIO)
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Labels (Node, Comp)
import Data.Map (Map, toList, foldMapWithKey, filterWithKey)
import Data.Array.Accelerate.Trafo.Operation.Simplify
import qualified Data.Array.Accelerate.Pretty.Operation as Pretty
import Lens.Micro ((^.))
import Data.Maybe (fromMaybe)

data Benchmarking = GreedyUp | GreedyDown | NoFusion
  deriving (Show, Eq, Bounded, Enum)

data FusionType = Fusion Objective | Benchmarking Benchmarking

defaultObjective :: FusionType
defaultObjective = Fusion MemoryUsage'

-- data type that should probably be in the options
newtype Solver = MIPSolver MIPSolver
data MIPSolver = CBC | Gurobi | CPLEX | GLPSOL | LPSOLVE | SCIP

ilpFusion'' :: (MakesILP op, SimplifyOperation op, Pretty.PrettyOp (Cluster op)) => Solver -> Objective -> OperationAcc op () a -> PartitionedAcc op () a
ilpFusion'' (MIPSolver s) = case s of
  CBC     -> ilpFusion (MIP cbc)
  Gurobi  -> ilpFusion (MIP gurobiCl)
  CPLEX   -> ilpFusion (MIP cplex)
  GLPSOL  -> ilpFusion (MIP glpsol)
  LPSOLVE -> ilpFusion (MIP lpSolve)
  SCIP    -> ilpFusion (MIP scip)


ilpFusionF'' :: (MakesILP op, SimplifyOperation op, Pretty.PrettyOp (Cluster op)) => Solver -> Objective -> OperationAfun op () a -> PartitionedAfun op () a
ilpFusionF'' (MIPSolver s) = case s of
  CBC     -> ilpFusionF (MIP cbc)
  Gurobi  -> ilpFusionF (MIP gurobiCl)
  CPLEX   -> ilpFusionF (MIP cplex)
  GLPSOL  -> ilpFusionF (MIP glpsol)
  LPSOLVE -> ilpFusionF (MIP lpSolve)
  SCIP    -> ilpFusionF (MIP scip)


ilpFusion  :: (MakesILP op, SimplifyOperation op, ILPSolver s, Pretty.PrettyOp (Cluster op)) => s -> Objective -> OperationAcc  op () a -> PartitionedAcc op () a
ilpFusion solver objective acc = ilpFusion' mkFullGraph  (reconstruct (groundsR acc) False) solver objective acc

ilpFusionF :: (MakesILP op, SimplifyOperation op, ILPSolver s, Pretty.PrettyOp (Cluster op)) => s -> Objective -> OperationAfun op () a -> PartitionedAfun op () a
ilpFusionF solver objective fun = ilpFusion' mkFullGraphF (reconstructF fun False) solver objective fun

ilpFusion' :: (MakesILP op, SimplifyOperation op, ILPSolver s)
           => (x -> FullGraph op)
           -> (FusionGraph -> [ClusterLs] -> Map (Node Comp) [ClusterLs] -> Symbols op -> ReadDirM -> InplaceM -> y)
           -> s
           -> Objective
           -> x
           -> y
ilpFusion' toGraph fromGraph s obj acc = do
  let fullgraph = {- traceGraph $ -} toGraph acc
  let ilp       = makeILP obj (fullgraph^.fusionILP)
  let solution  = {- traceWith ppNumInplace $ -} fromMaybe (error "Accelerate: No ILP solution found") (unsafePerformIO $ solve s ilp)
  let symbols'  = attachBackendLabels solution (fullgraph^.symbols)
  let readDirM  = interpretReadDirs  solution
  -- let writeDirM = interpretWriteDirs solution
  let inplaceM  = interpretInplaceUpdates solution
  let (topClusters, subClustersM) = splitExecs (interpretClusters solution) symbols'
  fromGraph (fullgraph^.fusionILP.graph) topClusters subClustersM symbols' readDirM inplaceM

traceGraph :: FullGraph op -> FullGraph op
traceGraph g = unsafePerformIO $ do
  writeFile "ilp.dot" $ toDOT (g^.fusionILP.graph) (g^.symbols)
  return g

ppNumInplace :: Solution -> String
ppNumInplace m = "Compilation performed " ++ show numInplace ++ "/" ++ show totalInplace ++ " in-place updates."
  where
    inplaceVars = filterWithKey (\k _ -> case k of InPlace{} -> True; _ -> False) m
    totalInplace = length inplaceVars
    numInplace = length $ filterWithKey (\_ v -> v == 0) inplaceVars


ppSolution :: Solution -> String
ppSolution solution = "solution: " ++ foldMap ppVar (toList solution)
  where
    ppVar :: (Var, Int) -> String
    ppVar (k, v) = "\n" ++ show k ++ " == " ++ show v
    -- ppVar (k, v) = case k of
    --   Pi{}               -> "\n" ++ show k  ++ " == " ++ show v
    --   Fused{} | v == 0   -> "\n" ++ show k
    --   Manifest{}         -> "\n" ++ show k  ++ " == " ++ show v
    --   InPlace{} | v == 0 -> "\n" ++ show k
    --   _ -> ""

ppList :: Show a => [a] -> String
ppList [] = "[]"
ppList [x] = "[" ++ show x ++ "]"
ppList (x:xs) = "[ " ++ show x ++ foldMap (\x -> "\n, " ++ show x) xs ++ "\n]"

ppScopedClusters :: (Show k, Show v) => ([v], Map k [v]) -> String
ppScopedClusters (top, sub) = "top =\n" ++ ppList top ++ foldMapWithKey (\k v -> "\n" ++ show k ++ " =\n" ++ ppList v) sub

-- for benchmarking: make all edges infusible
-- note: does allow for horizontal fusion!
-- more rigorous is to change 'topSort' in Clustering.hs into separating each cluster completely
noFusion' :: (MakesILP op, SimplifyOperation op, ILPSolver s)
           => (x -> FullGraph op)
           -> (FusionGraph -> [ClusterLs] -> Map (Node Comp) [ClusterLs] -> Symbols op -> ReadDirM -> InplaceM -> y)
           -> s
           -> Objective
           -> x
           -> y
noFusion' = undefined
-- noFusion' k1 k2 s obj acc = fusedAcc
--   where
--     (fusionILP', constrM')          = k1 acc
--     fusionILP''                     = fusionILP' & graph.strictEdges <>~ Set.map (\(w,_,r) -> (w,r)) (fusionILP'^.graph.fusibleEdges)
--     constrM                         = attachBackendLabels solution constrM'
--     ilp                             = makeILP obj fusionILP''
--     solution                        = solve' ilp
--     interpreted                     = interpretSolution solution
--     (labelClusters, labelClustersM) = splitExecs interpreted constrM
--     fusedAcc                        = k2 (fusionILP'^.graph) labelClusters labelClustersM constrM
--     solve' x = unsafePerformIO (solve s x) & \case
--       Nothing -> error "Accelerate: No ILP solution found"
--       Just y -> y

-- for benchmarking: greedily fuse edges
-- this search is clearly inefficient, but just an easy implementation. We only benchmark its runtime.
-- note that this is perhaps still too generous. For example, anything that can fuse into 1 loop will still be fully fused!
-- it's perhaps more of an 'alternative' than a 'baseline'
greedyFusion' :: forall s op x y. (MakesILP op, SimplifyOperation op, ILPSolver s)
                    => (x -> FullGraph op)
                    -> (FusionGraph -> [ClusterLs] -> Map (Node Comp) [ClusterLs] -> Symbols op -> ReadDirM -> InplaceM -> y)
                    -> s
                    -> Benchmarking
                    -> Objective
                    -> x
                    -> y
greedyFusion' = undefined
-- greedyFusion' k1 k2 s b obj acc = fusedAcc
--   where
--     (info'@(FusionILP graph _ _), constrM') = k1 acc
--     nedges = (graph^.fusibleEdges) Set.\\ (graph^.infusibleEdges) & Set.size
--     go :: Int -> FusionILP op -> FusionILP op
--     go n info -- loop over all fusible edges. Try to set the current one to fused, if there's still a legal solution, keep it fused and continue.
--       | n >= nedges = info
--       | otherwise = let
--         i:->j = (graph^.fusibleEdges) Set.\\ (graph^.infusibleEdges)&Set.elemAt (case b of
--           GreedyUp -> n
--           GreedyDown -> nedges - n - 1
--           _ -> error "nope")
--         info'' = info&constr<>~(fused i j .==. int 0)
--         in go (n+1) $ if check info'' then info'' else info
--     check :: FusionILP op -> Bool
--     check info = let
--       ilp = makeILP @op obj info
--       in isJust $ unsafePerformIO (solve s ilp)
--     info = go 0 info'
--     ilp                               = makeILP FusedEdges info

--     constrM = backendConstruc solution constrM'
--     solution                          = solve' ilp
--     interpreted                       = interpretSolution solution
--     (labelClusters, labelClustersM)   = splitExecs interpreted constrM
--     fusedAcc                          = k2 graph labelClusters labelClustersM constrM
--     solve' x = unsafePerformIO (solve s x) & \case
--       Nothing -> error "Accelerate: No ILP solution found"
--       Just y -> y

bench :: (MakesILP op, SimplifyOperation op, Pretty.PrettyOp (Cluster op)) => Benchmarking -> Objective -> OperationAcc op () a -> PartitionedAcc op () a
bench NoFusion = no
bench b = greedy b
benchF :: (MakesILP op, SimplifyOperation op, Pretty.PrettyOp (Cluster op)) => Benchmarking -> Objective -> OperationAfun op () a -> PartitionedAfun op () a
benchF NoFusion = noF
benchF b = greedyF b
greedy :: (MakesILP op, SimplifyOperation op, Pretty.PrettyOp (Cluster op)) => Benchmarking -> Objective -> OperationAcc op () a -> PartitionedAcc op () a
greedy = greedyFusion (MIP gurobiCl)
no :: (MakesILP op, SimplifyOperation op, Pretty.PrettyOp (Cluster op)) => Objective -> OperationAcc op () a -> PartitionedAcc op () a
no = noFusion (MIP gurobiCl)
greedyF :: (MakesILP op, SimplifyOperation op, Pretty.PrettyOp (Cluster op)) => Benchmarking -> Objective -> OperationAfun op () a -> PartitionedAfun op () a
greedyF = greedyFusionF (MIP gurobiCl)
noF :: (MakesILP op, SimplifyOperation op, Pretty.PrettyOp (Cluster op)) => Objective -> OperationAfun op () a -> PartitionedAfun op () a
noF = noFusionF (MIP gurobiCl)
greedyFusion  :: (MakesILP op, SimplifyOperation op, ILPSolver s, Pretty.PrettyOp (Cluster op)) => s -> Benchmarking -> Objective -> OperationAcc  op () a -> PartitionedAcc op () a
greedyFusion  solver b objective acc = greedyFusion' mkFullGraph  (reconstruct (groundsR acc) False) solver b objective acc
greedyFusionF :: (MakesILP op, SimplifyOperation op, ILPSolver s, Pretty.PrettyOp (Cluster op)) => s -> Benchmarking -> Objective -> OperationAfun op () a -> PartitionedAfun op () a
greedyFusionF solver b objective fun = greedyFusion' mkFullGraphF (reconstructF fun False) solver b objective fun
noFusion      :: (MakesILP op, SimplifyOperation op, ILPSolver s, Pretty.PrettyOp (Cluster op)) => s -> Objective -> OperationAcc  op () a -> PartitionedAcc op () a
noFusion      solver objective acc =     noFusion' mkFullGraph  (reconstruct (groundsR acc) True) solver objective acc
noFusionF     :: (MakesILP op, SimplifyOperation op, ILPSolver s, Pretty.PrettyOp (Cluster op)) => s -> Objective -> OperationAfun op () a -> PartitionedAfun op () a
noFusionF     solver objective fun =     noFusion' mkFullGraphF (reconstructF fun True) solver objective fun
