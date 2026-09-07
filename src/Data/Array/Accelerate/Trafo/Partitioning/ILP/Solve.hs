{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Data.Array.Accelerate.Trafo.Partitioning.ILP.Solve where

import Data.Array.Accelerate.Trafo.Partitioning.ILP.Graph hiding (graph, constraints, bounds)
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Labels (Node, parent, Nodes, Comp, GVal, DataflowEdge, StrictEdge, ReadEdge, InplacePath, WriteEdge)
import Data.Array.Accelerate.Trafo.Partitioning.ILP.LinearConstraint
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Solver hiding (finalize)

import Data.List (groupBy, sortOn)
import Prelude hiding (sum, pi, read )

import qualified Data.Map as M

-- In this file, order very often subly does matter.
-- To keep this clear, we use S.Set whenever it does not,
-- and [] only when it does. It's also often efficient
-- by removing duplicates.
import qualified Data.Set as S
import Data.Function ( on )
import Lens.Micro ((^.),  _1 )
import Lens.Micro.Extras ( view )
import Data.Maybe (fromJust,  mapMaybe )
import Data.Array.Accelerate.Trafo.Partitioning.ILP.ConstraintLanguage (Constraint(..))
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Lower (LowerEnv(..), lowerAll)

data Objective
  -- Old fusion only objectives:
  = NumClusters          -- ^ Minimise the number of clusters.
  | ArrayReads           -- ^ Minimise the number of array reads.
  | ArrayReadsWrites     -- ^ Minimise the number of array reads and writes.
  | IntermediateArrays   -- ^ Minimise the number of intermediate arrays.
  | FusedEdges           -- ^ Minimise the number of unfused edges.
  | Everything           -- ^ Minimise the number of clusters and array reads/writes.
  -- Old fusion objectives with in-place updates as secondary objective:
  | ArrayReads'          -- ^ Minimise the number of array reads, then maximise the number of in-place updates.
  | ArrayReadsWrites'    -- ^ Minimise the number of array reads and writes, then maximise the number of in-place updates.
  | IntermediateArrays'  -- ^ Minimise the number of intermediate arrays, then maximise the number of in-place updates.
  | FusedEdges'          -- ^ Minimise the number of unfused edges, then maximise the number of in-place updates.
  -- Custom objectives:
  | MemoryUsage          -- ^ Minimise the number of distinct intermediate arrays.
  | MemoryUsage'         -- ^ Version of `MemoryUsage` that prioritizes fusion when two solutions would otherwise have the same costs.
  deriving (Show, Bounded, Enum, Eq, Ord)

-- Makes the ILP. Note that this function 'appears' to ignore the Node levels completely!
-- We could add some assertions, but if all the input is well-formed (no labels, constraints, etc
-- that reward putting non-siblings in the same cluster) this is fine: We will interpret 'cluster 3'
-- with parents `Nothing` as a different cluster than 'cluster 3' with parents `Just 5`.
makeILP :: forall op. MakesILP op => Objective -> FusionILP op -> ILP op
makeILP obj (FusionILP graph constraints bounds) =
  ILP minMax objFun loweredConstraints (graphBounds <> bounds) (Constants n m)
  where
    graphBounds = fusionBounds <> inPlaceBounds

    lowered :: (LinearConstraint op, Bounds op, Expression op)
    lowered = lowerAll (LowerEnv n) $ finalize graph <> fusionConstraints <> inPlaceConstraints <> constraints

    (loweredConstraints, loweredBounds, loweredCost) = lowered

    fusionConstraints = strictAcyclicConstraints
        <> infusibleConstraints
        <> manifestConstraints
        <> fusibleAcyclicConstraints
        <> fusionDirectionConstraints
        <> numberOfClustersConstraints
        <> horizontalReadCostConstraints
        <> manifestValueConstraints
        <> noInPlaceConstraints

    fusionBounds = piB <> fusedB <> manifestB <> loweredBounds

    inPlaceConstraints = if enableIU
        then onManifestConstraints
            <> inPlaceDirectionConstraints
            <> inPlaceClusterConstraints
            <> acrossClusterConstraints
            <> atMostOneReaderConstraints
            <> atMostOneWriterConstraints
            <> readAliveThroughWritersConstraints
        else mempty

    inPlaceBounds = if enableIU then pimaxB <> inplaceB else mempty

    ----------------------------------------------------------------------------
    -- Utils:
    ----------------------------------------------------------------------------

    compN :: Nodes Comp
    compN = graph^.computationNodes

    buffN :: Nodes GVal
    buffN = graph^.valueNodes

    n :: Int
    n = S.size compN

    m :: Int
    m = S.size buffN

    ----------------------------------------------------------------------------
    -- Fusion:
    ----------------------------------------------------------------------------
    dataflowE :: S.Set DataflowEdge
    dataflowE = graph^.dataflowEdges

    strictE :: S.Set StrictEdge
    strictE = graph^.strictEdges

    fusibleE, infusibleE :: S.Set DataflowEdge
    (fusibleE, infusibleE) = graph^.fusionEdges

    fusibleE', infusibleE' :: S.Set (Node Comp, Node Comp)
    fusibleE'   = S.map (\(i,_,j) -> (i,j)) fusibleE
    infusibleE' = S.map (\(i,_,j) -> (i,j)) infusibleE

    -- objective function that maximises the number of edges we fuse, and minimises the number of array reads if you ignore horizontal fusion
    numberOfUnfusedEdges = foldMap fused fusibleE'

    -- A cost function that doesn't ignore horizontal fusion.
    -- Idea: Each node $x$ with $n$ outgoing edges gets $n$ extra variables.
    -- Each edge (fused or not) $(x,y)$ will require that one of these variables is equal to $pi y$.
    -- The number of extra variables that are equal to 0 (the thing you maximise) is exactly equal to n - the number of clusters that read from $x$.
    -- Then, we also need n^2 intermediate variables just to make these disjunction of conjunctions
    -- note, it's only quadratic in the number of consumers of a specific array.
    -- We also check for the 'order': horizontal fusion only happens when the two fused accesses are in the same order.
    horizontalReadCostConstraints :: [Constraint op]
    horizontalReadCostConstraints = [HorizontalReadCost consumers
        | computation <- S.toList compN
        , let consumers = S.toList . S.map (\(_,b,c) -> (b,c)) $ S.filter (\(c,_,_) -> c == computation) fusibleE]

    numberOfReads = loweredCost .+. numberOfUnfusedEdges

    -- objective function that maximises the number of fused away arrays, and thus minimises the number of array writes
    -- using .-. instead of notB to factor the constants out of the cost function; if we use (1 - manifest l) as elsewhere Gurobi thinks the 1 is a variable name
    numberOfManifestArrays = foldl' (\e b -> e .-. manifest b) (int 0) buffN

    -- objective function that minimises the total number of array reads + writes
    numberOfArrayReadsWrites = numberOfReads .+. numberOfManifestArrays

    -- objective function that minimises the number of clusters only works if the constraint below it is used!
    -- NOTE: this does not work remotely as well as you'd hope, because the ILP outputs clusters that get split afterwards.
    -- This includes independent array operations, which might not be safe to fuse and get no real benefit from fusing,
    -- but also includes independent alloc, compute, etc nodes which we don't even want to count in the first place!
    -- It's possible to also give each array operation a 'exec-pi' variable, and change this to minimise the maximum of
    -- these exec-pi values, in which case we are only left with the independent array operations problem.
    -- To eliminate that one too, we'd need n^2 edges.
    numberOfClusters  = maxCluster

    -- pi_i < pi_j for all strict edges
    strictAcyclicConstraints   = map (uncurry ClusterBefore)    $ S.toList strictE

    -- x_ij == 1 for all infusible edges
    infusibleConstraints       = map (uncurry DifferentCluster) $ S.toList infusibleE'

    -- forall b, iff all (w,b,r) are fused, then b is not manifest.
    manifestConstraints        = map (uncurry NotManifestIfAllFused) . M.toList $ foldl (flip \(i,b,j) -> M.insertWith (<>) b [(i,j)]) M.empty dataflowE

    -- x_ij <= pi_j - pi_i <= n*x_ij for all fusible edges
    fusibleAcyclicConstraints  = map (uncurry FusibleOrder) $ S.toList fusibleE'

    -- if (w,b,r) is fused, then d_wb == d_br
    fusionDirectionConstraints = map (\(w,b,r) -> FusionDirection w b r) $ S.toList fusibleE

    -- removing this makes the ILP slightly smaller, but disables the use of this cost function
    numberOfClustersConstraints = case obj of
        NumClusters -> map WithinClusterCount $ S.toList compN
        Everything  -> map WithinClusterCount $ S.toList compN
        _ -> []

    -- b is manifest, for every program result
    manifestValueConstraints = map Manifest $ S.toList $ graph^.manifestValues

    -- b stays live past every cluster
    noInPlaceConstraints = map NoInPlace $ S.toList $ graph^.noInplaceValues

    --  0 <= pi_i <= n
    piB = foldMap (\i -> lowerUpper 0 (Pi i) n) compN

    -- 0 <= x_ij <= 1
    fusedB = foldMap (binary . uncurry Fused) $ S.map (\(i,_,j) -> (i,j)) dataflowE

    -- 0 <= m_i  <= 1
    manifestB = foldMap (binary . IsManifest) buffN


    ----------------------------------------------------------------------------
    -- In-place updates:
    ----------------------------------------------------------------------------

    -- NOTE: Here we need to use the number of non-inplace updates, because using 1 - x is not liked by the solver.
    -- TODO: Either make the internal structure more robust by only allowing variables to appear once per expression/constraint,
    -- or add a simplification step to ensure this is the case.

    readE :: S.Set ReadEdge
    readE = graph^.readEdges

    inplaceP :: S.Set InplacePath
    inplaceP = M.keysSet $ graph^.inplacePaths

    -- Number of in-place updates:
    numberOfNonInplaceUpdates = foldMap inplace inplaceP

    -- If inplace p, then manifest b1 and manifest b2
    onManifestConstraints :: [Constraint op]
    onManifestConstraints = [OnManifestIfInPlace p | p <- S.toList inplaceP]

    -- If inplace p, then d_br == d_wb
    inPlaceDirectionConstraints :: [Constraint op]
    inPlaceDirectionConstraints = [InPlaceDirection p | p <- S.toList inplaceP]

    -- If inplace p, then pimax b1 >= pi c2
    inPlaceClusterConstraints :: [Constraint op]
    inPlaceClusterConstraints = [InPlaceCluster p | p <- S.toList inplaceP]

    -- If inplace p, then c1 == c2
    acrossClusterConstraints :: [Constraint op]
    acrossClusterConstraints = [AcrossClusterSame p | p <- S.toList inplaceP]

    readerGroups = foldl (flip \p@((b,_),_) -> M.insertWith (<>) b [p]) M.empty inplaceP
    writerGroups = foldl (flip \p@(_,(_,b)) -> M.insertWith (<>) b [p]) M.empty inplaceP

    -- Forall b, at most one inplace p
    atMostOneReaderConstraints :: [Constraint op]
    atMostOneReaderConstraints = [AtMostOneReader ps | ps <- M.elems readerGroups]

    -- Forall b, at most one inplace p
    atMostOneWriterConstraints :: [Constraint op]
    atMostOneWriterConstraints = [AtMostOneWriter ps | ps <- M.elems writerGroups]

    -- Group inplace paths by read edge:
    readM = foldl (flip \(r,w) -> M.insertWith (<>) r [w]) M.empty inplaceP

    -- Iff     inplace p, then pi c1     <= pimax b1
    -- Iff not inplace p, then pi c1 + 1 <= pimax b1
    readAliveThroughWritersConstraints :: [Constraint op]
    readAliveThroughWritersConstraints = [ReadAliveThroughWriters r (M.findWithDefault [] r readM) | r <- S.toList readE]

    -- TODO: Maybe add a constraint that c2 is the first writer to b2?
    -- This would make sense because the graph doesn't acctually enforce there is only one writer per buffer.
    -- For most cases there shouldn't be more than 2 writers, one of which is a let-binding, so no issues arise without this constraint.
    -- However, a mutable computation would create a third writer, which would be a problem.

    -- 0 <= pimax_b
    pimaxB = foldMap (\b -> lowerUpper 0 (PiMax b) (n+5)) buffN

    -- inplace b1 b2 \in {0, 1}
    inplaceB = foldMap (\((b1,c1),(c2,b2)) -> binary $ InPlace b1 c1 c2 b2) inplaceP

    ----------------------------------------------------------------------------
    -- Objective function
    ----------------------------------------------------------------------------

    -- Since we want all clusters to have one 'iteration size', the final objFun should
    -- take care to never reward 'fusing' disjoint clusters, and then slightly penalise it.
    -- The alternative is O(n^2) edges, so this is worth the trouble!
    --
    -- In the future, maybe we want this to be backend-dependent (add to MakesILP).
    -- Also future: add @IVO's IPU reward here.
    (enableIU, minMax, objFun) = case obj of
      NumClusters         -> (False, Minimise, numberOfClusters)
      ArrayReads          -> (False, Minimise, numberOfReads)
      ArrayReadsWrites    -> (False, Minimise, numberOfArrayReadsWrites)
      IntermediateArrays  -> (False, Minimise, numberOfManifestArrays)
      FusedEdges          -> (False, Minimise, numberOfUnfusedEdges)
      Everything          -> (False, Minimise, numberOfClusters .+. numberOfArrayReadsWrites) -- arrayreadswrites already indictly includes everything else
      ArrayReads'         -> (True,  Minimise, (int m .*. numberOfReads)            .+. numberOfNonInplaceUpdates)
      ArrayReadsWrites'   -> (True,  Minimise, (int m .*. numberOfArrayReadsWrites) .+. numberOfNonInplaceUpdates)
      IntermediateArrays' -> (True,  Minimise, (int m .*. numberOfManifestArrays)   .+. numberOfNonInplaceUpdates)
      FusedEdges'         -> (True,  Minimise, (int m .*. numberOfUnfusedEdges)     .+. numberOfNonInplaceUpdates)
      MemoryUsage         -> (True,  Minimise, numberOfManifestArrays .+. numberOfNonInplaceUpdates)
      MemoryUsage'        -> (True,  Minimise, (int (m+1) .*. numberOfManifestArrays) .+. (int m .*. numberOfNonInplaceUpdates))  -- We want to prioritise solutions that use fusion, so the weight of fusion is increased by a small factor.


-- | Extract the read directions from the ILP solution.
interpretReadDirs :: forall op. Solution op -> M.Map ReadEdge Int
interpretReadDirs = M.fromList . mapMaybe (_1 fromReadDir) . M.toList
  where
    fromReadDir :: Var op -> Maybe ReadEdge
    fromReadDir (ReadDir b c) = Just (b, c)
    fromReadDir _             = Nothing

-- | Extract the write directions from the ILP solution.
interpretWriteDirs :: forall op. Solution op -> M.Map WriteEdge Int
interpretWriteDirs = M.fromList . mapMaybe (_1 fromWriteDir) . M.toList
  where
    fromWriteDir :: Var op -> Maybe WriteEdge
    fromWriteDir (WriteDir c b) = Just (c, b)
    fromWriteDir _              = Nothing

-- | Extract the top-level clusters and the sub-scoped clusters from the ILP
--   solution.
interpretClusters :: Solution op -> ([Nodes Comp], M.Map (Node Comp) [Nodes Comp])
interpretClusters sol = do
  let            piVars  = mapMaybe (_1 fromPi) (M.toList sol)               -- Take the Pi variables.
  let      scopedPiVars  = partition (^._1.parent) piVars                    -- Partition them by their parent (i.e. the scope they are in).
  let   clusteredPiVars  = map (partition snd) scopedPiVars                  -- Partition them again by their cluster (i.e. the value of the variable).
  let    scopedClusters  = map (map $ S.fromList . map fst) clusteredPiVars  -- Remove the cluster numbers and convert each cluster to a set.
  let       topClusters  = head scopedClusters  -- The first scope in the list is the top-level scope.
  let subScopedClusters  = tail scopedClusters  -- The rest of the scopes are arbitrarily nested sub-scopes.
  let subScopedClustersM = M.fromList $ map (\s -> (scopeLabel s, s)) subScopedClusters
  (topClusters, subScopedClustersM)
  where
    fromPi :: Var op -> Maybe (Node Comp)
    fromPi (Pi l) = Just l
    fromPi _      = Nothing

    scopeLabel :: [Nodes Comp] -> Node Comp
    scopeLabel = fromJust . view parent . S.findMin . head

-- | `groupBy` except it's equivalent to SQL's `GROUP BY` clause.
partition :: Ord b => (a -> b) -> [a] -> [[a]]
partition f = groupBy ((==) `on` f) . sortOn f

interpretInplaceUpdates :: Solution op -> M.Map (Node GVal) (Node GVal)
interpretInplaceUpdates sol = M.map firstInChain inplaceM
  where
    -- Map from buffer to the buffer that will replace it.
    inplaceM = M.fromList $ mapMaybe fromInPlace $ M.toList sol

    fromInPlace :: (Var op, Int) -> Maybe (Node GVal, Node GVal)
    fromInPlace (InPlace b1 _ _ b2, v) | v == 0 = Just (b2, b1)
    fromInPlace _ = Nothing

    firstInChain :: Node GVal -> Node GVal
    firstInChain b = maybe b firstInChain (M.lookup b inplaceM)

-- | Cluster labels, distinguishing between execute and non-execute labels.
data ClusterLs = Execs (Nodes Comp) | NonExec (Node Comp)
  deriving (Eq, Show)

-- I think that only `let`s can still be in the same cluster as `exec`s,
-- and their bodies should all be in earlier clusters already.
-- Simply make one cluster per let, before the cluster with execs.
splitExecs :: ([Nodes Comp], M.Map (Node Comp) [Nodes Comp]) -> Symbols op -> ([ClusterLs], M.Map (Node Comp) [ClusterLs])
splitExecs (xs, xM) symbolM = (f xs, M.map f xM)
  where
    f :: [Nodes Comp] -> [ClusterLs]
    f = concatMap (\ls -> filter (/= Execs mempty) $ map NonExec (S.toList $ S.filter isBeforeExec ls) ++ [Execs (S.filter isExec ls)] ++ afterexecs ls)

    isExec :: Node Comp -> Bool
    isExec l = case symbolM M.!? l of
      Just SExe {} -> True
      Just SExe'{} -> True
      _ -> False
    isBeforeExec l = case symbolM M.!? l of
      Just SLet{} -> True
      _ -> False
    isAfterExec l = case symbolM M.!? l of
      Just SExe{} -> False
      Just SExe'{} -> False
      Just SLet{} -> False
      Nothing -> False
      _ -> True
    -- Tests say that this happens, and that it's correct anyway, but I'm unsure why.
    -- The reason I doubt is because if multiple non-exec, non-lhs nodes are here, the current reconstruction code
    -- (I think) ignores all but the last one.
    afterexecs ls = let xs = map NonExec (S.toList $ S.filter isAfterExec ls) in if length xs > 1 then xs {-error "dunno what this means"-} else xs
