{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RecordWildCards #-}

module Data.Array.Accelerate.Trafo.Partitioning.ILP.Solve where


import Data.Array.Accelerate.Trafo.Partitioning.ILP.Graph hiding (readEdges, writeEdges, strictEdges, dataflowEdges, constraints, bounds)
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Labels
    (Label, parent, Labels, LabelType (..) )
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Solver hiding (finalize)

import Data.List (groupBy, sortOn)
import Prelude hiding ( pi, read )

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
import Control.Monad.State
import Data.Array.Accelerate.Trafo.Partitioning.ILP.NameGeneration (freshName)
import Data.Foldable
import Data.Tuple (swap)

data Objective
  = NumClusters
  | ArrayReads
  | ArrayReadsWrites
  | IntermediateArrays
  | FusedEdges
  | Everything
  deriving (Show, Bounded, Enum)


-- Makes the ILP. Note that this function 'appears' to ignore the Label levels completely!
-- We could add some assertions, but if all the input is well-formed (no labels, constraints, etc
-- that reward putting non-siblings in the same cluster) this is fine: We will interpret 'cluster 3'
-- with parents `Nothing` as a different cluster than 'cluster 3' with parents `Just 5`.
makeILP :: forall op. MakesILP op => Objective -> FusionILP op -> ILP op
makeILP obj (FusionILP (Graph readEdges writeEdges strictEdges dataflowEdges) constraints bounds) = combine graphILP
  where
    fusibleEdges, infusibleEdges :: S.Set (Label Comp, Label Buff, Label Comp)
    (fusibleEdges, infusibleEdges) = S.partition (\(c1, _, c2) -> S.notMember (c1, c2) strictEdges) dataflowEdges

    bufferNodes      :: S.Set (Label Buff)
    computationNodes :: S.Set (Label Comp)
    (bufferNodes, computationNodes) = S.foldr  biinsert         mempty readEdges
                                   <> S.foldr (biinsert . swap) mempty writeEdges

    biinsert :: (Ord a, Ord b) => (a, b) -> (S.Set a, S.Set b) -> (S.Set a, S.Set b)
    biinsert (a, b) (as, bs) = (S.insert a as, S.insert b bs)

    combine :: ILP op -> ILP op
    combine (ILP dir fun cons bnds _) =
      ILP dir fun (cons <> constraints) (bnds <> bounds) n

    -- n is used in some of the constraints, as an upperbound on the number of clusters.
    -- We add a small constant to be safe, as some variables have ranges from -3 to number of nodes.
    -- Then, we also multiply by 2, as some variables range from -n to n
    n :: Int
    n = 10 + 2 * S.size computationNodes

    graphILP = ILP minmax objFun myConstraints myBounds n

    -- Since we want all clusters to have one 'iteration size', the final objFun should
    -- take care to never reward 'fusing' disjoint clusters, and then slightly penalise it.
    -- The alternative is O(n^2) edges, so this is worth the trouble!
    --
    -- In the future, maybe we want this to be backend-dependent (add to MakesILP).
    -- Also future: add @IVO's IPU reward here.
    objFun :: Expression op
    minmax :: OptDir
    (minmax,objFun) = case obj of
      NumClusters         -> (Minimise, numberOfClusters)
      ArrayReads          -> (Minimise, numberOfReads)
      ArrayReadsWrites    -> (Minimise, numberOfArrayReadsWrites)
      IntermediateArrays  -> (Minimise, numberOfManifestArrays)
      FusedEdges          -> (Minimise, numberOfUnfusedEdges)
      Everything          -> (Minimise, numberOfClusters .+. numberOfArrayReadsWrites) -- arrayreadswrites already indictly includes everything else


    -- objective function that maximises the number of edges we fuse, and minimises the number of array reads if you ignore horizontal fusion
    numberOfUnfusedEdges = foldl' (\e (prod, _, cons) -> e .+. fused prod cons) (int 0) fusibleEdges

    -- A cost function that doesn't ignore horizontal fusion.
    -- Idea: Each node $x$ with $n$ outgoing edges gets $n$ extra variables.
    -- Each edge (fused or not) $(x,y)$ will require that one of these variables is equal to $pi y$.
    -- The number of extra variables that are equal to 0 (the thing you maximise) is exactly equal to n - the number of clusters that read from $x$.
    -- Then, we also need n^2 intermediate variables just to make these disjunction of conjunctions
    -- note, it's only quadratic in the number of consumers of a specific array.
    -- We also check for the 'order': horizontal fusion only happens when the two fused accesses are in the same order.
    numberOfReads =  nReads .+. numberOfUnfusedEdges
    (nReads, readConstraints, readBounds)
      = foldl (<>) mempty
      . flip evalState ""
      . forM (S.toList computationNodes) $ \computation -> do
      let consumers  = S.map (\(_,b,c) -> (b,c)) $ S.filter (\(c,_,_) -> c == computation) fusibleEdges
          nConsumers = S.size consumers
      readPis    <- replicateM nConsumers readPiVar
      readOrders <- replicateM nConsumers readOrderVar
      (subConstraint, subBounds) <- flip foldMapM consumers $ \read@(_,consumer) -> do
        useVars <- replicateM nConsumers useVar -- these are the n^2 variables: For each consumer, n variables which each check the equality of pi to readpi
        let constraint = foldMap
              (\(uv, rp, ro) -> isEqualRangeN (var rp) (pi consumer)  (var uv)
                             <> isEqualRangeN (var ro) (readDir read) (var uv))
              (zip3 useVars readPis readOrders)
        return (constraint <> foldl (.+.) (int 0) (map var useVars) .<=. int (nConsumers-1), foldMap binary useVars)
      readPi0s <- replicateM nConsumers readPi0Var
      return ( foldl (.+.) (int 0) (map var readPi0s)
             , subConstraint <> fold (zipWith (\p p0 -> var p .<=. timesN (var p0)) readPis readPi0s)
             , subBounds <> foldMap (\v -> lowerUpper 0 v n) readPis <> foldMap binary readPi0s)

    readOrderVar = Other <$> freshName "ReadOrder"
    readPiVar    = Other <$> freshName "ReadPi"   -- non-zero signifies that at least one consumer reads this array from a certain pi
    readPi0Var   = Other <$> freshName "Read0Pi"  -- signifies whether the corresponding readPi variable is 0
    useVar       = Other <$> freshName "ReadUse"  -- signifies whether a consumer corresponds with a readPi variable; because its pi == readpi

    -- objective function that maximises the number of fused away arrays, and thus minimises the number of array writes
    -- using .-. instead of notB to factor the constants out of the cost function; if we use (1 - manifest l) as elsewhere Gurobi thinks the 1 is a variable name
    numberOfManifestArrays = foldl' (\e b -> e .-. manifest b) (int 0) bufferNodes

    -- objective function that minimises the total number of array reads + writes
    numberOfArrayReadsWrites = numberOfReads .+. numberOfManifestArrays

    -- objective function that minimises the number of clusters -- only works if the constraint below it is used!
    -- NOTE: this does not work remotely as well as you'd hope, because the ILP outputs clusters that get split afterwards.
    -- This includes independent array operations, which might not be safe to fuse and get no real benefit from fusing,
    -- but also includes independent alloc, compute, etc nodes which we don't even want to count in the first place!
    -- It's possible to also give each array operation a 'exec-pi' variable, and change this to minimise the maximum of
    -- these exec-pi values, in which case we are only left with the independent array operations problem.
    -- To eliminate that one too, we'd need n^2 edges.
    numberOfClusters  = var (Other "maximumClusterNumber")
    -- removing this from myConstraints makes the ILP slightly smaller, but disables the use of this cost function
    numberOfClustersConstraint = case obj of NumClusters -> foldMap (\l -> pi l .<=. numberOfClusters) computationNodes
                                             Everything  -> foldMap (\l -> pi l .<=. numberOfClusters) computationNodes
                                             _ -> mempty

    myConstraints = acyclicC <> infusibleC <> manifestC <> numberOfClustersConstraint <> readConstraints <> orderConstraints  -- TODO: Call finalize

    -- x_ij <= pi_j - pi_i <= n*x_ij for all edges
    acyclicC   = foldMap (\(i,_,j) -> between (fused i j) (pi j .-. pi i) (timesN $ fused i j)) dataflowEdges
    infusibleC = foldMap (\(i,_,j) -> fused i j .==. int 1) infusibleEdges

    -- if (i,b,j) is not fused, b has to be manifest
    -- TODO: final output is also manifest
    manifestC = foldMap (\(i,b,j) -> notB (fused i j) `impliesB` manifest b) dataflowEdges


    orderConstraints = flip foldMap fusibleEdges $ \(i,b,j) ->
                    timesN (fused i j) .>=. readDir (b, j) .-. writeDir (i, b)
        <> (-1) .*. timesN (fused i j) .<=. readDir (b, j) .-. writeDir (i, b)

    myBounds :: Bounds op
                   --  0 <= pi_i <= n
    myBounds = foldMap (\i -> lowerUpper 0 (Pi i) n) computationNodes
               <>  -- x_ij \in {0, 1}
               foldMap (\(i,_,j) -> binary $ Fused i j) dataflowEdges
               <>  -- m_i \in {0, 1}
               foldMap (binary . Manifest) bufferNodes
               <>
               readBounds


-- Extract the fusion information (ordered list of clusters of Labels) (head is the first cluster).
-- Output has the top-level clusters in fst, and the rest in snd.
interpretSolution :: MakesILP op => Solution op -> ([Labels Comp], M.Map (Label Comp) [Labels Comp])
interpretSolution
  = (\(x:xs) ->
      ( x
      , M.fromList $
            map
            (\l ->
              ( fromJust -- All labels in the Map will have a parent, only the top clusters can have Nothing as parent (depending on whether we have an Acc or an Afun)
              . view parent
              . S.findMin -- `head` and `findMin` just to get _any_ element:
              . head      -- there is at least one and the parents are all identical
              $ l
              , l))
            xs))
  . map
    ( map
      ( S.fromList
      . map fst)
    . partition snd)
  . partition (^. _1.parent)
  . mapMaybe (_1 fromPi)
  . M.toList
  where
    fromPi (Pi l) = Just l
    fromPi _      = Nothing

    -- groupBy only really does what you want on a sorted list
    partition f = groupBy ((==) `on` f) . sortOn f

-- | Cluster labels, distinguishing between execute and non-execute labels.
data ClusterLs = Execs (Labels Comp) | NonExec (Label Comp)
  deriving (Eq, Show)

-- I think that only `let`s can still be in the same cluster as `exec`s,
-- and their bodies should all be in earlier clusters already.
-- Simply make one cluster per let, before the cluster with execs.
-- TODO: split the cluster of Execs into connected components
splitExecs :: ([Labels Comp], M.Map (Label Comp) [Labels Comp]) -> M.Map (Label Comp) (Symbol op) -> ([ClusterLs], M.Map (Label Comp) [ClusterLs])
splitExecs (xs, xM) constrM = (f xs, M.map f xM)
  where
    f :: [Labels Comp] -> [ClusterLs]
    f = concatMap (\ls -> filter (/= Execs mempty) $ map NonExec (S.toList $ S.filter isNonExec ls) ++ [Execs (S.filter isExec ls)])

    isExec l = case constrM M.!? l of
      Just SExe{}  -> True
      Just SExe'{} -> True
      _ -> False
    isNonExec l = not $ isExec l

-- Only needs Applicative
newtype MonadMonoid f m = MonadMonoid { getMonadMonoid :: f m }
instance (Monad f, Semigroup m) => Semigroup (MonadMonoid f m) where
  (MonadMonoid x) <> (MonadMonoid y) = MonadMonoid $ (<>) <$> x <*> y
instance (Monad f, Monoid m) => Monoid (MonadMonoid f m) where
  mempty = MonadMonoid (pure mempty)

foldMapM :: (Foldable t, Monad f, Monoid m) => (a -> f m) -> t a -> f m
foldMapM f = getMonadMonoid . foldMap (MonadMonoid . f)
