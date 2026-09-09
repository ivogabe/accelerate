{-# LANGUAGE EmptyCase           #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_HADDOCK hide #-}
-- |
-- Module      : Data.Array.Accelerate.AST.Graph
-- Copyright   : [2008..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.AST.Graph (
  Graph, InEdge(..), empty, nodeCount, pushNode, dropNode,
  insertEdge, insertEdgeWith,
  insertEdgesFromWith, insertEdgesToWith,
  insertCartesianEdgesWith, removeEdgesOf,
  out, inn, prjNode, prjEdge, updateNode,

  shortestPath, shortestPathLessThanEqual, shortestPathsFrom, shortestPathsTo
) where

import Data.Array.Accelerate.AST.Idx
import Data.Array.Accelerate.AST.Environment

import Data.Functor.Const
import Data.Maybe
import Data.Typeable ( (:~:)(..) )

-- | Directed well-scoped graph.
-- 'node' is the label on a node, 'edge' the label on an edge.
--
data Graph node edge env where
  GEmpty :: Graph node edge ()
  GPush :: Graph node edge env -> Node node edge env t -> Graph node edge (env, t)

-- An edge (s, t) is stored either in node s or in node t.
-- If s <= t (based on the integral value if the Idx), then it is stored in s,
-- as an outgoing edge.
-- If t < s, then it is stored in t as an incomming edge.

data Node node edge env a = Node
  -- Data of this node
  (node a)
  -- Incomming edges
  (PartialEnv (InEdge edge a) env)
  -- Outgoing edges, potentially with a self-loop
  (PartialEnv (edge a) (env, a))

newtype InEdge edge t s = InEdge (edge s t)

empty :: Graph node edge ()
empty = GEmpty

nodeCount :: Graph node edge env -> Int
nodeCount GEmpty = 0
nodeCount (GPush g _) = nodeCount g + 1

pushNode :: Graph node edge env -> node a -> PartialEnv (InEdge edge a) env -> PartialEnv (edge a) (env, a) -> Graph node edge (env, a)
pushNode g n i o = GPush g $ Node n i o

dropNode :: Graph node edge (env, t) -> Graph node edge env
dropNode (GPush g _) = g

insertEdge :: Idx env s -> Idx env t -> edge s t -> Graph node edge env -> Graph node edge env
insertEdge = insertEdgeWith const

-- | Inserts an edge in the graph. If the edge already exists, their labels will be combined 
insertEdgeWith :: (edge s t -> edge s t -> edge s t) -> Idx env s -> Idx env t -> edge s t -> Graph node edge env -> Graph node edge env
insertEdgeWith f i1 i2 edge (GPush g node) = case (i1, i2) of
  (SuccIdx j1, SuccIdx j2) -> insertEdgeWith f j1 j2 edge g `GPush` node
  (ZeroIdx   , _)
    | Node n i o <- node -> GPush g $ Node n i $ partialUpdateWith f edge i2 o
  (SuccIdx j1, ZeroIdx)
    | Node n i o <- node -> GPush g $ Node n (partialUpdateWith f' (InEdge edge) j1 i) o
  where
    f' (InEdge e1) (InEdge e2) = InEdge $ f e1 e2
insertEdgeWith _ i1 _ _ GEmpty = case i1 of {}

insertEdgesFromWith
  :: forall node edge env s'.
     (forall s t. edge s t -> edge s t -> edge s t) -- Combine with existing edge, if needed
  -> Idx env s' -- Starting point
  -> PartialEnv (edge s') env -- End points
  -> Graph node edge env
  -> Graph node edge env
insertEdgesFromWith f from = insertCartesianEdgesWith
  f
  (\Refl edge -> edge)
  (partialEnvSingleton from Refl :: PartialEnv ((:~:) s') env)

insertEdgesToWith
  :: forall node edge env t'.
     (forall s t. edge s t -> edge s t -> edge s t) -- Combine with existing edge, if needed
  -> PartialEnv (InEdge edge t') env -- Start points
  -> Idx env t' -- End point
  -> Graph node edge env
  -> Graph node edge env
insertEdgesToWith f from to = insertCartesianEdgesWith
  f
  (\(InEdge edge) Refl -> edge)
  from
  (partialEnvSingleton to Refl :: PartialEnv ((:~:) t') env)

-- Given two partial environments, adds 
insertCartesianEdgesWith
  :: (forall s t. edge s t -> edge s t -> edge s t) -- Combine with existing edge, if needed
  -> (forall s t. from s -> to t -> edge s t) -- Construct the new edge
  -> PartialEnv from env -- Starting points of edges
  -> PartialEnv to env -- End points of edges
  -> Graph node edge env
  -> Graph node edge env
insertCartesianEdgesWith _ _ PEnd _ graph = graph
insertCartesianEdgesWith _ _ _ PEnd graph = graph
insertCartesianEdgesWith f edge (PPush starts start) (PPush ends end) (GPush graph (Node n i o))
  | i' <- unionPartialEnv (\(InEdge a) (InEdge b) -> InEdge $ f a b) i $ mapPartialEnv (\s -> InEdge $ edge s end) starts
  , o' <- unionPartialEnv f o $ PNone $ mapPartialEnv (edge start) ends
  = insertCartesianEdgesWith f edge starts ends graph `GPush` Node n i' o'
insertCartesianEdgesWith f edge (PPush starts start) (PNone ends) (GPush graph (Node n i o))
  | o' <- unionPartialEnv f o $ PNone $ mapPartialEnv (edge start) ends
  = insertCartesianEdgesWith f edge starts ends graph `GPush` Node n i o'
insertCartesianEdgesWith f edge (PNone starts) (PPush ends end) (GPush graph (Node n i o))
  | i' <- unionPartialEnv (\(InEdge a) (InEdge b) -> InEdge $ f a b) i $ mapPartialEnv (\s -> InEdge $ edge s end) starts
  = insertCartesianEdgesWith f edge starts ends graph `GPush` Node n i' o
insertCartesianEdgesWith f edge (PNone starts) (PNone ends) (GPush graph node) =
  insertCartesianEdgesWith f edge starts ends graph `GPush` node

removeEdgesOf :: Idx env s -> Graph node edge env -> Graph node edge env
removeEdgesOf ZeroIdx (GPush graph (Node n _ _))
  = GPush graph $ Node n PEnd PEnd
removeEdgesOf (SuccIdx idx) (GPush graph (Node n i o))
  = removeEdgesOf idx graph `GPush` Node n (partialRemove idx i) (partialRemove (SuccIdx idx) o)

out :: Graph node edge env -> Idx env s -> PartialEnv (edge s) env
out (GPush g (Node _ i _)) (SuccIdx idx) = case prjPartial idx i of
  Nothing -> partialEnvSkip $ out g idx
  Just (InEdge edge) -> out g idx `PPush` edge
out (GPush _ (Node _ _ o)) ZeroIdx = o
out GEmpty idx = case idx of {}

inn :: Graph node edge env -> Idx env t -> PartialEnv (InEdge edge t) env
inn (GPush g (Node _ _ o)) (SuccIdx idx) = case prjPartial (SuccIdx idx) o of
  Nothing -> partialEnvSkip $ inn g idx
  Just edge -> inn g idx `PPush` InEdge edge
inn (GPush _ (Node _ i _)) ZeroIdx = partialEnvSkip i
inn GEmpty idx = case idx of {}

prjNode :: Graph node edge env -> Idx env t -> node t
prjNode (GPush g (Node n _ _)) = \case
  ZeroIdx -> n
  SuccIdx idx -> prjNode g idx
prjNode GEmpty = \case {}

prjEdge :: Graph node edge env -> Idx env s -> Idx env t -> Maybe (edge s t)
prjEdge (GPush g _) (SuccIdx s) (SuccIdx t) = prjEdge g s t
prjEdge (GPush _ (Node _ _ o)) ZeroIdx t = prjPartial t o
prjEdge (GPush _ (Node _ i _)) (SuccIdx s) ZeroIdx = case prjPartial s i of
  Just (InEdge edge) -> Just edge
  Nothing -> Nothing
prjEdge GEmpty s _ = case s of {}

updateNode :: Idx env t -> (node t -> node t) -> Graph node edge env -> Graph node edge env
updateNode ZeroIdx f (GPush g (Node n i o)) = GPush g $ Node (f n) i o
updateNode (SuccIdx idx) f (GPush g node) = updateNode idx f g `GPush` node

shortestPath
  :: (Show dist, Num dist, Ord dist)
  => (forall a b. edge a b -> dist)
  -> Graph node edge env
  -> Idx env s
  -> Idx env t
  -> Maybe dist
shortestPath edgeDist graph from to = fmap getConst $ prjPartial to dists
  where
    (_, dists, _) = shortestPathGeneric From (const Nothing) edgeDist graph from

shortestPathLessThanEqual
  :: (Show dist, Num dist, Ord dist)
  => (forall a b. edge a b -> dist)
  -> Graph node edge env
  -> Idx env s
  -> Idx env t
  -> dist
  -> Bool
shortestPathLessThanEqual edgeDist graph from to dist = isJust res
  where
    (res, _, _) = shortestPathGeneric From earlyExit edgeDist graph from
    earlyExit dists = case prjPartial to dists of
      Just (Const d)
        | d <= dist -> Just ()
      _ -> Nothing

shortestPathsFrom
  :: (Show dist, Num dist, Ord dist)
  => (forall a b. edge a b -> dist)
  -> Graph node edge env
  -> Idx env s
  -> PartialEnv (Const dist) env
shortestPathsFrom edgeDist graph from = dists
  where
    (_, dists, _) = shortestPathGeneric From (const Nothing) edgeDist graph from

shortestPathsTo
  :: (Show dist, Num dist, Ord dist)
  => (forall a b. edge a b -> dist)
  -> Graph node edge env
  -> Idx env s
  -> PartialEnv (Const dist) env
shortestPathsTo edgeDist graph to = dists
  where
    (_, dists, _) = shortestPathGeneric To (const Nothing) edgeDist graph to

type HasNegativeCycle = Bool

data StartPoint = From | To

-- | Generic implementation of the shortest path algorithm, used for
-- shortestPath, shortestPathsFrom and shortestPathGlobalFrom.
-- We use Bellman-Ford, to support negative cycles.
shortestPathGeneric
  :: forall dist node edge env res s.
     (Show dist, Num dist, Ord dist)
  => StartPoint
  -> (PartialEnv (Const dist) env -> Maybe res) -- Early exit check
  -> (forall a b. edge a b -> dist)
  -> Graph node edge env
  -> Idx env s
  -> (Maybe res, PartialEnv (Const dist) env, HasNegativeCycle)
shortestPathGeneric startPoint earlyExit edgeDist graph startIdx =
  loop (nodeCount graph) (partialEnvSingleton startIdx (Const 0))
  where
    loop :: Int -> PartialEnv (Const dist) env -> (Maybe res, PartialEnv (Const dist) env, HasNegativeCycle)
    -- If the tentative distances didn't stabilize after 'nodeCount graph' iterations, the graph has a negative cycle.
    loop 0 dists = (Nothing, dists, True)
    loop iters dists
      | Just res <- earlyExit dists' = (Just res, dists', False)
      | distancesEq dists dists' = (Nothing, dists', False)
      | otherwise = loop (iters - 1) dists'
      where
        dists' = case startPoint of
          From -> shortestPathFromStep edgeDist graph dists
          To   -> shortestPathToStep   edgeDist graph dists

-- | One iteration of Bellman-Ford for shortestPathGeneric when start = From 
shortestPathFromStep
  :: forall dist node edge env.
     (Show dist, Num dist, Ord dist)
  => (forall a b. edge a b -> dist)
  -> Graph node edge env
  -> PartialEnv (Const dist) env
  -> PartialEnv (Const dist) env
shortestPathFromStep _ GEmpty _ = PEnd
shortestPathFromStep dist (GPush g (Node _ ins outs)) dists1 = dists4
  where
    -- Update our own distance
    paths :: [dist]
    paths = map (\(EnvBinding _ (Const d)) -> d)
      $ partialEnvToList
      -- Combine all nodes with their edge to the current node
      $ intersectPartialEnv (\(Const d) (InEdge edge) -> Const $ d + dist edge) (partialEnvTail dists1) ins

    own = minimum' (partialEnvLast dists1) paths

    -- Update distances based on outgoing edges out of this node
    dists2 = case own of
      Nothing -> dists1
      Just (Const d) ->
        unionPartialEnv (\(Const a) (Const b) -> Const $ min a b) dists1
          $ mapPartialEnv
            (\edge -> Const $ d + dist edge)
            outs

    -- Recursion
    dists3 = shortestPathFromStep dist g (partialEnvTail dists2)

    dists4 = partialEnvPush dists3 own

-- | One iteration of Bellman-Ford for shortestPathGeneric when start = To
shortestPathToStep
  :: forall dist node edge env.
     (Show dist, Num dist, Ord dist)
  => (forall a b. edge a b -> dist)
  -> Graph node edge env
  -> PartialEnv (Const dist) env
  -> PartialEnv (Const dist) env
shortestPathToStep _ GEmpty _ = PEnd
shortestPathToStep dist (GPush g (Node _ ins outs)) dists1 = dists4
  where
    -- Update our own distance
    paths :: [dist]
    paths = map (\(EnvBinding _ (Const d)) -> d)
      $ partialEnvToList
      -- Combine all nodes with their edge to the current node
      $ intersectPartialEnv (\(Const d) edge -> Const $ d + dist edge) dists1 outs

    own = minimum' (partialEnvLast dists1) paths

    -- Update distances based on outgoing edges out of this node
    dists2 = case own of
      Nothing -> partialEnvTail dists1
      Just (Const d) ->
        unionPartialEnv (\(Const a) (Const b) -> Const $ min a b) (partialEnvTail dists1)
          $ mapPartialEnv
            (\(InEdge edge) -> Const $ d + dist edge)
            ins

    -- Recursion
    dists3 = shortestPathToStep dist g dists2

    dists4 = partialEnvPush dists3 own

distancesEq :: Eq dist => PartialEnv (Const dist) env -> PartialEnv (Const dist) env -> Bool
distancesEq PEnd         PEnd         = True
distancesEq (PPush as a) (PPush bs b) = a == b && distancesEq as bs
distancesEq (PNone as  ) (PNone bs  ) = distancesEq as bs
distancesEq (PNone as  ) PEnd         = distancesEq as PEnd
distancesEq PEnd         (PNone bs  ) = distancesEq PEnd bs
distancesEq _            _            = False

minimum' :: Ord dist => Maybe (Const dist t) -> [dist] -> Maybe (Const dist t)
minimum' m [] = m
minimum' Nothing ds = Just $ Const $ minimum ds
minimum' (Just (Const d)) ds = Just $ Const $ min d $ minimum ds
