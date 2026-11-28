{-# LANGUAGE MultiWayIf #-}

module Data.Array.Accelerate.Trafo.Partitioning.ILP.Presolve
  ( presolve,
    ResolvedValue (..),
    Problem (..),
    resolveVar,
    knownValue,
    substitutionConstraints,
    substituteExpression,
    substituteLinearConstraint,
    substituteBounds,
    emptySubstitution,
    assume,
    assumeAll,
  )
where

import Control.Monad (foldM)
import Data.Array.Accelerate.Trafo.Partitioning.ILP.ConstraintLanguage (Constraint (..))
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Labels (InplacePath, ReadEdge, WriteEdge, nodeId)
import Data.Array.Accelerate.Trafo.Partitioning.ILP.LinearConstraint
  ( Bounds (..),
    Expression (..),
    LinearConstraint (..),
    int,
    var,
    (.==.),
  )
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Var (Var (..))
import Data.Graph.Inductive.Graph qualified as Graph
import Data.Graph.Inductive.PatriciaTree (Gr)
import Data.Graph.Inductive.Query.DFS qualified as DFS
import Data.Map qualified as M
import Data.Maybe (catMaybes, mapMaybe)
import Data.Set qualified as S
import Lens.Micro ((^.))

data Value = Const Int | Alias Var deriving (Eq, Show)

type Assignment = (Var, Value)

data Problem = Problem
  { constraints :: [Constraint],
    substitution :: Substitution
  }

data Infeasible = Conflict Var Value Value | Violated Constraint | CyclicClusterOrder [Var]

newtype Substitution = Substitution (M.Map Var Value) deriving (Show)

data ResolvedValue
  = Known Int
  | Representative Var
  deriving (Eq, Show)

emptySubstitution :: Substitution
emptySubstitution = Substitution M.empty

-- | Follow aliases to a constant or the representative variable.
lookupVar :: Var -> Substitution -> Value
lookupVar v s@(Substitution m) = case M.lookup v m of
  Nothing -> Alias v
  Just (Alias v') -> lookupVar v' s
  Just c -> c

resolveVar :: Problem -> Var -> ResolvedValue
resolveVar Problem {substitution = s} variable =
  case lookupVar variable s of
    Const c -> Known c
    Alias representative -> Representative representative

knownValue :: Problem -> Var -> Maybe Int
knownValue problem variable = case resolveVar problem variable of
  Known c -> Just c
  Representative _ -> Nothing

-- | Record an assignment to the substitution. Fails if it contradicts an existing assignment.
assign :: Assignment -> Substitution -> Either Infeasible Substitution
assign (v, val) s@(Substitution m) = case (lookupVar v s, resolve val) of
  (Const a, Const b)
    | a == b -> Right s
    | otherwise -> Left (Conflict v (Const a) (Const b))
  (Alias r, Const b) -> Right $ Substitution (M.insert r (Const b) m)
  (Const a, Alias r) -> Right $ Substitution (M.insert r (Const a) m)
  (Alias r1, Alias r2)
    | r1 == r2 -> Right s
    | otherwise -> Right $ Substitution (M.insert (max r1 r2) (Alias (min r1 r2)) m)
  where
    resolve (Const c) = Const c
    resolve (Alias v') = lookupVar v' s

instantiate :: Substitution -> Constraint -> Either Infeasible (Maybe Constraint, [Assignment])
instantiate s c = case c of
  Unfused i j -> drop' [(Fused i j, Const 1)]
  ClusterBefore i j -> case (resolve (Pi i), resolve (Pi j)) of
    (Alias a, Alias b) | a == b -> Left (Violated c)
    (Const a, Const b)
      | a < b -> drop' []
      | otherwise -> Left (Violated c)
    _ -> keep
  ClusterBeforeUnlessFused i j -> case resolve (Fused i j) of
    Const 0 -> drop' [(Pi i, Alias (Pi j))]
    Const 1 -> instantiate s (ClusterBefore i j)
    Const _ -> Left (Violated c)
    Alias _ -> case (resolve (Pi i), resolve (Pi j)) of
      (a, b) | a == b -> drop' [(Fused i j, Const 0)]
      (Const a, Const b)
        | a < b -> drop' [(Fused i j, Const 1)]
        | otherwise -> Left (Violated c)
      _ -> keep
  Manifest b -> drop' [(IsManifest b, Const 0)]
  NewFoldSize co -> drop' [(OutFoldSize co, Const (co ^. nodeId))]
  SameFoldSize co -> drop' [(InFoldSize co, Alias (OutFoldSize co))]
  SameDirection rs ws -> drop' $ aliasAll $ dirVars rs ws
  PinnedDirection co rs ws -> drop' [(v, Const (co ^. nodeId)) | v <- dirVars rs ws]
  SameFoldSizeIfFused w co -> Fused w co .=>. (InFoldSize co, OutFoldSize w)
  FusionDirection w b r -> Fused w r .=>. (WriteDir w b, ReadDir b r)
  InPlaceDirection p@(r, w) -> inPlaceVar p .=>. (uncurry ReadDir r, uncurry WriteDir w)
  AcrossClusterSame p@((_, c1), (c2, _)) -> inPlaceVar p .=>. (Pi c1, Pi c2)
  NotManifestIfAllFused b pairs ->
    let xs = map (uncurry Fused) pairs
        vals = map resolve xs
        open = [x | (x, Alias _) <- zip xs vals]
     in if
          | null pairs -> drop' []
          | Const 1 `elem` vals -> drop' [(IsManifest b, Const 0)]
          | all (== Const 0) vals -> drop' [(IsManifest b, Const 1)]
          | otherwise -> case resolve (IsManifest b) of
              Const 1 -> drop' [(x, Const 0) | x <- open]
              Const 0 | [x] <- open -> drop' [(x, Const 1)]
              Const 0 -> keep
              Const _ -> Left (Violated c)
              Alias _ -> keep
  OnManifestIfInPlace p@((b1, _), (_, b2)) ->
    case (resolve (inPlaceVar p), resolve (IsManifest b1), resolve (IsManifest b2)) of
      (Const 1, _, _) -> drop' []
      (Const 0, _, _) -> drop' [(IsManifest b1, Const 0), (IsManifest b2, Const 0)]
      (_, Const 1, _) -> drop' [(inPlaceVar p, Const 1)]
      (_, _, Const 1) -> drop' [(inPlaceVar p, Const 1)]
      (_, Const 0, Const 0) -> drop' []
      _ -> keep
  AtMostOneReader ps -> atMostOne ps
  AtMostOneWriter ps -> atMostOne ps
  NegativeDirIfManifest (w, b) -> case (resolve (IsManifest b), resolve (WriteDir w b)) of
    (Const 1, _) -> drop' []
    (_, Const d) | d < 0 -> drop' []
    (_, Const _) -> Right (Just c, [(IsManifest b, Const 1)])
    _ -> keep
  InPlaceCluster p -> case resolve (inPlaceVar p) of
    Const 1 -> drop' []
    _ -> keep
  _ -> keep
  where
    keep = Right (Just c, [])
    drop' as = Right (Nothing, as)
    resolve v = lookupVar v s
    -- \| @x@ => @a == b@. x beeing 0 means true here exceptionally.
    x .=>. (a, b) = case resolve x of
      Const 1 -> drop' []
      Const 0 -> drop' [(a, Alias b)]
      Const _ -> Left (Violated c)
      Alias _ -> case (resolve a, resolve b) of
        (va, vb) | va == vb -> drop' []
        (Const _, Const _) -> drop' [(x, Const 1)]
        _ -> keep
    -- \| At most one of the paths is used in place.
    atMostOne ps =
      let xs = map inPlaceVar ps
          vals = map resolve xs
          chosen = [x | (x, Const 0) <- zip xs vals]
          open = [x | (x, Alias _) <- zip xs vals]
       in if
            | length ps <= 1 -> drop' []
            | [x] <- chosen -> drop' [(y, Const 1) | y <- xs, y /= x]
            | not (null chosen) -> Left (Violated c)
            | length open <= 1 -> drop' []
            | otherwise -> keep

dirVars :: [ReadEdge] -> [WriteEdge] -> [Var]
dirVars rs ws = map (uncurry ReadDir) rs <> map (uncurry WriteDir) ws

aliasAll :: [Var] -> [Assignment]
aliasAll [] = []
aliasAll (v : vs) = [(w, Alias v) | w <- vs]

inPlaceVar :: InplacePath -> Var
inPlaceVar ((b1, c1), (c2, b2)) = InPlace b1 c1 c2 b2

-- | Applying constraints and assignments as long as there is progress.
apply :: [Assignment] -> Problem -> Either Infeasible Problem
apply assignments p = assignAll (substitution p) assignments >>= go (constraints p)
  where
    go cs s = do
      results <- traverse (instantiate s) cs
      let cs' = mapMaybe fst results
      s' <- assignAll s (concatMap snd results)
      if size s' == size s
        then Right (Problem cs' s')
        else go cs' s'

assignAll :: Substitution -> [Assignment] -> Either Infeasible Substitution
assignAll = foldM $ flip assign

size :: Substitution -> Int
size (Substitution m) = M.size m

-- | Presolve a set of constraints, returning either an infeasibility or a simplified problem.
presolve :: [Constraint] -> Either Infeasible Problem
presolve cs = do
  initial <- apply [] (Problem cs emptySubstitution)
  runPassesToFixpoint defaultPasses initial

assume :: Var -> Int -> Problem -> Either Infeasible Problem
assume v value = assumeAll [(v, value)]

assumeAll :: [(Var, Int)] -> Problem -> Either Infeasible Problem
assumeAll assignments problem = do
  assumed <- apply [(variable, Const value) | (variable, value) <- assignments] problem
  runPassesToFixpoint defaultPasses assumed

runPasses :: [Pass] -> Pass
runPasses passes problem = foldM (flip ($)) problem passes

runPassesToFixpoint :: [Pass] -> Pass
runPassesToFixpoint passes problem = do
  next <- runPasses passes problem >>= apply []
  if progress next == progress problem
    then Right next
    else runPassesToFixpoint passes next
  where
    progress current = (size $ substitution current, length $ constraints current)

defaultPasses :: [Pass]
defaultPasses = [noInPlace, piMaxOrder, orderComponents, orderReachability]

type Pass = Problem -> Either Infeasible Problem

type VertexMap = M.Map Var Graph.Node

data OrderGraph = OrderGraph
  { orderGraph :: Gr Var (),
    orderVertices :: VertexMap
  }

strictOrderEdges :: Problem -> [(Var, Var)]
strictOrderEdges Problem {constraints = cs, substitution = s} =
  mapMaybe edge cs
  where
    edge (ClusterBefore i j) =
      case (lookupVar (Pi i) s, lookupVar (Pi j) s) of
        (Alias from, Alias to) -> Just (from, to)
        _ -> Nothing
    edge _ = Nothing

data OrderRelation = OrderRelation
  { relationFrom :: Var,
    relationTo :: Var,
    relationStrict :: Bool
  }

orderRelations :: Problem -> [OrderRelation]
orderRelations Problem {constraints = cs, substitution = s} =
  mapMaybe relation cs
  where
    relation constraint = case constraint of
      ClusterBefore from to -> resolvedRelation True (Pi from) (Pi to)
      ClusterBeforeUnlessFused from to -> resolvedRelation False (Pi from) (Pi to)
      _ -> Nothing

    resolvedRelation strict from to =
      case (lookupVar from s, lookupVar to s) of
        (Alias fromVar, Alias toVar) -> Just $ OrderRelation fromVar toVar strict
        _ -> Nothing

buildOrderGraph :: [(Var, Var)] -> OrderGraph
buildOrderGraph edges =
  OrderGraph
    { orderGraph = Graph.mkGraph labeledNodes labeledEdges,
      orderVertices = vertexMap
    }
  where
    variables = S.toList $ S.fromList [v | (from, to) <- edges, v <- [from, to]]

    vertexMap = M.fromList $ zip variables [0 ..]

    labeledNodes = [(vertex, variable) | (variable, vertex) <- M.toList vertexMap]

    labeledEdges = [(vertexMap M.! from, vertexMap M.! to, ()) | (from, to) <- edges]

canReach :: OrderGraph -> Var -> Var -> Bool
canReach (OrderGraph g vMap) from to =
  case (M.lookup from vMap, M.lookup to vMap) of
    (Just fromVertex, Just toVertex) -> toVertex `elem` DFS.reachable fromVertex g
    _ -> False

orderComponents :: Pass
orderComponents problem@Problem {substitution = s} = do
  assignments <- concat <$> traverse inspectComponent components
  updatedSubstitution <- assignAll s assignments
  Right $ problem {substitution = updatedSubstitution}
  where
    relations = orderRelations problem

    graph = buildOrderGraph [(relationFrom r, relationTo r) | r <- relations]

    components =
      [ mapMaybe (Graph.lab $ orderGraph graph) component
      | component <- DFS.scc $ orderGraph graph,
        length component > 1
      ]

    inspectComponent component
      | any (strictInside componentSet) relations = Left $ CyclicClusterOrder component
      | otherwise = Right $ aliasComponent component
      where
        componentSet = S.fromList component

    strictInside component relation =
      relationStrict relation
        && relationFrom relation `S.member` component
        && relationTo relation `S.member` component

    aliasComponent [] = []
    aliasComponent (representative : variables) = [(v, Alias representative) | v <- variables]

orderReachability :: Pass
orderReachability p@Problem {constraints = cs, substitution = s} = do
  checkAcyclic graph
  (remaining, assignments) <- foldM inspect ([], []) cs
  s' <- assignAll s assignments
  Right $ p {constraints = reverse remaining, substitution = s'}
  where
    graph = buildOrderGraph $ strictOrderEdges p

    inspect (remaining, assignments) c@(ClusterBeforeUnlessFused i j) =
      case (lookupVar (Pi i) s, lookupVar (Pi j) s) of
        (Alias from, Alias to)
          -- A strict path from i to j exists, they can't be fused.
          | canReach graph from to -> Right (remaining, (Fused i j, Const 1) : assignments)
          -- The graph proves pi_j < pi_i, which constradicts the constraint (pi_i <= pi_j).
          | canReach graph to from -> Left (Violated c)
        _ -> Right (c : remaining, assignments)
    inspect (remaining, assignments) c@(AcrossClusterSame path@((_, c1), (c2, _))) =
      case (lookupVar (Pi c1) s, lookupVar (Pi c2) s) of
        (Alias from, Alias to)
          | from /= to, canReach graph from to || canReach graph to from -> Right (remaining, (inPlaceVar path, Const 1) : assignments)
        _ -> Right (c : remaining, assignments)
    inspect (remaining, assignments) c = Right (c : remaining, assignments)

checkAcyclic :: OrderGraph -> Either Infeasible ()
checkAcyclic OrderGraph {orderGraph = g} =
  case filter ((> 1) . length) (DFS.scc g) of
    [] -> Right ()
    component : _ -> Left $ CyclicClusterOrder $ mapMaybe (Graph.lab g) component

-- | A buffer marked 'NoInPlace' can't be the input of a selected reuse path.
noInPlace :: Pass
noInPlace problem@Problem {constraints = cs, substitution = s} = do
  updatedSubstitution <- assignAll s assignments
  Right $ problem {substitution = updatedSubstitution}
  where
    forbiddenBuffers = S.fromList [buffer | NoInPlace buffer <- cs]

    assignments = [(inPlaceVar path, Const 1) | InPlaceCluster path@((buffer, _), _) <- cs, buffer `S.member` forbiddenBuffers]

-- | A selected in-place path bounds the buffer lifetime by the writer.
-- Readers without a selected path must therefore precede that writer.
piMaxOrder :: Pass
piMaxOrder problem@Problem {constraints = cs, substitution = s} = do
  impliedOrders <- concat <$> traverse ordersForPath selectedPaths
  Right $ problem {constraints = impliedOrders <> cs}
  where
    graph = buildOrderGraph $ strictOrderEdges problem

    selectedPaths = [path | InPlaceCluster path <- cs, lookupVar (inPlaceVar path) s == Const 0]

    ordersForPath path@((buffer, _), (writer, _)) = do
      let readers = [(readEdge, writers) | ReadAliveThroughWriters readEdge@(buffer', _) writers <- cs, buffer == buffer']
      catMaybes <$> traverse (orderForReader path writer) readers

    orderForReader path writer (readEdge@(_, reader), writers)
      | all (isNotInPlace readEdge) writers =
          case (lookupVar (Pi reader) s, lookupVar (Pi writer) s) of
            (Const readerPosition, Const writerPosition)
              | readerPosition < writerPosition -> Right Nothing
              | otherwise -> Left $ Violated $ InPlaceCluster path
            (Alias readerVariable, Alias writerVariable)
              | readerVariable == writerVariable -> Left $ Violated $ InPlaceCluster path
              | canReach graph writerVariable readerVariable -> Left $ Violated $ InPlaceCluster path
              | canReach graph readerVariable writerVariable -> Right Nothing
              | otherwise -> Right $ Just $ ClusterBefore reader writer
            _ -> Right Nothing
      | otherwise = Right Nothing

    isNotInPlace readEdge writerEdge =
      lookupVar (inPlaceVar (readEdge, writerEdge)) s == Const 1

-- | Convert a substitution to a set of linear constraints.
-- This could be optimized later by actually removing variables from the constraints instead of just adding equality constraints.
substitutionConstraints :: Substitution -> LinearConstraint
substitutionConstraints (Substitution m) = foldMap row $ M.toList m
  where
    row (v, Const c) = var v .==. int c
    row (v, Alias v') = var v .==. var v'

-- | Replace variables in a linear expression with their resolved values.
substituteExpression :: Substitution -> Expression -> Expression
substituteExpression s expression = case expression of
  Constant n -> Constant n
  a :+ b -> substituteExpression s a :+ substituteExpression s b
  coefficient :* v -> case lookupVar v s of
    Const value -> Constant $ coefficient * fromIntegral value
    Alias representative -> coefficient :* representative

-- | Replace variables throughout a set of linear constraints.
substituteLinearConstraint :: Substitution -> LinearConstraint -> LinearConstraint
substituteLinearConstraint s constraint = case constraint of
  a :>= b -> substituteExpression s a :>= substituteExpression s b
  a :<= b -> substituteExpression s a :<= substituteExpression s b
  a :== b -> substituteExpression s a :== substituteExpression s b
  a :&& b -> substituteLinearConstraint s a :&& substituteLinearConstraint s b
  TrueConstraint -> TrueConstraint

-- | Transfer bounds to representative variables and remove bounds for constants.
substituteBounds :: Substitution -> Bounds -> Bounds
substituteBounds s bounds = case bounds of
  Binary v -> replaceBound v (`elem` [0, 1]) Binary
  LowerUpper lower v upper -> replaceBound v (\value -> lower <= value && value <= upper) (\representative -> LowerUpper lower representative upper)
  Lower lower v -> replaceBound v (lower <=) (Lower lower)
  Upper v upper -> replaceBound v (<= upper) (`Upper` upper)
  a :<> b -> substituteBounds s a <> substituteBounds s b
  NoBounds -> NoBounds
  where
    replaceBound v valid rebuild = case lookupVar v s of
      Alias representative -> rebuild representative
      Const value
        | valid value -> NoBounds
        | otherwise -> error $ "presolve substitution violates bound for " <> show v <> ": " <> show value
