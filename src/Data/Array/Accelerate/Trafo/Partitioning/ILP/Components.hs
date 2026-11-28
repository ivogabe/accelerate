module Data.Array.Accelerate.Trafo.Partitioning.ILP.Components (solveOptimalSplit, solveOptimalWithSplitWithReport, componentSizes) where

import Control.Monad.State (evalState)
import Data.Array.Accelerate.Trafo.Partitioning.ILP.ConstraintLanguage (Constraint)
import Data.Array.Accelerate.Trafo.Partitioning.ILP.CustomSolver (CompletionError (..), FeasibleSolution (..), solveOptimal)
import Data.Array.Accelerate.Trafo.Partitioning.ILP.LinearConstraint (Bounds (..), Constants (nComps), Expression (..), IsNumber (..), LinearConstraint (..), Number (..))
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Lower (LowerEnv (..), lower, lowerAll)
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Presolve (Problem (..), ResolvedValue (..), assumeAll, emptySubstitution, knownValue, resolveVar, substituteBounds, substituteExpression, substituteLinearConstraint)
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Solver (ILP (..), OptDir (..), allVars, varsBounds, varsConstr, varsExpr)
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Var (Var (..))
import Data.Foldable
import Data.Graph.Inductive.Graph qualified as G
import Data.Graph.Inductive.PatriciaTree (Gr)
import Data.Graph.Inductive.Query qualified as DFS
import Data.Map qualified as M
import Data.Maybe (mapMaybe)
import Data.Set qualified as S

representatives :: Problem -> S.Set Var -> S.Set Var
representatives problem variables =
  S.fromList
    [ representative
    | variable <- S.toList variables,
      Representative representative <- [resolveVar problem variable]
    ]

belongs :: Problem -> S.Set Var -> Var -> Bool
belongs problem group variable = case resolveVar problem variable of
  Representative repr -> repr `S.member` group
  Known _ -> False

semantic :: Var -> Bool
semantic Other {} = False
semantic _ = True

connect :: S.Set Var -> [S.Set Var] -> [S.Set Var]
connect vertices dependencies = map variablesForNodes (DFS.components graph)
  where
    allVertices = S.unions (vertices : dependencies)

    nodes = zip [0 ..] (S.toList allVertices)

    nodeIds = M.fromList [(variable, nodeId) | (nodeId, variable) <- nodes]

    edges = concatMap dependencyEdges dependencies

    dependencyEdges variables = case mapMaybe (`M.lookup` nodeIds) (S.toList variables) of
      [] -> []
      first : rest -> concat [[(first, node, ()), (node, first, ())] | node <- rest]

    graph :: Gr Var ()
    graph = G.mkGraph nodes edges

    variablesForNodes nodesInComponent = S.fromList $ mapMaybe (G.lab graph) nodesInComponent

domainBatches :: Constants -> [Constraint] -> [(LinearConstraint, Bounds, Expression)]
domainBatches constants constraints =
  evalState
    (traverse (lower (LowerEnv (nComps constants))) constraints)
    ""

batchDependencies :: Problem -> (LinearConstraint, Bounds, Expression) -> S.Set Var
batchDependencies problem (linear, bounds, objective) =
  representatives problem $
    varsConstr linear <> varsBounds bounds <> varsExpr objective

linearAtoms :: LinearConstraint -> [LinearConstraint]
linearAtoms (left :&& right) = linearAtoms left <> linearAtoms right
linearAtoms TrueConstraint = []
linearAtoms row = [row]

boundAtoms :: Bounds -> [Bounds]
boundAtoms (left :<> right) = boundAtoms left <> boundAtoms right
boundAtoms NoBounds = []
boundAtoms bound = [bound]

discoverComponents :: (Problem -> ILP) -> S.Set Var -> Problem -> [S.Set Var]
discoverComponents lowerProblem originalVariables problem =
  connect vertices dependencies
  where
    ilp@(ILP _ _ linear bounds constants) = lowerProblem problem

    batches = domainBatches constants $ constraints problem

    batchVariables =
      S.unions
        [ varsConstr batchLinear <> varsBounds batchBounds <> varsExpr batchObjective
        | (batchLinear, batchBounds, batchObjective) <- batches
        ]

    vertices = representatives problem $ originalVariables <> allVars ilp <> batchVariables

    dependencies =
      map (batchDependencies problem) batches
        <> map (representatives problem . varsConstr) (linearAtoms linear)
        <> map (representatives problem . varsBounds) (boundAtoms bounds)

prepare :: (Problem -> ILP) -> Problem -> Maybe Problem
prepare lowerProblem problem =
  either (const Nothing) Just $
    assumeAll assignments problem
  where
    ILP _ _ _ bounds _ = lowerProblem problem

    assignments =
      [ (variable, lo)
      | LowerUpper lo variable hi <- boundAtoms bounds,
        semantic variable,
        lo == hi
      ]

componentSizes :: (Problem -> ILP) -> S.Set Var -> Problem -> [Int]
componentSizes lowerProblem originalVariables problem =
  case prepare lowerProblem problem of
    Nothing -> []
    Just prepared -> maybe [] (map S.size) $ components lowerProblem originalVariables prepared

expressionTerms :: Constants -> Problem -> Expression -> (Int, M.Map Var Int)
expressionTerms constants problem = go
  where
    go (Constant (Number coefficient)) = (coefficient constants, M.empty)
    go (left :+ right) =
      let (leftConst, leftVars) = go left
          (rightConst, rightVars) = go right
       in (leftConst + rightConst, M.unionWith (+) leftVars rightVars)
    go (Number coefficient :* variable) = case resolveVar problem variable of
      Representative representative -> (0, M.singleton representative (coefficient constants))
      Known value -> (coefficient constants * value, M.empty)

rowKey :: Constants -> LinearConstraint -> (Int, Int, M.Map Var Int)
rowKey constants row =
  case row of
    left :>= right -> key 0 left right
    left :<= right -> key 1 left right
    left :== right -> key 2 left right
    _ -> (3, 0, M.empty)
  where
    key relation left right =
      let emptyProblem = Problem [] emptySubstitution
          (leftConstant, leftTerms) = expressionTerms constants emptyProblem left
          (rightConstant, rightTerms) = expressionTerms constants emptyProblem right
          coefficients = M.unionWith (+) leftTerms (M.map negate rightTerms)
       in (relation, leftConstant - rightConstant, M.filter (/= 0) coefficients)

components :: (Problem -> ILP) -> S.Set Var -> Problem -> Maybe [S.Set Var]
components lowerProblem originalVariables problem
  | direction /= Minimise = Nothing
  | not (all semantic (S.toList (varsExpr objective))) = Nothing
  | not (all semantic (S.toList (varsExpr resolvedObjective))) = Nothing
  | not (auxiliaries `S.isSubsetOf` generatedAuxiliaries) = Nothing
  | any changedAuxiliary (S.toList generatedAuxiliaries) = Nothing
  | any unknownAuxiliaryRow (linearAtoms resolvedLinear) = Nothing
  | any unknownAuxiliaryBound (boundAtoms resolvedBounds) = Nothing
  | otherwise = Just $ discoverComponents lowerProblem originalVariables problem
  where
    ilp@(ILP direction objective linear bounds constants) = lowerProblem problem

    subst = substitution problem

    resolvedObjective = substituteExpression subst objective
    resolvedLinear = substituteLinearConstraint subst linear
    resolvedBounds = substituteBounds subst bounds

    batches = domainBatches constants $ constraints problem
    (domainLinear, domainBounds, _) = mconcat batches

    generatedVariables = varsConstr domainLinear <> varsBounds domainBounds

    auxiliaries = S.filter (not . semantic) $ allVars ilp <> originalVariables

    generatedAuxiliaries = S.filter (not . semantic) generatedVariables

    generatedRows = S.fromList $ map (rowKey constants) $ linearAtoms $ substituteLinearConstraint subst domainLinear

    generatedBounds = S.fromList $ map show $ boundAtoms $ substituteBounds subst domainBounds

    changedAuxiliary variable = resolveVar problem variable /= Representative variable

    unknownAuxiliaryRow row =
      not (all semantic (S.toList (varsConstr row))) && rowKey constants row `S.notMember` generatedRows

    unknownAuxiliaryBound bound =
      not (all semantic (S.toList (varsBounds bound))) && show bound `S.notMember` generatedBounds

componentProblem :: Problem -> [(Constraint, S.Set Var)] -> S.Set Var -> Problem
componentProblem root dependencies group =
  root {constraints = [constraint | (constraint, variables) <- dependencies, variables `S.isSubsetOf` group]}

constraintDependencies :: Constants -> Problem -> [(Constraint, S.Set Var)]
constraintDependencies constants problem =
  zip
    (constraints problem)
    (map (batchDependencies problem) batches)
  where
    batches = domainBatches constants $ constraints problem

componentVariables :: Problem -> S.Set Var -> S.Set Var -> S.Set Var
componentVariables root originalVariables group =
  S.filter
    (\variable -> semantic variable && belongs root group variable)
    originalVariables

lowerComponent :: ILP -> Problem -> S.Set Var -> Problem -> ILP
lowerComponent (ILP direction objective linear bounds constants) root group problem =
  ILP
    direction
    (substituteExpression subst projectedObjective)
    (substituteLinearConstraint subst (localLinear <> projectedRows))
    (substituteBounds subst (localBounds <> projectedBounds))
    constants
  where
    subst = substitution problem

    (localLinear, localBounds, _) = lowerAll (LowerEnv (nComps constants)) $ constraints problem

    (_, coefficients) = expressionTerms constants root objective

    projectedObjective =
      foldMap
        (\(variable, coefficient) -> int coefficient :* variable)
        [(variable, coefficient) | (variable, coefficient) <- M.toList coefficients, variable `S.member` group]

    projectedRows =
      fold
        [ row
        | row <- linearAtoms linear,
          all semantic (S.toList (varsConstr row)),
          representatives root (varsConstr row) `S.isSubsetOf` group
        ]

    projectedBounds =
      fold
        [ bound
        | bound <- boundAtoms bounds,
          all semantic (S.toList (varsBounds bound)),
          representatives root (varsBounds bound) `S.isSubsetOf` group
        ]

evaluateExpression :: Constants -> Problem -> Expression -> Maybe Int
evaluateExpression constants problem expr =
  let (constant, terms) = expressionTerms constants problem expr
   in if all (== 0) (M.elems terms)
        then Just constant
        else Nothing

validateLinear :: Constants -> Problem -> LinearConstraint -> Bool
validateLinear constants problem row =
  case row of
    left :>= right -> compareValues (>=) left right
    left :<= right -> compareValues (<=) left right
    left :== right -> compareValues (==) left right
    left :&& right -> validateLinear constants problem left && validateLinear constants problem right
    TrueConstraint -> True
  where
    compareValues op left right =
      case (evaluateExpression constants problem left, evaluateExpression constants problem right) of
        (Just leftValue, Just rightValue) -> leftValue `op` rightValue
        _ -> False

validateBound :: Problem -> Bounds -> Bool
validateBound problem bound = case bound of
  Binary variable -> check variable (\value -> value == 0 || value == 1)
  LowerUpper lo variable hi -> check variable (\value -> lo <= value && value <= hi)
  Lower lo variable -> check variable (lo <=)
  Upper variable hi -> check variable (<= hi)
  left :<> right -> validateBound problem left && validateBound problem right
  NoBounds -> True
  where
    check variable predicate = maybe False predicate (knownValue problem variable)

solveComponents :: (Problem -> ILP) -> S.Set Var -> Problem -> [S.Set Var] -> Either CompletionError FeasibleSolution
solveComponents lowerProblem originalVariables root groups = do
  results <- traverse solveGroup groups

  let merged = M.unions (map solution results)
      known = M.fromList [(variable, value) | variable <- S.toList originalVariables, semantic variable, Known value <- [resolveVar root variable]]

  completed <- either (const $ Left NoFeasibleSolution) Right $ assumeAll (M.toList (merged <> known)) root

  reconstructed <- traverse (extract completed) $ S.toList $ S.filter semantic originalVariables

  let expectedCost = constantCost + sum (map cost results)

      ILP _ completedObjective completedLinear completedBounds completedConstants = lowerProblem completed

      objectiveMatches =
        evaluateExpression constants completed objective == Just expectedCost
          && evaluateExpression completedConstants completed completedObjective == Just expectedCost

      rowsValid = semanticRowsValid constants completed linear && semanticRowsValid completedConstants completed completedLinear

      boundsValid = semanticBoundsValid completed bounds && semanticBoundsValid completed completedBounds

  if objectiveMatches && rowsValid && boundsValid
    then Right $ FeasibleSolution (M.fromList reconstructed) expectedCost
    else Left NoFeasibleSolution
  where
    rootILP@(ILP _ objective linear bounds constants) = lowerProblem root

    (constantCost, _) = expressionTerms constants root objective

    dependencies = constraintDependencies constants root

    solveGroup group =
      solveOptimal
        (lowerComponent rootILP root group)
        (componentVariables root originalVariables group)
        (componentProblem root dependencies group)

    extract problem variable = case knownValue problem variable of
      Just value -> Right (variable, value)
      Nothing -> Left $ MissingVariableValue variable

    semanticRowsValid rowConstants problem rows =
      all (validateLinear rowConstants problem) [row | row <- linearAtoms rows, all semantic (S.toList (varsConstr row))]

    semanticBoundsValid problem variableBounds =
      all (validateBound problem) [bound | bound <- boundAtoms variableBounds, all semantic (S.toList (varsBounds bound))]

solveOptimalWithSplitWithReport :: (Problem -> ILP) -> S.Set Var -> Problem -> (Bool, Either CompletionError FeasibleSolution)
solveOptimalWithSplitWithReport lowerProblem originalVariables initial =
  case prepare lowerProblem initial of
    Nothing -> unsplit
    Just root ->
      case components lowerProblem originalVariables root of
        Just groups
          | length groups > 1 ->
              case solveComponents lowerProblem originalVariables root groups of
                Right results -> (True, Right results)
                Left _ -> unsplit
        _ -> unsplit
  where
    unsplit = (False, solveOptimal lowerProblem originalVariables initial)

solveOptimalSplit :: (Problem -> ILP) -> S.Set Var -> Problem -> Either CompletionError FeasibleSolution
solveOptimalSplit lowerProblem originalVariables problem = snd $ solveOptimalWithSplitWithReport lowerProblem originalVariables problem
