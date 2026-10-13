module Data.Array.Accelerate.Trafo.Partitioning.ILP.CustomSolver
  ( FeasibleSolution (..),
    CompletionError (..),
    solveFeasible,
    solveOptimal,
    solveOptimalWithBinaryDefaults,
    solveOptimalUsing,
  )
where

import Data.Array.Accelerate.Trafo.Partitioning.ILP.BinaryDefaults (applyBinaryDefaults)
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Branching (greedyFusionLeaf)
import Data.Array.Accelerate.Trafo.Partitioning.ILP.ConstraintLanguage
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Labels (InplacePath)
import Data.Array.Accelerate.Trafo.Partitioning.ILP.LinearConstraint (Bounds (..), Constants (..), Expression (..), Number (..))
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Presolve (Problem (..), ResolvedValue (..), assume, assumeAll, knownValue, resolveVar)
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Solver (ILP (..), Solution)
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Var (Var (..))
import Data.List (minimumBy)
import Data.Map qualified as M
import Data.Maybe (catMaybes)
import Data.Ord (Down (..), comparing)
import Data.Set qualified as S

data FeasibleSolution = FeasibleSolution
  { solution :: Solution,
    cost :: Int
  }

data CompletionError
  = NoGreedyFusionPath
  | CannotDisableInPlace
  | NoFeasibleSolution
  | CyclicClusterPositions
  | InvalidFixedClusterOrder
  | CannotAssignClusterPositions
  | MissingVariableValue Var
  | CannotAssignPiMax
  | PiMaxExceedsBound
  | CannotAssignDirections
  | CannotAssignFoldSizes
  | NonConstantObjective
  deriving (Show)

chooseFusionWithoutInPlace :: S.Set Var -> Problem -> Either CompletionError Problem
chooseFusionWithoutInPlace originalVariables initialProblem = do
  fusionProblem <- case greedyFusionLeaf initialProblem of
    Nothing -> Left NoGreedyFusionPath
    Just problem -> Right problem

  let assignments = [(variable, 1) | variable@InPlace {} <- S.toList originalVariables, Representative _ <- [resolveVar fusionProblem variable]]

  case assumeAll assignments fusionProblem of
    Left _ -> Left CannotDisableInPlace
    Right completed -> Right completed

assignClusterPositions :: S.Set Var -> Problem -> Either CompletionError Problem
assignClusterPositions originalVariables problem = do
  edges <- traverse orderEdge [constraint | constraint@ClusterBefore {} <- constraints problem]

  let representatives = S.fromList [representative | variable@Pi {} <- S.toList originalVariables, Representative representative <- [resolveVar problem variable]]

      strictEdges = S.fromList (catMaybes edges)

  order <- topologicalOrder representatives strictEdges

  case assumeAll (zip order [0 ..]) problem of
    Left _ -> Left CannotAssignClusterPositions
    Right completed -> Right completed
  where
    orderEdge (ClusterBefore from to) =
      case (resolveVar problem (Pi from), resolveVar problem (Pi to)) of
        (Representative left, Representative right)
          | left == right -> Left CyclicClusterPositions
          | otherwise -> Right $ Just (left, right)
        (Known left, Known right)
          | left < right -> Right Nothing
          | otherwise -> Left InvalidFixedClusterOrder
        _ -> Left InvalidFixedClusterOrder
    orderEdge _ = Right Nothing

topologicalOrder :: S.Set Var -> S.Set (Var, Var) -> Either CompletionError [Var]
topologicalOrder vertices edges = go initialReady initialDegrees []
  where
    successors = M.fromListWith (<>) [(from, S.singleton to) | (from, to) <- S.toList edges]

    initialDegrees :: M.Map Var Int
    initialDegrees = foldl' addEdge (M.fromSet (const 0) vertices) (S.toList edges)

    addEdge degrees (_, to) = M.adjust (+ 1) to degrees

    initialReady = M.keysSet $ M.filter (== 0) initialDegrees

    go ready degrees ordered
      | S.null ready =
          if length ordered == S.size vertices
            then Right (reverse ordered)
            else Left CyclicClusterPositions
      | otherwise =
          let (vertex, readyWithoutVertex) = S.deleteFindMin ready
              nextVertices = S.toList $ M.findWithDefault S.empty vertex successors
              (ready', degree') = foldl' decrement (readyWithoutVertex, degrees) nextVertices
           in go ready' degree' (vertex : ordered)

    decrement (ready, degrees) vertex =
      let degree = M.findWithDefault 0 vertex degrees - 1
          degrees' = M.insert vertex degree degrees
          ready'
            | degree == 0 = S.insert vertex ready
            | otherwise = ready
       in (ready', degrees')

requireValue :: Problem -> Var -> Either CompletionError Int
requireValue problem variable =
  case knownValue problem variable of
    Nothing -> Left $ MissingVariableValue variable
    Just value -> Right value

inPlaceVariable :: InplacePath -> Var
inPlaceVariable ((inputBuffer, reader), (writer, outputBuffer)) =
  InPlace inputBuffer reader writer outputBuffer

assignPiMax :: Constants -> S.Set Var -> Problem -> Either CompletionError Problem
assignPiMax constants originalVariables problem = do
  assignments <- traverse assignment [buffer | PiMax buffer <- S.toList originalVariables]

  case assumeAll assignments problem of
    Left _ -> Left CannotAssignPiMax
    Right completed -> Right completed
  where
    assignment buffer = do
      readerBounds <- traverse readerBound [(readEdge, writers) | ReadAliveThroughWriters readEdge@(buffer', _) writers <- constraints problem, buffer' == buffer]
      inPlaceUpperBounds <- traverse inPlaceUpperBound [path | InPlaceCluster path@((buffer', _), _) <- constraints problem, buffer' == buffer]
      let noInPlace = any isNoInPlace (constraints problem)
          lowerBound = maximum (0 : readerBounds <> [nComps constants | noInPlace])
          upperBound = minimum (nComps constants + 5 : inPlaceUpperBounds)

      if lowerBound <= upperBound
        then Right (PiMax buffer, lowerBound)
        else Left PiMaxExceedsBound
      where
        isNoInPlace (NoInPlace buffer') = buffer' == buffer
        isNoInPlace _ = False

    readerBound (readEdge@(_, reader), writers) = do
      readerPosition <- requireValue problem (Pi reader)

      inplaceValues <- traverse (\writer -> requireValue problem (inPlaceVariable (readEdge, writer))) writers

      Right $ readerPosition + 1 - sum [1 - value | value <- inplaceValues]

    inPlaceUpperBound path@(_, (writer, _)) = do
      inPlace <- requireValue problem (inPlaceVariable path)
      if inPlace == 0
        then requireValue problem (Pi writer)
        else Right $ nComps constants + 5

assignDirections :: S.Set Var -> Problem -> Either CompletionError Problem
assignDirections originalVariables problem = do
  case assumeAll assignments problem of
    Left _ -> Left CannotAssignDirections
    Right completed -> Right completed
  where
    assignments = [(representative, -1) | representative <- S.toList . S.fromList $ [representative | variable <- S.toList originalVariables, isDirectionVariable variable, Representative representative <- [resolveVar problem variable]]]

isDirectionVariable :: Var -> Bool
isDirectionVariable ReadDir {} = True
isDirectionVariable WriteDir {} = True
isDirectionVariable _ = False

assignFoldSizes :: S.Set Var -> Problem -> Either CompletionError Problem
assignFoldSizes originalVariables problem = do
  case assumeAll assignments problem of
    Left _ -> Left CannotAssignFoldSizes
    Right completed -> Right completed
  where
    assignments = [(representative, 0) | representative <- S.toList . S.fromList $ [representative | variable <- S.toList originalVariables, isFoldSizeVariable variable, Representative representative <- [resolveVar problem variable]]]

isFoldSizeVariable :: Var -> Bool
isFoldSizeVariable InFoldSize {} = True
isFoldSizeVariable OutFoldSize {} = True
isFoldSizeVariable _ = False

extractSolution :: S.Set Var -> Problem -> Either CompletionError Solution
extractSolution originalVariables problem =
  M.fromList <$> traverse extract semanticVariables
  where
    semanticVariables = filter isSemanticVariable (S.toList originalVariables)

    extract variable = do
      value <- requireValue problem variable
      Right (variable, value)

isSemanticVariable :: Var -> Bool
isSemanticVariable Other {} = False
isSemanticVariable _ = True

evaluateCost :: (Problem -> ILP) -> Problem -> Either CompletionError Int
evaluateCost lowerProblem problem =
  let ILP _ objective _ _ constants = lowerProblem problem
   in case constantExpression constants objective of
        Nothing -> Left NonConstantObjective
        Just cost -> Right cost

constantExpression :: Constants -> Expression -> Maybe Int
constantExpression constants expression =
  case expression of
    Constant (Number value) ->
      Just $ value constants
    left :+ right ->
      (+)
        <$> constantExpression constants left
        <*> constantExpression constants right
    Number coefficient :* _ ->
      let value = coefficient constants
       in if value == 0
            then Just 0
            else Nothing

solveFeasible :: (Problem -> ILP) -> S.Set Var -> Problem -> Either CompletionError FeasibleSolution
solveFeasible lowerProblem originalVariables initialProblem = do
  withoutInPlace <- chooseFusionWithoutInPlace originalVariables initialProblem
  completeSolution lowerProblem originalVariables withoutInPlace

completeSolution :: (Problem -> ILP) -> S.Set Var -> Problem -> Either CompletionError FeasibleSolution
completeSolution lowerProblem originalVariables problem = do
  withClusters <- assignClusterPositions originalVariables problem
  completeClusteredSolution lowerProblem originalVariables withClusters

completeClusteredSolution :: (Problem -> ILP) -> S.Set Var -> Problem -> Either CompletionError FeasibleSolution
completeClusteredSolution lowerProblem originalVariables problem = do
  let ILP _ _ _ _ constants = lowerProblem problem
  withPiMax <- assignPiMax constants originalVariables problem
  withDirections <- assignDirections originalVariables withPiMax
  completed <- assignFoldSizes originalVariables withDirections
  completedSolution <- extractSolution originalVariables completed
  solutionCost <- evaluateCost lowerProblem completed
  Right $ FeasibleSolution completedSolution solutionCost

fusionCandidates :: Problem -> [Var]
fusionCandidates problem =
  S.toList . S.fromList $ [representative | ClusterBeforeUnlessFused from to <- constraints problem, Representative representative <- [resolveVar problem (Fused from to)]]

nextDecision :: S.Set Var -> Problem -> Maybe Var
nextDecision originalVariables problem =
  case chooseInPlaceByOccurrence originalVariables problem of
    Just inPlaceDecision -> Just inPlaceDecision
    Nothing -> choosFusionByOccurrence problem

branchChildren :: Var -> Problem -> [Problem]
branchChildren variable problem =
  [child | value <- [0, 1], Right child <- [assume variable value problem]]

inPlaceDecisions :: S.Set Var -> Problem -> [Var]
inPlaceDecisions originalVariables problem =
  S.toList . S.fromList $ [representative | variable@InPlace {} <- S.toList originalVariables, Representative representative <- [resolveVar problem variable]]

fusionVariables :: Constraint -> S.Set Var
fusionVariables constraint = case constraint of
  ClusterBeforeUnlessFused from to -> S.singleton $ Fused from to
  NotManifestIfAllFused _ pairs -> S.fromList [Fused from to | (from, to) <- pairs]
  FusionDirection writer _ reader -> S.singleton $ Fused writer reader
  SameFoldSizeIfFused writer consumer -> S.singleton $ Fused writer consumer
  Unfused from to -> S.singleton $ Fused from to
  _ -> S.empty

inPlaceVariables :: Constraint -> S.Set Var
inPlaceVariables constraint = case constraint of
  OnManifestIfInPlace path -> S.singleton $ inPlaceVariable path
  InPlaceDirection path -> S.singleton $ inPlaceVariable path
  InPlaceCluster path -> S.singleton $ inPlaceVariable path
  AcrossClusterSame path -> S.singleton $ inPlaceVariable path
  AtMostOneReader paths -> S.fromList $ map inPlaceVariable paths
  AtMostOneWriter paths -> S.fromList $ map inPlaceVariable paths
  ReadAliveThroughWriters readEdge writers -> S.fromList $ map (inPlaceVariable . (readEdge,)) writers
  _ -> S.empty

occurrenceCounts :: (Constraint -> S.Set Var) -> Problem -> M.Map Var Int
occurrenceCounts variableExtractor problem =
  M.fromListWith
    (+)
    [ (representative, 1)
    | constraint <- constraints problem,
      variable <- S.toList $ variableExtractor constraint,
      Representative representative <- [resolveVar problem variable]
    ]

fusionOccurrenceCounts :: Problem -> M.Map Var Int
fusionOccurrenceCounts = occurrenceCounts fusionVariables

inPlaceOccurrenceCounts :: Problem -> M.Map Var Int
inPlaceOccurrenceCounts = occurrenceCounts inPlaceVariables

chooseMostFrequent :: M.Map Var Int -> [Var] -> Maybe Var
chooseMostFrequent counts candidates =
  case candidates of
    [] -> Nothing
    _ ->
      Just $
        minimumBy
          (comparing $ \candidate -> (Down $ M.findWithDefault 0 candidate counts, candidate))
          candidates

choosFusionByOccurrence :: Problem -> Maybe Var
choosFusionByOccurrence problem = chooseMostFrequent (fusionOccurrenceCounts problem) (fusionCandidates problem)

chooseInPlaceByOccurrence :: S.Set Var -> Problem -> Maybe Var
chooseInPlaceByOccurrence originalVariables problem =
  chooseMostFrequent (inPlaceOccurrenceCounts problem) (inPlaceDecisions originalVariables problem)

betterSolution :: FeasibleSolution -> FeasibleSolution -> FeasibleSolution
betterSolution left right
  | cost right < cost left = right
  | otherwise = left

isObjectiveBinary :: Var -> Bool
isObjectiveBinary Fused {} = True
isObjectiveBinary InPlace {} = True
isObjectiveBinary IsManifest {} = True
isObjectiveBinary _ = False

objectiveLowerBound :: (Problem -> ILP) -> Problem -> Maybe Int
objectiveLowerBound lowerProblem problem = do
  (expressionBound, unresolvedCosts) <- expressionLowerBound objective
  pure $ expressionBound + atMostOnePenalty unresolvedCosts
  where
    ILP _ objective _ _ constants = lowerProblem problem

    expressionLowerBound expression = case expression of
      Constant (Number value) -> Just (value constants, M.empty)
      left :+ right -> do
        (leftBound, leftUnresolved) <- expressionLowerBound left
        (rightBound, rightUnresolved) <- expressionLowerBound right
        Just (leftBound + rightBound, M.unionWith (+) leftUnresolved rightUnresolved)
      Number coefficient :* variable ->
        let coefficientValue = coefficient constants
         in case knownValue problem variable of
              Just value -> Just (coefficientValue * value, M.empty)
              Nothing
                | isObjectiveBinary variable -> Just (min 0 coefficientValue, M.singleton variable coefficientValue)
                | otherwise -> Nothing

    atMostOnePenalty unresolvedCosts =
      maximum (0 : map groupPenalty atMostOneGroups)
      where
        atMostOneGroups =
          [paths | AtMostOneReader paths <- constraints problem]
            <> [paths | AtMostOneWriter paths <- constraints problem]

        groupPenalty paths =
          let representatives =
                S.toList . S.fromList $
                  [ representative
                  | path <- paths,
                    Representative representative <- [resolveVar problem (inPlaceVariable path)]
                  ]
              costs = [max 0 $ M.findWithDefault 0 representative unresolvedCosts | representative <- representatives]
           in sum costs - maximum (0 : costs)

fixedBoundAssignments :: Bounds -> [(Var, Int)]
fixedBoundAssignments bounds =
  case bounds of
    LowerUpper lower variable upper
      | lower == upper -> [(variable, lower)]
    left :<> right -> fixedBoundAssignments left <> fixedBoundAssignments right
    _ -> []

solveOptimal :: (Problem -> ILP) -> S.Set Var -> Problem -> Either CompletionError FeasibleSolution
solveOptimal = solveOptimalUsing Just

solveOptimalWithBinaryDefaults :: (Problem -> ILP) -> S.Set Var -> Problem -> Either CompletionError FeasibleSolution
solveOptimalWithBinaryDefaults lowerProblem = solveOptimalUsing (applyBinaryDefaults lowerProblem) lowerProblem

solveOptimalUsing :: (Problem -> Maybe Problem) -> (Problem -> ILP) -> S.Set Var -> Problem -> Either CompletionError FeasibleSolution
solveOptimalUsing prepare lowerProblem originalVariables initialProblem = do
  let ILP _ _ _ bounds _ = lowerProblem initialProblem
  boundedProblem <-
    case assumeAll (fixedBoundAssignments bounds) initialProblem of
      Left _ -> Left NoFeasibleSolution
      Right problem -> Right problem

  preparedProblem <- case prepare boundedProblem of
    Nothing -> Left NoFeasibleSolution
    Just problem -> Right problem

  initialCandidate <- solveFeasible lowerProblem originalVariables preparedProblem

  search initialCandidate preparedProblem
  where
    search :: FeasibleSolution -> Problem -> Either CompletionError FeasibleSolution
    search incumbent problem
      | shouldPrune incumbent problem = Right incumbent
      | otherwise =
          case nextDecision originalVariables problem of
            Just decision -> searchChildren incumbent (branchChildren decision problem)
            Nothing -> completeLeaf incumbent problem

    shouldPrune :: FeasibleSolution -> Problem -> Bool
    shouldPrune incumbent problem =
      case objectiveLowerBound lowerProblem problem of
        Just lowerBound -> lowerBound >= cost incumbent
        Nothing -> False

    searchChildren :: FeasibleSolution -> [Problem] -> Either CompletionError FeasibleSolution
    searchChildren incumbent [] = Right incumbent
    searchChildren incumbent (child : children) =
      case prepare child of
        Nothing -> searchChildren incumbent children
        Just preparedChild -> do
          improvedIncumbent <- search incumbent preparedChild
          searchChildren improvedIncumbent children

    completeLeaf :: FeasibleSolution -> Problem -> Either CompletionError FeasibleSolution
    completeLeaf incumbent problem =
      case completeSolution lowerProblem originalVariables problem of
        Right candidate -> Right $ betterSolution incumbent candidate
        Left PiMaxExceedsBound -> Right incumbent
        Left CannotAssignPiMax -> Right incumbent
        Left CyclicClusterPositions -> Right incumbent
        Left InvalidFixedClusterOrder -> Right incumbent
        Left CannotAssignClusterPositions -> Right incumbent
        Left completionError -> Left completionError
