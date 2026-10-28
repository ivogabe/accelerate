module Data.Array.Accelerate.Trafo.Partitioning.ILP.BinaryDefaults where

import Data.Array.Accelerate.Trafo.Partitioning.ILP.ConstraintLanguage (Constraint (..))
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Labels (InplacePath)
import Data.Array.Accelerate.Trafo.Partitioning.ILP.LinearConstraint (Bounds (..), Constants, Expression (..), Number (..), Var (..))
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Presolve (Problem (..), ResolvedValue (..), assumeAll, resolveVar)
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Solver (ILP (..))
import Data.Map qualified as M

data BinaryRequirement
  = RequireZero
  | RequireOne
  | RequireUnknown
  deriving (Eq)

instance Semigroup BinaryRequirement where
  RequireZero <> RequireZero = RequireZero
  RequireOne <> RequireOne = RequireOne
  _ <> _ = RequireUnknown

objectiveBinaryRequirements :: Constants -> Expression -> M.Map Var BinaryRequirement
objectiveBinaryRequirements constants expression = case expression of
  Constant _ -> M.empty
  left :+ right -> M.unionWith (<>) (objectiveBinaryRequirements constants left) (objectiveBinaryRequirements constants right)
  Number coefficient :* variable
    | isBinary variable -> case compare (coefficient constants) 0 of
        LT -> M.singleton variable RequireOne
        EQ -> M.empty
        GT -> M.singleton variable RequireZero
    | otherwise -> M.empty

constraintBinaryRequirements :: Constraint -> M.Map Var BinaryRequirement
constraintBinaryRequirements constraint = case constraint of
  ClusterBeforeUnlessFused from to -> M.singleton (Fused from to) RequireUnknown
  Unfused from to -> M.singleton (Fused from to) RequireOne
  NotManifestIfAllFused buffer pairs -> M.fromListWith (<>) ((IsManifest buffer, RequireUnknown) : [(Fused from to, RequireUnknown) | (from, to) <- pairs])
  FusionDirection writer _ reader -> M.singleton (Fused writer reader) RequireOne
  OnManifestIfInPlace path@((input, _), (_, output)) ->
    M.fromListWith
      (<>)
      [ (inPlaceVariable path, RequireOne),
        (IsManifest input, RequireZero),
        (IsManifest output, RequireZero)
      ]
  InPlaceDirection path -> M.singleton (inPlaceVariable path) RequireOne
  InPlaceCluster path -> M.singleton (inPlaceVariable path) RequireOne
  AcrossClusterSame path -> M.singleton (inPlaceVariable path) RequireOne
  AtMostOneReader paths -> M.fromListWith (<>) [(inPlaceVariable path, RequireOne) | path <- paths]
  AtMostOneWriter paths -> M.fromListWith (<>) [(inPlaceVariable path, RequireOne) | path <- paths]
  ReadAliveThroughWriters reader writers ->
    M.fromListWith (<>) [(inPlaceVariable (reader, writer), RequireUnknown) | writer <- writers]
  Manifest buffer -> M.singleton (IsManifest buffer) RequireZero
  SameFoldSizeIfFused writer reader -> M.singleton (Fused writer reader) RequireOne
  NegativeDirIfManifest (_, buffer) -> M.singleton (IsManifest buffer) RequireOne
  _ -> M.empty

allowedByBounds :: Problem -> Bounds -> Var -> Int -> Bool
allowedByBounds problem bounds var value = case bounds of
  Binary variable -> check variable (value == 0 || value == 1)
  LowerUpper lower variable upper -> check variable (lower <= value && value <= upper)
  Lower lower variable -> check variable (lower <= value)
  Upper variable upper -> check variable (value <= upper)
  left :<> right -> allowedByBounds problem left var value && allowedByBounds problem right var value
  NoBounds -> True
  where
    check variable allowed = case resolveVar problem variable of
      Representative representative
        | representative == var -> allowed
      _ -> True

defaultBinaryAssignments :: (Problem -> ILP) -> Problem -> M.Map Var Int
defaultBinaryAssignments lowerProblem problem =
  M.fromList
    [ (variable, value)
    | (variable, requirement) <- M.toList requirements,
      value <- case requirement of
        RequireZero -> [0]
        RequireOne -> [1]
        RequireUnknown -> [],
      allowedByBounds problem bounds variable value
    ]
  where
    ILP _ objective _ bounds constants = lowerProblem problem

    objectiveRequirements = objectiveBinaryRequirements constants objective

    constraintRequirements =
      foldr
        (M.unionWith (<>) . constraintBinaryRequirements)
        M.empty
        (constraints problem)

    combinedRequirements = M.unionWith (<>) objectiveRequirements constraintRequirements

    requirements =
      M.fromListWith
        (<>)
        [ (representative, requirement)
        | (variable, requirement) <- M.toList combinedRequirements,
          Representative representative <- [resolveVar problem variable],
          isBinary representative
        ]

applyBinaryDefaults :: (Problem -> ILP) -> Problem -> Maybe Problem
applyBinaryDefaults lowerProblem problem
  | M.null assignments = Just problem
  | otherwise =
      case assumeAll (M.toList assignments) problem of
        Left _ -> Nothing
        Right defaulted -> applyBinaryDefaults lowerProblem defaulted
  where
    assignments = defaultBinaryAssignments lowerProblem problem

isBinary :: Var -> Bool
isBinary Fused {} = True
isBinary InPlace {} = True
isBinary IsManifest {} = True
isBinary _ = False

inPlaceVariable :: InplacePath -> Var
inPlaceVariable ((input, reader), (writer, output)) = InPlace input reader writer output
