module Data.Array.Accelerate.Trafo.Partitioning.ILP.DirectionDefaults where

import Data.Array.Accelerate.Trafo.Operation.Bounds.Algebra (TermBound (upper))
import Data.Array.Accelerate.Trafo.Partitioning.ILP.ConstraintLanguage (Constraint (..))
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Labels (nodeId)
import Data.Array.Accelerate.Trafo.Partitioning.ILP.LinearConstraint (Bounds (..), Constants, Expression (..), LinearConstraint (..), Number (..), nComps)
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Lower (LowerEnv (..), lowerAll)
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Presolve (Problem (..), ResolvedValue (..), assumeAll, resolveVar, substituteLinearConstraint)
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Solver (ILP (..), varsExpr)
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Var (Var (..))
import Data.Map qualified as M
import Data.Set qualified as S
import Lens.Micro ((^.))
import Prelude hiding (reads)

data Use
  = Equal [Var]
  | Pin Var Int
  | Negative Var
  | Ignore

isDirection :: Var -> Bool
isDirection ReadDir {} = True
isDirection WriteDir {} = True
isDirection _ = False

useVars :: Use -> [Var]
useVars (Equal vars) = vars
useVars (Pin var _) = [var]
useVars (Negative var) = [var]
useVars Ignore = []

uses :: Constraint -> [Use]
uses constraint = case constraint of
  FusionDirection writer buffer reader -> [Equal [WriteDir writer buffer, ReadDir buffer reader]]
  InPlaceDirection ((input, reader), (writer, output)) -> [Equal [ReadDir input reader, WriteDir writer output]]
  SameDirection reads writes -> [Equal (map (uncurry ReadDir) reads ++ map (uncurry WriteDir) writes)]
  PinnedDirection computation reads writes ->
    [ Pin variable (computation ^. nodeId)
    | variable <- map (uncurry ReadDir) reads ++ map (uncurry WriteDir) writes
    ]
  NegativeDirIfManifest (writer, buffer) -> [Negative (WriteDir writer buffer)]
  _ -> [Ignore]

connected :: M.Map Var (S.Set Var) -> S.Set Var -> [S.Set Var]
connected graph = go
  where
    go remaining = case S.minView remaining of
      Nothing -> []
      Just (root, _) ->
        let component = visit S.empty $ S.singleton root
         in component : go (remaining S.\\ component)

    visit seen pending = case S.minView pending of
      Nothing -> seen
      Just (current, rest)
        | current `S.member` seen -> visit seen rest
        | otherwise ->
            let seen' = S.insert current seen
                neighbours = M.findWithDefault S.empty current graph
                pending' = (rest <> neighbours) S.\\ seen'
             in visit seen' pending'

directionComponents :: Problem -> ([Use], [S.Set Var])
directionComponents problem = (allUses, connected adjacency vertices)
  where
    allUses = concatMap uses $ constraints problem

    representative variable = case resolveVar problem variable of
      Representative repr -> Just repr
      Known _ -> Nothing

    resolved variables = S.fromList [resolvedVar | variable <- variables, Just resolvedVar <- [representative variable]]

    vertices = resolved $ concatMap useVars allUses

    equalityGroups = [resolved vars | Equal vars <- allUses]

    adjacency = M.fromSet neighbours vertices

    neighbours variable = S.unions [group | group <- equalityGroups, variable `S.member` group]

belongsToComponent :: Problem -> S.Set Var -> Var -> Bool
belongsToComponent problem component variable = case resolveVar problem variable of
  Representative repr -> repr `S.member` component
  Known _ -> False

componentPins :: Problem -> [Use] -> S.Set Var -> S.Set Integer
componentPins problem allUses component = S.fromList (explicitPins ++ knownEndpoints)
  where
    belongs = belongsToComponent problem component

    explicitPins =
      [ toInteger value
      | Pin variable value <- allUses,
        belongs variable
      ]

    knownEndpoints =
      [ toInteger value
      | Equal variables <- allUses,
        any belongs variables,
        variable <- variables,
        Known value <- [resolveVar problem variable]
      ]

componentNeedsNegative :: Problem -> [Use] -> S.Set Var -> Bool
componentNeedsNegative problem allUses component = any needsNegative allUses
  where
    needsNegative (Negative variable) = belongsToComponent problem component variable
    needsNegative _ = False

data Interval = Interval
  { lowerBound :: Maybe Integer,
    upperBound :: Maybe Integer
  }
  deriving (Eq, Show)

instance Semigroup Interval where
  (Interval lowerA upperA) <> (Interval lowerB upperB) =
    Interval (combine max lowerA lowerB) (combine min upperA upperB)
    where
      combine _ Nothing other = other
      combine _ other Nothing = other
      combine operation (Just a) (Just b) = Just (operation a b)

boundEntries :: Bounds -> [(Var, Interval)]
boundEntries bounds = case bounds of
  Binary variable -> [(variable, Interval (Just 0) (Just 1))]
  LowerUpper lower variable upper -> [(variable, Interval (Just (toInteger lower)) (Just (toInteger upper)))]
  Lower lower variable -> [(variable, Interval (Just (toInteger lower)) Nothing)]
  Upper variable upper -> [(variable, Interval Nothing (Just (toInteger upper)))]
  left :<> right -> boundEntries left ++ boundEntries right
  NoBounds -> []

directionIntervals :: Problem -> Bounds -> M.Map Var Interval
directionIntervals problem bounds =
  M.fromListWith
    (<>)
    [ (representative, interval)
    | (variable, interval) <- boundEntries bounds,
      Representative representative <- [resolveVar problem variable]
    ]

allowed :: Interval -> Integer -> Bool
allowed (Interval lower upper) value = maybe True (<= value) lower && maybe True (value <=) upper

expression :: Constants -> Expression -> (Integer, M.Map Var Integer)
expression constants expr = case expr of
  Constant (Number coefficient) -> (toInteger (coefficient constants), M.empty)
  Number coefficient :* variable -> (0, M.singleton variable (toInteger (coefficient constants)))
  left :+ right ->
    let (leftConst, leftVars) = expression constants left
        (rightConst, rightVars) = expression constants right
     in (leftConst + rightConst, M.unionWith (+) leftVars rightVars)

type Row = (Int, Integer, M.Map Var Integer)

rows :: Constants -> LinearConstraint -> [Row]
rows constants constraint = case constraint of
  TrueConstraint -> []
  left :&& right -> rows constants left ++ rows constants right
  left :<= right -> [makeRow 0 left right]
  left :>= right -> [makeRow 0 right left]
  left :== right -> [makeRow 1 left right]
  where
    makeRow kind left right =
      let (leftConst, leftVars) = expression constants left
          (rightConst, rightVars) = expression constants right
          combinedVars = M.unionWith (+) leftVars (M.map negate rightVars)
       in (kind, leftConst - rightConst, M.filter (/= 0) combinedVars)

blockedDirections :: (Problem -> ILP) -> Problem -> S.Set Var
blockedDirections lowerProblem problem =
  S.fromList
    [ representative
    | variable <- referencedVariables,
      Representative representative <- [resolveVar problem variable]
    ]
  where
    ILP _ objective linear _ constants = lowerProblem problem

    understoodConstraints =
      [ constraint
      | constraint <- constraints problem,
        not (all (null . useVars) (uses constraint))
      ]

    (understoodLinear, _, _) = lowerAll (LowerEnv (nComps constants)) understoodConstraints

    understoodRows = S.fromList $ rows constants $ substituteLinearConstraint (substitution problem) understoodLinear

    actualRows = rows constants $ substituteLinearConstraint (substitution problem) linear

    unknownVars = [vars | row@(_, _, vars) <- actualRows, row `S.notMember` understoodRows]

    referencedVariables = S.toList (varsExpr objective) ++ concatMap M.keys unknownVars

eligibleComponent :: S.Set Var -> S.Set Var -> Bool
eligibleComponent blocked component = all isDirection (S.toList component) && S.null (component `S.intersection` blocked)

defaultDirectionAssignments :: (Problem -> ILP) -> Problem -> M.Map Var Int
defaultDirectionAssignments lowerProblem problem =
  M.fromList
    [ (variable, fromInteger value)
    | component <- components,
      eligibleComponent blocked component,
      Just value <- [chooseValue component],
      variable <- S.toList component
    ]
  where
    ILP _ _ _ bounds _ = lowerProblem problem

    (allUses, components) = directionComponents problem
    intervals = directionIntervals problem bounds
    blocked = blockedDirections lowerProblem problem

    intervalFor variable = M.findWithDefault (Interval Nothing Nothing) variable intervals

    fits component value =
      value >= toInteger (minBound :: Int)
        && value <= toInteger (maxBound :: Int)
        && all (\variable -> allowed (intervalFor variable) value) (S.toList component)

    chooseValue component =
      case S.toList (componentPins problem allUses component) of
        [value]
          | not (componentNeedsNegative problem allUses component) || value < 0 ->
              accept component value
        []
          | componentNeedsNegative problem allUses component ->
              accept component $ negativeValue component
        _ -> Nothing

    accept component value
      | fits component value = Just value
      | otherwise = Nothing

    negativeValue component =
      minimum
        ( -1
            : [ upper
              | variable <- S.toList component,
                Just upper <- [upperBound (intervalFor variable)]
              ]
        )

applyDirectionDefaults :: (Problem -> ILP) -> Problem -> Maybe Problem
applyDirectionDefaults lowerProblem problem
  | M.null assignments = Just problem
  | otherwise =
      case assumeAll (M.toList assignments) problem of
        Left _ -> Nothing
        Right defaulted -> applyDirectionDefaults lowerProblem defaulted
  where
    assignments = defaultDirectionAssignments lowerProblem problem
