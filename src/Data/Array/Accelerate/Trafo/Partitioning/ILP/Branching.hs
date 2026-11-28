module Data.Array.Accelerate.Trafo.Partitioning.ILP.Branching
  ( greedyFusionLeaf
  )
where

import Data.Array.Accelerate.Trafo.Partitioning.ILP.ConstraintLanguage (Constraint (..))
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Presolve (Problem (..), assume)
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Var (Var (Fused))
import Data.Either (rights)
import Data.List (minimumBy)
import Data.Ord (comparing)
import Data.Set qualified as S

-- | Follow the most promising presolver-guided fusion branch until every
-- fusion decision has been made. Returns 'Nothing' if every choice is
-- infeasible.
greedyFusionLeaf :: Problem -> Maybe Problem
greedyFusionLeaf problem =
  case chooseBranches problem of
    Nothing ->
      Just problem
    Just [] ->
      Nothing
    Just children ->
      greedyFusionLeaf $ minimumBy (comparing childScore) children
  where
    childScore child = (unresolvedFusionCount child, length (constraints child))

chooseBranches :: Problem -> Maybe [Problem]
chooseBranches problem =
  case fusionBranchCandidates problem of
    [] ->
      Nothing
    candidates ->
      Just . snd . minimumBy (comparing fst) $ map evaluateCandidate candidates
  where
    evaluateCandidate variable =
      let children = rights [assume variable 0 problem, assume variable 1 problem]
       in (branchScore children, children)

branchScore :: [Problem] -> (Int, Int, Int)
branchScore children =
  ( length children,
    sum $ map unresolvedFusionCount children,
    sum $ map (length . constraints) children
  )

unresolvedFusionCount :: Problem -> Int
unresolvedFusionCount Problem {constraints} =
  length [() | ClusterBeforeUnlessFused _ _ <- constraints]

fusionBranchCandidates :: Problem -> [Var]
fusionBranchCandidates Problem {constraints} =
  S.toList . S.fromList $ [Fused i j | ClusterBeforeUnlessFused i j <- constraints]
