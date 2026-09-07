module Data.Array.Accelerate.Trafo.Partitioning.ILP.Lower (LowerEnv (..), Lower, lowerAll, lower) where

import Control.Monad (replicateM)
import Control.Monad.State (State, evalState)
import Data.Array.Accelerate.Trafo.Partitioning.ILP.ConstraintLanguage
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Graph (Var (Other), fused, inFoldSize, inplace, manifest, maxCluster, outFoldSize, pi, pimax, readDir, readDirs, writeDir, writeDirs)
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Labels (Comp, GVal, Node, nodeId)
import Data.Array.Accelerate.Trafo.Partitioning.ILP.LinearConstraint (Bounds, Expression, LinearConstraint, allB, allEqual, between, binary, impliesB, int, isEqualRangeN, lowerUpper, nCompsE, notB, packB, timesN, var, (.+.), (.-.), (.<.), (.<=.), (.==.), (.>.), (.>=.))
import Data.Array.Accelerate.Trafo.Partitioning.ILP.NameGeneration (freshName)
import Data.Foldable (fold)
import Data.Monoid (Ap (..))
import Lens.Micro ((^.))
import Prelude hiding (pi)

-- | An environment for lowering, contains the number of computations
newtype LowerEnv = LowerEnv {lowerEnvNComps :: Int}

-- | The result of lowering. Contains the generated constraints, the bounds of the variables and the cost expression.
--   State monad is used to generate fresh variable names.
type Lower op = State String (LinearConstraint op, Bounds op, Expression op)

-- | Lower a batch of 'Constraint's under one shared name supply.
lowerAll :: LowerEnv -> [Constraint op] -> (LinearConstraint op, Bounds op, Expression op)
lowerAll env constraints = evalState (mconcat <$> mapM (lower env) constraints) ""

-- | Lower a single 'Constraint'.
lower :: LowerEnv -> Constraint op -> Lower op
lower env constraint = case constraint of
  ClusterBefore i j -> pure (pi i .<. pi j, mempty, mempty)
  DifferentCluster i j -> pure (fused (i, j) .==. int 1, mempty, mempty)
  NotManifestIfAllFused b pairs -> pure (allB (map fused pairs) (notB $ manifest b), mempty, mempty)
  FusibleOrder i j -> pure (between (fused (i, j)) (pi j .-. pi i) (timesN $ fused (i, j)), mempty, mempty)
  FusionDirection w b r -> pure (isEqualRangeN (writeDir (w, b)) (readDir (b, r)) (fused (w, r)), mempty, mempty)
  WithinClusterCount l -> pure (pi l .<=. maxCluster, mempty, mempty)
  OnManifestIfInPlace p@((b1, _), (_, b2)) -> pure ((inplace p `impliesB` manifest b1) <> (inplace p `impliesB` manifest b2), mempty, mempty)
  InPlaceDirection p@(r, w) -> pure (isEqualRangeN (readDir r) (writeDir w) (inplace p), mempty, mempty)
  InPlaceCluster p@((b1, _), (c2, _)) -> pure ((pimax b1 .-. pi c2) .<=. timesN (inplace p), mempty, mempty)
  AcrossClusterSame p@((_, c1), (c2, _))
    | c1 == c2 -> pure (mempty, mempty, mempty)
    | otherwise -> pure (isEqualRangeN (pi c1) (pi c2) (inplace p), mempty, mempty)
  AtMostOneReader ps -> pure (packB 1 (map inplace ps), mempty, mempty)
  AtMostOneWriter ps -> pure (packB 1 (map inplace ps), mempty, mempty)
  ReadAliveThroughWriters r@(b1, c1) ws ->
    pure (pi c1 .+. int 1 .-. foldMap (\w -> int 1 .-. inplace (r, w)) ws .<=. pimax b1, mempty, mempty)
  HorizontalReadCost pairs -> lowerHorizontalReadCost env pairs
  Manifest b -> pure (manifest b .==. int 0, mempty, mempty)
  NoInPlace b -> pure (pimax b .>=. nCompsE, mempty, mempty)
  SameFoldSize c -> pure (inFoldSize c .==. outFoldSize c, mempty, mempty)
  NewFoldSize c -> pure (outFoldSize c .==. int (c ^. nodeId), mempty, mempty)
  SameFoldSizeIfFused w c -> pure (isEqualRangeN (inFoldSize c) (outFoldSize w) (fused (w, c)), mempty, mempty)
  SameDirection rs ws -> pure (allEqual (readDirs rs <> writeDirs ws), mempty, mempty)
  PinnedDirection c rs ws -> pure (allEqual ([int (c ^. nodeId)] <> readDirs rs <> writeDirs ws), mempty, mempty)
  NegativeDirIfManifest (w, b) -> pure (timesN (manifest b) .>. writeDir (w, b), mempty, mempty)

-- | Variables for the horizontal read cost constraint.
readOrderVar, readPiVar, readPi0Var, useVar :: State String (Var op)
readOrderVar = Other <$> freshName "ReadOrder"
readPiVar = Other <$> freshName "ReadPi"
readPi0Var = Other <$> freshName "Read0Pi"
useVar = Other <$> freshName "ReadUse"

-- | Lower 'HorizontalReadCost' constraints.
lowerHorizontalReadCost :: LowerEnv -> [(Node GVal, Node Comp)] -> Lower op
lowerHorizontalReadCost env consumers = do
  let nConsumers = length consumers
      n = lowerEnvNComps env
  readPis <- replicateM nConsumers readPiVar
  readOrders <- replicateM nConsumers readOrderVar
  (subConstraint, subBounds) <- flip foldMapM consumers $ \(buff, cons) -> do
    useVars <- replicateM nConsumers useVar
    let c =
          foldMap
            ( \(uv, rp, ro) ->
                isEqualRangeN (var rp) (pi cons) (var uv)
                  <> isEqualRangeN (var ro) (readDir (buff, cons)) (var uv)
            )
            (zip3 useVars readPis readOrders)
    pure (c <> foldl (.+.) (int 0) (map var useVars) .<=. int (nConsumers - 1), foldMap binary useVars)
  readPi0s <- replicateM nConsumers readPi0Var
  let cost = foldl (.+.) (int 0) (map var readPi0s)
      constraint' = subConstraint <> fold (zipWith (\p p0 -> var p .<=. timesN (var p0)) readPis readPi0s)
      bounds = subBounds <> foldMap (\v -> lowerUpper 0 v n) readPis <> foldMap binary readPi0s
  pure (constraint', bounds, cost)

-- | 'foldMap' with an effectful mapping function.
foldMapM :: (Foldable t, Applicative f, Monoid m) => (a -> f m) -> t a -> f m
foldMapM f = getAp . foldMap (Ap . f)
