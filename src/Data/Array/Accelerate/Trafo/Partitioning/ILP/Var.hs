-- | The decision variables of the fusion ILP.
module Data.Array.Accelerate.Trafo.Partitioning.ILP.Var (Var (..)) where

import Data.Array.Accelerate.Trafo.Partitioning.ILP.Labels (Comp, GVal, Node)

data Var
  -- Variables used by fusion:
  = Pi (Node Comp)
    -- ^ Used for acyclic ordering of clusters.
    -- Pi (Node x y) = z means that computation number x (possibly a subcomputation of y, see Node) is fused into cluster z (y ~ Just i -> z is a subcluster of the cluster of i)
  | Fused (Node Comp) (Node Comp)
    -- ^ 0 is fused (same cluster), 1 is unfused. We do *not* have one of these for all pairs, only the ones we need for constraints and/or costs!
    -- Invariant: Like edges, both labels have to have the same parent: Either on top (Node _ Nothing) or as sub-computation of the same label (Node _ (Just x)).
    -- In fact, this is the Var-equivalent to Edge: an infusible edge has a constraint (== 1).
  | IsManifest (Node GVal)
    -- ^ 0 means manifest, 1 is like a `delayed array`.
    -- Binary variable; will we write the output to a manifest array, or is it fused away (i.e. all uses are in its cluster)?
  | ReadDir (Node GVal) (Node Comp)
    -- ^ \-3 can't fuse with anything, -2 for 'left to right', -1 for 'right to left', n for 'unknown', see computation n (currently only backpermute).
  | WriteDir (Node Comp) (Node GVal)
    -- ^ See 'ReadDir'.
  | InFoldSize (Node Comp)  -- Legacy? Probably needs per-edge equivalent
    -- ^ Keeps track of the fold that's one dimension larger than this operation, and is fused in the same cluster.
    -- This prevents something like @zipWith f (fold g xs) (fold g ys)@ from illegally fusing
  | OutFoldSize (Node Comp)  -- Legacy? Probably needs per-edge equivalent
    -- ^ Keeps track of the fold that's one dimension larger than this operation, and is fused in the same cluster.
    -- This prevents something like @zipWith f (fold g xs) (fold g ys)@ from illegally fusing
  | Other String
    -- ^ For one-shot variables that don't deserve a constructor. These are also integer variables, and the responsibility is on the user to pick a unique name!
    -- It is possible to add a variation for continuous variables too, see `allIntegers` in MIP.hs.
    -- We currently use this in Lower.hs for cost functions.

  -- Variables introduced for in-place updates:
  | InPlace (Node GVal) (Node Comp) (Node Comp) (Node GVal)
    -- ^ 0 means in-place, 1 means not in-place. The first label is an input of a cluster, the second label is an output of a cluster.
    -- All 'InPlace' variables need to be unique, so we can't omit the computation labels. Taking one path through a cluster is different from taking another.
  | PiMax (Node GVal)
    -- ^ The cluster number of the largest reader of the buffer, since in-place updates are only allowed on the final consumer of an array/buffer.
  | MaxCluster
    -- ^ Upper bound on the larget 'Pi' assigned to any comptation, used by the 'NumClusters'/'Everything' objectives to approximate the cluster count.
  -- | WriteDirPiMax (Node GVal)
  --   -- ^ The write direction of the largest reader of the buffer. This is used to check that all reads of the buffer are in the same direction as the write.
  deriving (Eq, Ord, Show)
