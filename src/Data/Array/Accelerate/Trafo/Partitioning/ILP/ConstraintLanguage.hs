{-# LANGUAGE KindSignatures #-}

-- | A domain-specific language for the fusion ILP's constraints.
module Data.Array.Accelerate.Trafo.Partitioning.ILP.ConstraintLanguage (Constraint (..)) where

import Data.Array.Accelerate.Trafo.Partitioning.ILP.Labels (Comp, GVal, InplacePath, Node, ReadEdge, WriteEdge)
import Data.Kind (Type)
import Prelude hiding (pi)

-- | A property of the fusion problem, to be lowered into linear constraints.
data Constraint
  = -- | @pi i < pi j@: @i@ lands in a strictly earlier cluster than @j@.
    ClusterBefore (Node Comp) (Node Comp)
  | -- | @i@ and @j@ land in different clusters.
    DifferentCluster (Node Comp) (Node Comp)
  | -- | Iff every listed edge is fused, the buffer is not manifest.
    NotManifestIfAllFused (Node GVal) [(Node Comp, Node Comp)]
  | -- | Fused: @i@ and @j@ share a cluster. Unfused: @i@ comes strictly before @j@.
    FusibleOrder (Node Comp) (Node Comp)
  | -- | Fusing @w@ and @r@ implies that the write direction of @w@ is equal to the read direction of @r@.
    FusionDirection (Node Comp) (Node GVal) (Node Comp)
  | -- | Bounds @l@'s cluster index to be at most @maxCluster@.
    WithinClusterCount (Node Comp)
  | -- | If @p@ is in place, then the buffers must be manifest.
    OnManifestIfInPlace InplacePath
  | -- | In-place reuse requires read and write directions to be equal.
    InPlaceDirection InplacePath
  | -- | In-place use requires the read buffer to be dead by the time the write buffer is written to.
    InPlaceCluster InplacePath
  | -- | In-place use requires the reading and writing computations to land in the same cluster.
    AcrossClusterSame InplacePath
  | -- | At most one of these paths may reuse the buffer they all read from.
    AtMostOneReader [InplacePath]
  | -- | At most one of these paths may reuse the buffer they all write to.
    AtMostOneWriter [InplacePath]
  | -- | Unless one of the writers consumes this read in place, the buffer must stay live past the reading cluster.
    ReadAliveThroughWriters ReadEdge [WriteEdge]
  | -- | The @(buffer, consumer)@ edges out of one computation. Costs one per distinct cluster that reads from the buffer, so the solver is paid to fuse the consumers together.
    HorizontalReadCost [(Node GVal, Node Comp)]
  | -- | The buffer is manifest.
    Manifest (Node GVal)
  | -- | The buffer may not be used in place.
    NoInPlace (Node GVal)
  | -- | The computation reads and writes at the same fold size.
    SameFoldSize (Node Comp)
  | -- | The computation establishes a new fold size.
    NewFoldSize (Node Comp)
  | -- | If @w@ and @c@ are fused, @c@ reads at the fold size @w@ writes at.
    SameFoldSizeIfFused (Node Comp) (Node Comp)
  | -- | Every listed read and write happens in the same direction.
    SameDirection [ReadEdge] [WriteEdge]
  | -- | As 'SameDirection', but with the addition of the direction @c@.
    PinnedDirection (Node Comp) [ReadEdge] [WriteEdge]
  | -- | If the buffer is manifest, it is written in a negative direction.
    NegativeDirIfManifest WriteEdge
