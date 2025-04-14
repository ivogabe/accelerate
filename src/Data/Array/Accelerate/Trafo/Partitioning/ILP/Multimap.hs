{-# LANGUAGE InstanceSigs #-}
module Data.Array.Accelerate.Trafo.Partitioning.ILP.Multimap where

import Prelude hiding (lookup)

import Data.Map (Map)
import qualified Data.Map as M

import Data.Set (Set)
import qualified Data.Set as S

--------------------------------------------------------------------------------
-- Multimap
--------------------------------------------------------------------------------

newtype Multimap k v = Multimap (Map k (Set v))
  deriving (Eq, Ord)

instance (Ord k, Ord v) => Semigroup (Multimap k v) where
  (<>) :: Multimap k v -> Multimap k v -> Multimap k v
  (<>) = union

instance (Ord k, Ord v) => Monoid (Multimap k v) where
  mempty :: Multimap k v
  mempty = empty

empty :: Multimap k v
empty = Multimap M.empty

singleton :: k -> v -> Multimap k v
singleton k v = Multimap $ M.singleton k (S.singleton v)

union :: (Ord k, Ord v) => Multimap k v -> Multimap k v -> Multimap k v
union (Multimap m1) (Multimap m2) = Multimap $ M.unionWith S.union m1 m2

insert :: (Ord k, Ord v) => k -> v -> Multimap k v -> Multimap k v
insert k v (Multimap m) = Multimap $ M.insertWith S.union k (S.singleton v) m

lookup :: (Ord k, Ord v) => k -> Multimap k v -> Set v
lookup k (Multimap m) = M.findWithDefault S.empty k m

--------------------------------------------------------------------------------
-- 2D Multimap
--------------------------------------------------------------------------------

newtype Multimap2D k1 k2 v = Multimap2D (Map k1 (Multimap k2 v))
  deriving (Eq, Ord)

instance (Ord k1, Ord k2, Ord v) => Semigroup (Multimap2D k1 k2 v) where
  (<>) :: Multimap2D k1 k2 v -> Multimap2D k1 k2 v -> Multimap2D k1 k2 v
  (<>) = union2D

instance (Ord k1, Ord k2, Ord v) => Monoid (Multimap2D k1 k2 v) where
  mempty :: Multimap2D k1 k2 v
  mempty = empty2D

empty2D :: Multimap2D k1 k2 v
empty2D = Multimap2D M.empty

singleton2D :: k1 -> k2 -> v -> Multimap2D k1 k2 v
singleton2D k1 k2 v = Multimap2D $ M.singleton k1 (singleton k2 v)

union2D :: (Ord k1, Ord k2, Ord v) => Multimap2D k1 k2 v -> Multimap2D k1 k2 v -> Multimap2D k1 k2 v
union2D (Multimap2D m1) (Multimap2D m2) = Multimap2D $ M.unionWith union m1 m2

insert2D :: (Ord k1, Ord k2, Ord v) => k1 -> k2 -> v -> Multimap2D k1 k2 v -> Multimap2D k1 k2 v
insert2D k1 k2 v (Multimap2D m) = Multimap2D $ M.insertWith union k1 (singleton k2 v) m

lookup2D :: (Ord k1, Ord k2, Ord v) => k1 -> k2 -> Multimap2D k1 k2 v -> Set v
lookup2D k1 k2 (Multimap2D m) = lookup k2 (M.findWithDefault empty k1 m)
