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

toList :: Multimap k v -> [(k, v)]
toList (Multimap m) = [(k, v) | (k, vs) <- M.toList m, v <- S.toList vs]


foldrWithKey :: (k -> a -> b -> b) -> b -> Multimap k a -> b
foldrWithKey f z (Multimap m) = M.foldrWithKey (\k vs acc -> S.foldr (f k) acc vs) z m
{-# INLINE foldrWithKey #-}

toMapOfSets :: Multimap k v -> Map k (Set v)
toMapOfSets (Multimap m) = m
{-# INLINE toMapOfSets #-}
