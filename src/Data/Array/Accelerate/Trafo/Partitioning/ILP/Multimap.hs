{-# LANGUAGE InstanceSigs #-}
module Data.Array.Accelerate.Trafo.Partitioning.ILP.Multimap where

import Lens.Micro
import Lens.Micro.TH
import Lens.Micro.Extras

import Data.Map (Map)
import qualified Data.Map as M

import Data.Set (Set)
import qualified Data.Set as S

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

fromMap :: Map k (Set v) -> Multimap k v
fromMap = Multimap

union :: (Ord k, Ord v) => Multimap k v -> Multimap k v -> Multimap k v
union (Multimap m1) (Multimap m2) = Multimap $ M.unionWith S.union m1 m2

insert :: (Ord k, Ord v) => k -> v -> Multimap k v -> Multimap k v
insert k v (Multimap m) = Multimap $ M.insertWith S.union k (S.singleton v) m
