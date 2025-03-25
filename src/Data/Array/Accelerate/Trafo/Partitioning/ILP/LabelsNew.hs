{-
Module      : Data.Array.Accelerate.Trafo.Partitioning.ILP.LabelsNew
Description : Labels representing nodes in the graph.

This module provides the labels that represent nodes in the graph. A node can
either be a computation or a buffer.
-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE FlexibleInstances #-}
module Data.Array.Accelerate.Trafo.Partitioning.ILP.LabelsNew where

import Lens.Micro

import qualified Data.Set as S
import Data.Hashable (Hashable, hashWithSalt)
import Control.Exception (assert)

-- | Types of labels, can either refer to a computation or a buffer.
data LabelType = Comp | Buff

-- | Labels for referencing nodes.
--
-- A label uniquely identifies a node and optionally specifies the parent it
-- belongs to. A buffer node can never be a parent.
--
-- @CLabel x Nothing@ means that label @x@ is top-level.
-- @CLabel x (Just y)@ means that label @x@ is a sub-computation of label @y@.
data Label (t :: LabelType) where
  CLabel  :: Int                  -- ^ The computation label.
          -> Maybe (Label Comp)   -- ^ The parent computation.
          -> Label Comp
  BLabel  :: Int                  -- ^ The buffer label.
          -> Maybe (Label Comp)   -- ^ The parent computation.
          -> Label Buff

-- | Lens for getting and setting the label id.
labelId :: Lens' (Label t) Int
labelId f (CLabel i p) = fmap (`CLabel` p) (f i)
labelId f (BLabel i p) = fmap (`BLabel` p) (f i)

-- | Lens for getting and setting the parent label.
parent :: Lens' (Label t) (Maybe (Label Comp))
parent f (CLabel i p) = fmap (CLabel i) (f p)
parent f (BLabel i p) = fmap (BLabel i) (f p)

-- | Lens for interpreting any label as a computation label.
asCLabel :: Lens' (Label t) (Label Comp)
asCLabel f l@CLabel{} = f l
asCLabel f l = fmap (\(CLabel i p) -> l & labelId .~ i & parent .~ p)
                    (f (CLabel (l ^. labelId) (l ^. parent)))

-- | Lens for interpreting any label as a buffer label.
asBLabel :: Lens' (Label t) (Label Buff)
asBLabel f l@BLabel{} = f l
asBLabel f l = fmap (\(BLabel i p) -> l & labelId .~ i & parent .~ p)
                    (f (BLabel (l ^. labelId) (l ^. parent)))

instance Show (Label t) where
  show :: Label t -> String
  show l = "L" <> show (l ^. labelId) <> "{" <> show (l ^. parent) <> "}"

instance Eq (Label t) where
  (==) :: Label t -> Label t -> Bool
  (==) l1 l2 = (l1 ^. labelId == l2 ^. labelId) && ((l1 ^. parent == l2 ^. parent) || parentMismatch l1 l2)

instance Ord (Label t) where
  compare :: Label t -> Label t -> Ordering
  compare l1 l2 = case compare (l1 ^. labelId) (l2 ^. labelId) of
    EQ -> if (l1 ^. parent) == (l2 ^. parent) then EQ else parentMismatch l1 l2
    x  -> x

instance Hashable (Label t) where
  hashWithSalt :: Int -> Label t -> Int
  hashWithSalt s l = hashWithSalt s (l ^. labelId)

-- | Compute the nesting level of a label.
level :: Label t -> Int
level l = case l ^. parent of
  Nothing -> 0
  Just p  -> 1 + level p



type Labels t = S.Set (Label t)



data LabelEnv env where
  LabelEnvNil :: LabelEnv ()
  (:>>:)      :: Labels Buff -> LabelEnv env -> LabelEnv (t, env)

instance Semigroup (LabelEnv env) where
  (<>) :: LabelEnv env -> LabelEnv env -> LabelEnv env
  (<>) LabelEnvNil LabelEnvNil = LabelEnvNil
  (<>) (bs1 :>>: env1) (bs2 :>>: env2) = (bs1 <> bs2) :>>: (env1 <> env2)

instance Monoid (LabelEnv ()) where
  mempty :: LabelEnv ()
  mempty = LabelEnvNil

instance Show (LabelEnv env) where
  show :: LabelEnv env -> String
  show LabelEnvNil = "Nil"
  show (bs :>>: env) = show bs <> " :>>: " <> show env



-- | Error message for when parent computation labels do not match.
parentMismatch :: Label t -> Label t -> a
parentMismatch l1 l2 = error $ "parent mismatch: " <> show l1 <> " " <> show l2
