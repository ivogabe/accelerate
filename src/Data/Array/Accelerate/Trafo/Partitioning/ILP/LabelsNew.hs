{-
Module      : Data.Array.Accelerate.Trafo.Partitioning.ILP.LabelsNew
Description : Labels for referencing nodes in the DataFlow graph.

This module provides the labels for referencing nodes in the DataFlow graph (DFG).
A node in the DataFlow graph is uniquely identified by it's position in the graph.
Since the graph is a nested structure, so too are the labels.
-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
module Data.Array.Accelerate.Trafo.Partitioning.ILP.LabelsNew where

import Data.Set (Set)



data LabelType = Abs  -- ^ Absolute label.
               | Rel  -- ^ Relative label.

-- | A label for referencing a node in a DataFlow graph.
-- A label uniquely identifies a node by it's position in the graph.
--
data Label (a :: LabelType) where
  -- | A base label refering to a node in the graph.
  --
  LabelBase :: Int    -- ^ The position of the node in the graph.
            -> Label a

  -- | A nested label refering to a node in a subgraph of the graph.
  --
  LabelNest :: Int        -- ^ The position of the subgraph in the graph.
            -> Label Abs  -- ^ The label of the node in the subgraph.
            -> Label a

deriving instance Show (Label a)
deriving instance Eq (Label a)

instance Ord (Label a) where
  compare (LabelBase i)   (LabelBase j)   = compare i j
  compare (LabelBase i)   (LabelNest j _) = compare i j
  compare (LabelNest i _) (LabelBase j)   = compare i j
  compare (LabelNest i l) (LabelNest j m) = case compare i j of
                                              LT -> LT
                                              GT -> GT
                                              EQ -> compare l m


type Labels (a :: LabelType) = Set (Label a)
