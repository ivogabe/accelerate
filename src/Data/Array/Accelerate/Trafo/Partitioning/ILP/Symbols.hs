{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
module Data.Array.Accelerate.Trafo.Partitioning.ILP.Symbols where

import Data.Array.Accelerate.Trafo.Partitioning.ILP.LabelsNew

import Data.Map (Map)

import Data.Kind


data Symbol (op :: Type -> Type) where  -- Empty for now.



-- | Mapping from labels to symbols.
type Symbols t op = Map (Label t) (Symbol op)
