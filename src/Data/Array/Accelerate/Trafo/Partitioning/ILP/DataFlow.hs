{- |
Module      : Data.Array.Accelerate.Trafo.Partitioning.ILP.DataFlow
Description : Data flow analysis for partitioning of Accelerate programs.
Author      : Timo Post

This module provides the data flow analysis required for the partitioning of
Accelerate programs. The data flow analysis builds a forward, directed acyclic
graph of the data dependencies between it's nodes. The data flow graph is
represented by an adjacency list.
-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RankNTypes #-}
module Data.Array.Accelerate.Trafo.Partitioning.ILP.DataFlow where


import Data.Array.Accelerate.AST.Operation
import Data.Array.Accelerate.AST.LeftHandSide

import Data.Array.Accelerate.Trafo.Partitioning.ILP.Symbols
import Data.Array.Accelerate.Trafo.Partitioning.ILP.LabelsNew

import Data.Kind
import Data.Set (Set)
import qualified Data.Set as S

type DataFlowGraph op = [DataFlowNode op]


-- | A node in the data flow graph (DFG).
--
-- A node in the DFG represents either an operation or a buffer in the program.
-- The node stores it's own absolute label, the labels of the nodes that depend
-- on it, the symbol representing the operation or buffer, and a (possibly empty)
-- subgraph.
--
data DataFlowNode (op :: Type -> Type) = DFNode
    { _self  :: Label Abs         -- ^ The label of the node.
    , _next  :: Labels Rel        -- ^ The forward dependencies.
    , _symb  :: Symbol op         -- ^ The symbol of the node.
    , _graph :: DataFlowGraph op  -- ^ The subgraph (if any).
    }



mkDataFlowGraph :: forall op env a. ()
                => PreOpenAcc op env a
                -> DataFlowGraph op
mkDataFlowGraph (Exec op args) = undefined
mkDataFlowGraph (Return vars)  = undefined
mkDataFlowGraph (Compute exp)  = undefined
mkDataFlowGraph (Alet LeftHandSideUnit _ bnd scp) = undefined
mkDataFlowGraph (Alet lhs uniq bnd scp) = undefined
mkDataFlowGraph (Alloc shr e sh) = undefined
mkDataFlowGraph (Use e n buff) = undefined
mkDataFlowGraph (Unit var) = undefined
mkDataFlowGraph (Acond cond tacc facc) = undefined
mkDataFlowGraph (Awhile uniq cond body init) = undefined
