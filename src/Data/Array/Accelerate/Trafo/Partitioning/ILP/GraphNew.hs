{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE InstanceSigs #-}
module Data.Array.Accelerate.Trafo.Partitioning.ILP.GraphNew where

import Data.Array.Accelerate.Trafo.Partitioning.ILP.LabelsNew

import Prelude hiding (reads)

import Lens.Micro
import Lens.Micro.TH
import Lens.Micro.Extras

import Data.Set (Set)
import qualified Data.Set as S

import Data.Map (Map)
import qualified Data.Map as M


-- | Fusible computations @c1 -> b -> c2@.
type   Fusible = (Label Comp, Label Buff, Label Comp)
-- | Infusible computations @c1 -> b -> c2@.
type Infusible = (Label Comp, Label Buff, Label Comp)
-- | In-place updateable buffers @b1 -> c1 -> ... -> c2 -> b2@.
type Inplace   = (Label Buff, Label Comp, Label Comp, Label Buff)

-- | Program graph in adjacency list representation.
--
-- The program graph is a directed graph in which a node is either a computation
-- or a buffer. Edges between buffers and computations represent the data flow
-- between them.
-- In addition to basic data flow, the graph also contains sets of fusible-,
-- infusible- and in-place updateable edges. These sets are used to guide the
-- clustering process.
--
data Graph = Graph   -- TODO: Maybe use hashmaps and hashsets in production?
  {      _readEdges :: Map (Label Buff) (Set (Label Comp))
  ,     _writeEdges :: Map (Label Comp) (Set (Label Buff))
  ,   _fusibleEdges :: Set Fusible
  , _infusibleEdges :: Set Infusible
  ,   _inplaceEdges :: Set Inplace
  }

makeLenses ''Graph

instance Semigroup Graph where
  (<>) :: Graph -> Graph -> Graph
  g1 <> g2 = Graph
    {      _readEdges = M.unionWith (<>)  (_readEdges g1)  (_readEdges g2)
    ,     _writeEdges = M.unionWith (<>) (_writeEdges g1) (_writeEdges g2)
    ,   _fusibleEdges =   _fusibleEdges g1 <>   _fusibleEdges g2
    , _infusibleEdges = _infusibleEdges g1 <> _infusibleEdges g2
    ,   _inplaceEdges =   _inplaceEdges g1 <>   _inplaceEdges g2
    }

instance Monoid Graph where
  mempty :: Graph
  mempty = Graph mempty mempty mempty mempty mempty

-- | Singleton graph in which a computation reads from a buffer.
--
-- The buffer needs to be in scope, i.e. its parent must be an ancestor of the
-- computation.
-- An edge is added to all ancestors of the computation until the buffer becomes
-- out of scope.
--
-- The current implementation assumes all ancestors are unique.
--
reads :: Label Comp -> Label Buff -> Graph
reads c b = if c ^. parent == b ^. parent
  then mempty & readEdges <>~ M.singleton b (S.singleton c)
  else case c ^. parent of
    Just p  -> reads p b & readEdges <>~ M.singleton b (S.singleton p)
    Nothing -> error "reads: Buffer is out of scope."

-- | Singleton graph in which a computation writes to a buffer.
--
-- See 'reads' for the scoping rules.
--
writes :: Label Comp -> Label Buff -> Graph
writes c b = if c ^. parent == b ^. parent
  then mempty & writeEdges <>~ M.singleton c (S.singleton b)
  else case c ^. parent of
    Just p  -> writes p b & writeEdges <>~ M.singleton p (S.singleton b)
    Nothing -> error "writes: Buffer is out of scope."
