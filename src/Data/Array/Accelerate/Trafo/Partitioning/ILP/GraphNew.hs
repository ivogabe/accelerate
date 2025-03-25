{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GADTs #-}
module Data.Array.Accelerate.Trafo.Partitioning.ILP.GraphNew where

import Data.Array.Accelerate.AST.LeftHandSide
import Data.Array.Accelerate.AST.Operation
import Data.Array.Accelerate.Backend hiding (MakesILP)
import Data.Array.Accelerate.Trafo.Partitioning.ILP.LabelsNew
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Multimap (Multimap)
import qualified Data.Array.Accelerate.Trafo.Partitioning.ILP.Multimap as MM
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Solver
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Symbols

import Prelude hiding (reads)

import Lens.Micro
import Lens.Micro.TH
import Lens.Micro.Mtl
import Lens.Micro.Extras

import Data.Set (Set)
import qualified Data.Set as S

import Data.Map (Map)
import qualified Data.Map as M
import Control.Monad.State


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
  {      _readEdges  :: Multimap (Label Buff) (Label Comp)  -- ^ Edges from buffers to computations.
  ,      _readEdges' :: Multimap (Label Comp) (Label Buff)  -- ^ Complement of '_readEdges'.
  ,     _writeEdges  :: Multimap (Label Comp) (Label Buff)  -- ^ Edges from computations to buffers.
  ,     _writeEdges' :: Multimap (Label Buff) (Label Comp)  -- ^ Complement of '_writeEdges'.
  ,   _fusibleEdges  :: Set Fusible    -- ^ Set of fusible computations.
  , _infusibleEdges  :: Set Infusible  -- ^ Set of infusible computations.
  ,   _inplaceEdges  :: Set Inplace    -- ^ Set of in-place updateable buffers.
  }

instance Semigroup Graph where
  (<>) :: Graph -> Graph -> Graph
  (<>) (Graph r1 r1' w1 w1' f1 i1 p1) (Graph r2 r2' w2 w2' f2 i2 p2) = Graph
    (r1 <> r2) (r1' <> r2') (w1 <> w2) (w1' <> w2') (f1 <> f2) (i1 <> i2) (p1 <> p2)

instance Monoid Graph where
  mempty :: Graph
  mempty = Graph mempty mempty mempty mempty mempty mempty mempty

makeLenses ''Graph

-- | Singleton graph in which a computation reads from a buffer.
--
-- The buffer needs to be in scope, i.e. its parent must be an ancestor of the
-- computation.
-- An edge is added to all ancestors of the computation until the buffer becomes
-- out of scope.
--
reads :: Label Comp -> Label Buff -> Graph
reads c b = if c ^. parent == b ^. parent
  then mempty & readEdges  %~ MM.insert b c
              & readEdges' %~ MM.insert c b
  else case c ^. parent of
    Just p  -> reads p b & readEdges  %~ MM.insert b p
                         & readEdges' %~ MM.insert p b
    Nothing -> error "reads: Buffer is out of scope."

-- | Singleton graph in which a computation writes to a buffer.
--
-- See 'reads' for the scoping rules.
--
writes :: Label Comp -> Label Buff -> Graph
writes c b = if c ^. parent == b ^. parent
  then mempty & writeEdges  %~ MM.insert c b
              & writeEdges' %~ MM.insert b c
  else case c ^. parent of
    Just p  -> writes p b & writeEdges  %~ MM.insert p b
                          & writeEdges' %~ MM.insert b p
    Nothing -> error "writes: Buffer is out of scope."



-- | All information required for making an ILP.
--
-- '_graph' is the common part of the ILP, mostly defined by the structure of
-- the program.
-- '_constr' is the set of constraints for the ILP, mostly defined by the
-- backend.
-- '_bounds' is the set of bounds on variables for the ILP, mostly defined by
-- the backend.
--
data ILPInfo op = ILPInfo
  { _graph  :: Graph          -- ^ The program graph.
  , _constr :: Constraint op  -- ^ Constraints for the ILP.
  , _bounds :: Bounds op      -- ^ Bounds for variables in the ILP.
  }

instance Semigroup (ILPInfo op) where
  (<>) :: ILPInfo op -> ILPInfo op -> ILPInfo op
  (<>) (ILPInfo g1 c1 b1) (ILPInfo g2 c2 b2) = ILPInfo (g1 <> g2) (c1 <> c2) (b1 <> b2)

instance Monoid (ILPInfo op) where
  mempty :: ILPInfo op
  mempty = ILPInfo mempty mempty mempty

makeLenses ''ILPInfo



class (ShrinkArg (BackendClusterArg op), Eq (BackendVar op), Ord (BackendVar op), Eq (BackendArg op), Show (BackendArg op), Ord (BackendArg op), Show (BackendVar op)) => MakesILP op where
  mkGraph :: op args -> a -> Graph



-- | State for the full graph construction.
--
-- The graph is constructed inside the state monad by inserting edges into it.
-- The state also contains the symbols needed for reconstruction of the AST and
-- the current computation label.
--
-- Computations labels and buffer labels should always be unique, so we only use
-- one counter for the computation labels and provide lenses for interpreting
-- them as buffer labels.
-- Since all labels are unique, we can use a single symbol map for all labels
-- instead of separate maps for computation and buffer labels.
--
-- The result of the full graph construction is reserved for the return values
-- of nodes in the program, which are generally buffer labels.
-- This method makes defining the control flow easier since we do not need to
-- worry about merging the graphs in the return values as in the old approach.
--
-- The environment is passed as an argument to 'mkFullGraph' and is not part of
-- the state. This is because the environment only modified by the 'Alet'
-- constructor, which is handled by 'mkFullGraph' itself.
--
data FullGraphState op = FullGraphState
  { _ilpInfo :: ILPInfo op       -- ^ The ILP information.
  , _symbols :: Symbols Comp op  -- ^ The symbols for the ILP.
  , _currCL  :: Label Comp       -- ^ The current computation label.
  }

makeLenses ''FullGraphState

-- | Lens for interpreting the current computation label as a buffer label.
currBL :: Lens' (FullGraphState op) (Label Buff)
currBL = currCL . asBLabel

-- | Fresh computation label.
freshCL :: State (FullGraphState op) (Label Comp)
freshCL = currCL <%= (labelId +~ 1)

-- | Fresh buffer label.
freshBL :: State (FullGraphState op) (Label Buff)
freshBL = currBL <%= (labelId +~ 1)


mkFullGraph :: forall op env a. (MakesILP op)
            => PreOpenAcc op env a
            -> LabelEnv env
            -> State (FullGraphState op) (Maybe (Label Buff))
mkFullGraph (Exec op args) env = do
  -- Get a fresh computation label.
  cl <- freshCL
  undefined
mkFullGraph (Alet LeftHandSideUnit _ bnd scp) env =
  mkFullGraph bnd env >> mkFullGraph scp env

mkFullGraph _ _ = undefined
