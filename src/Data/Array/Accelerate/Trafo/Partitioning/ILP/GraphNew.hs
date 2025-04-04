{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
module Data.Array.Accelerate.Trafo.Partitioning.ILP.GraphNew where

import Data.Array.Accelerate.AST.LeftHandSide
import Data.Array.Accelerate.AST.Operation
import Data.Array.Accelerate.Backend hiding (MakesILP)
import Data.Array.Accelerate.Trafo.Partitioning.ILP.LabelsNew
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Multimap (Multimap)
import qualified Data.Array.Accelerate.Trafo.Partitioning.ILP.Multimap as MM
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Solver hiding (c)
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


import Control.Monad.State (State)
import Data.Foldable
import Control.Monad
import Data.Coerce



-- | Fusible computations @c1 -> b -> c2@.
type   Fusible = (Label Comp, Label Buff, Label Comp)  -- Probaly not needed
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
  ,   _fusibleEdges  :: Set Fusible    -- ^ Set of fusible computations. (Unused)
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

-- | Add a read edge from a buffer to a computation in the graph.
--
-- The buffer needs to be in scope, i.e. its parent must be an ancestor of the
-- computation.
-- An edge is added to all ancestors of the computation until the buffer becomes
-- out of scope.
--
--
reads :: Label Comp -> Label Buff -> Graph -> Graph
reads c b g = if c ^. parent == b ^. parent
  then g & readEdges  %~ MM.insert b c
         & readEdges' %~ MM.insert c b
  else case c ^. parent of
    Just p  -> reads p b g & readEdges  %~ MM.insert b p
                           & readEdges' %~ MM.insert p b
    Nothing -> error "reads: Buffer is out of scope."

-- | Add a write edge from a computation to a buffer.
--
-- See 'reads' for the scoping rules.
--
writes :: Label Comp -> Label Buff -> Graph -> Graph
writes c b g = if c ^. parent == b ^. parent
  then g & writeEdges  %~ MM.insert c b
         & writeEdges' %~ MM.insert b c  -- TODO: Add check for sole writer?
  else case c ^. parent of
    Just p  -> writes p b g & writeEdges  %~ MM.insert p b
                            & writeEdges' %~ MM.insert b p
    Nothing -> error "writes: Buffer is out of scope."

-- | Lens for getting the set of readers of a buffer.
--
-- This is a getter for now since modifying the set is a bit tricky.
--
readers :: Label Buff -> Lens' Graph (Labels Comp)
readers b = lens (\g -> MM.lookup b (g ^. readEdges)) const

-- | Lens for getting the set of writers of a buffer.
--
-- This is a getter for now since modifying the set is a bit tricky.
--
writers :: Label Buff -> Lens' Graph (Labels Comp)
writers b = lens (\g -> MM.lookup b (g ^. writeEdges')) const

-- | Lens for getting the set of inputs of a computation.
--
-- This is a getter for now since modifying the set is a bit tricky.
--
inputs :: Label Comp -> Lens' Graph (Labels Buff)
inputs c = lens (\g -> MM.lookup c (g ^. readEdges')) const

-- | Lens for getting the set of outputs of a computation.
--
-- This is a getter for now since modifying the set is a bit tricky.
--
outputs :: Label Comp -> Lens' Graph (Labels Buff)
outputs c = lens (\g -> MM.lookup c (g ^. writeEdges)) const





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
-- The environment is not passed as an argument to 'mkFullGraph' since it may
-- be modified by certain computations. Specifically, when a buffer is marked as
-- mutable, a copy of the buffer is created and the original buffer is replaced
-- by the copy in the environment.
--
data FullGraphState op env = FullGraphState
  { _ilpInfo :: ILPInfo op       -- ^ The ILP information.
  , _lenv    :: LabelEnv env     -- ^ The label environment.
  , _symbols :: Symbols Comp op  -- ^ The symbols for the ILP.
  , _currCL  :: Label Comp       -- ^ The current computation label.
  }

makeLenses ''FullGraphState

-- | Lens for interpreting the current computation label as a buffer label.
currBL :: Lens' (FullGraphState op env) (Label Buff)
currBL = currCL . asBLabel

-- | Fresh computation label.
freshCL :: State (FullGraphState op env) (Label Comp)
freshCL = currCL <%= (labelId +~ 1)

-- | Fresh buffer label.
freshBL :: State (FullGraphState op env) (Label Buff)
freshBL = currBL <%= (labelId +~ 1)



mkFullGraph :: forall op env a. (MakesILP op)
            => PreOpenAcc op env a
            -> State (FullGraphState op env) (Maybe (Label Buff))
mkFullGraph (Exec op args) = do
  cl  <- freshCL   -- Fresh computation label.
  env <- use lenv  -- Current label environment.
  (labelMap :: Map (Label Buff) (Label Buff), labelledArgs)
    <- forAccumLArgsM M.empty (labelArgs args env) \cases
      lmap larg@(LArg (ArgArray In _ _ _) bs) -> do
        -- If the argument is an input we add a read edge from the buffer to the
        -- computation.
        forM_ (S.elems bs) (\b -> ilpInfo.graph %= cl `reads` b)
        return (lmap, larg)
      lmap (LArg arg@(ArgArray Out _ _ _) bs) -> do
        -- If the argument is an output we also need to check if the buffer has
        -- previously been written to.
        -- If so, we need to make a copy of the buffer and use the copy instead.
        (lmap', elems) <- forAccumM lmap (S.elems bs) \lmap' b -> do
          ws <- use (ilpInfo.graph.writers b)
          b' <- if S.null ws then return b else copyBuffer b
          ilpInfo.graph %= cl `writes` b'
          return (M.insert b b' lmap', b')
        return (lmap', LArg arg (S.fromList elems))
      lmap larg@(LArg (ArgArray Mut _ _ _) bs) -> do
        -- If the argument is mutable we don't need to make a copy, but we do
        -- need to add read and write edges and mark them infusible.
        forM_ (S.elems bs) \b -> do
          ilpInfo.graph %= cl `reads` b
          ilpInfo.graph %= cl `writes` b
          -- TODO: Mark writers of b as infusible.
        return (lmap, larg)

      lmap larg@(LArg _ bs) -> do
        -- If the argument is not an array, but instead depends on arrays, then
        -- we need to add read edges and mark them as infusible.
        forM_ (S.elems bs) \b -> do
          ilpInfo.graph %= cl `reads` b
          -- TODO: Mark writers of b as infusible.
        return (lmap, larg)



  undefined


mkFullGraph (Alet LeftHandSideUnit _ bnd scp) =
  mkFullGraph bnd >> mkFullGraph scp

mkFullGraph _ = undefined


copyBuffer :: Label Buff -> State (FullGraphState op env) (Label Buff)
copyBuffer b = undefined



--------------------------------------------------------------------------------
-- mapAccumM from base-4.18.0
--------------------------------------------------------------------------------

-- | The `mapAccumM` function behaves like a combination of `mapM` and
-- `mapAccumL` that traverses the structure while evaluating the actions
-- and passing an accumulating parameter from left to right.
-- It returns a final value of this accumulator together with the new structure.
-- The accumulator is often used for caching the intermediate results of a computation.
--
-- @since base-4.18.0.0
mapAccumM
  :: forall m t s a b. (Monad m, Traversable t)
  => (s -> a -> m (s, b)) -> s -> t a -> m (s, t b)
mapAccumM f s t = coerce (mapM (StateT #. flip f) t) s
{-# INLINE mapAccumM #-}

-- | 'forAccumM' is 'mapAccumM' with the arguments rearranged.
--
-- @since base-4.18.0.0
forAccumM
  :: forall m t s a b. (Monad m, Traversable t)
  => s -> t a -> (s -> a -> m (s, b)) -> m (s, t b)
forAccumM s t f = mapAccumM f s t
{-# INLINE forAccumM #-}



--------------------------------------------------------------------------------
-- Flipped StateT from ghc-internals for `mapAccumM`
--------------------------------------------------------------------------------

newtype StateT s m a = StateT { runStateT :: s -> m (s, a) }

instance Monad m => Functor (StateT s m) where
    fmap :: Monad m => (a -> b) -> StateT s m a -> StateT s m b
    fmap = liftM
    {-# INLINE fmap #-}

instance Monad m => Applicative (StateT s m) where
    pure :: Monad m => a -> StateT s m a
    pure a = StateT $ \ s -> return (s, a)
    {-# INLINE pure #-}
    (<*>) :: Monad m => StateT s m (a -> b) -> StateT s m a -> StateT s m b
    StateT mf <*> StateT mx = StateT $ \ s -> do
        (s', f) <- mf s
        (s'', x) <- mx s'
        return (s'', f x)
    {-# INLINE (<*>) #-}
    (*>) :: Monad m => StateT s m a -> StateT s m b -> StateT s m b
    m *> k = m >> k
    {-# INLINE (*>) #-}

instance (Monad m) => Monad (StateT s m) where
    (>>=) :: Monad m => StateT s m a -> (a -> StateT s m b) -> StateT s m b
    m >>= k  = StateT $ \ s -> do
        (s', a) <- runStateT m s
        runStateT (k a) s'
    {-# INLINE (>>=) #-}

(#.) :: Coercible b c => (b -> c) -> (a -> b) -> (a -> c)
(#.) _f = coerce
{-# INLINE (#.) #-}
