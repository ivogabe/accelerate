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

import Data.Set (Set)
import qualified Data.Set as S

import Data.Map (Map)
import qualified Data.Map as M


import Control.Monad.State (State)
import Data.Foldable



--------------------------------------------------------------------------------
-- Graph
--------------------------------------------------------------------------------

-- | Fusible computations @c1 -> b -> c2@.
type Fusible   = (Label Comp, Label Buff, Label Comp)
-- | Infusible computations @c1 -> c2@.
type Infusible = (Label Comp, Label Comp)
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

-- | Add a read edge from a buffer to a computation in the graph.
--
-- See 'canAccess' for the scoping rules. This condition may be removed in the
-- future, but for now it is required to ensure that the graph is well-formed.
--
reads :: Label Comp -> Label Buff -> Graph -> Graph
reads c b g
  | c `canAccess` b = g & readEdges  %~ MM.insert b c
                        & readEdges' %~ MM.insert c b
  | otherwise       = error "reads: Buffer is out of scope."

-- | Add a write edge from a computation to a buffer.
--
-- See 'canAccess' for the scoping rules. This condition may be removed in the
-- future, but for now it is required to ensure that the graph is well-formed.
--
writes :: Label Comp -> Label Buff -> Graph -> Graph
writes c b g
  | c `canAccess` b = g & writeEdges  %~ MM.insert c b
                        & writeEdges' %~ MM.insert b c
  | otherwise       = error "writes: Buffer is out of scope."

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

-- | Add an infusible edge between two computations.
--
-- Infusible edges represent computations that cannot be fused together and
-- enforces a strict ordering between them.
--
-- These edges represent the fact that two computations are not allowed to be in
-- the same cluster and that one should happen before the other. This is usually
-- to avoid race-conditions when two computations write to the same buffer.
--
before :: Label Comp -> Label Comp -> Graph -> Graph
before c1 c2 g
  | c1 == c2 = error "before: Cannot add infusible edge to self."
  | S.member (c2, c1) (g ^. infusibleEdges)  -- Very rudimentary cycle check.
    = error "before: c2 Already happens before c1."
  | any (\(c1', _, c2') -> c1' == c2 && c2' == c1) (g ^. fusibleEdges)  -- Also check the fusible edges.
    = error "before: c2 Already happens before c1."
  | otherwise = g & infusibleEdges %~ S.insert (c1, c2)

-- | Multiple computations must happen before a computation.
--
-- This is a convenience function for adding multiple infusible edges at once.
-- (See 'before'.)
--
allBefore :: Labels Comp -> Label Comp -> Graph -> Graph
allBefore cs c2 g
  | S.null cs = g
  | otherwise = foldl' (\g' c1 -> (c1 `before` c2) g') g cs

-- | Add a fusible edge between two computations over a buffer.
--
-- Fusible edges represent computations that can be fused together but enforces
-- a strict ordering between them if they are not fused.
--
-- These edges represent the flow of data between computations. Since multiple
-- computations can write to the same buffer, it is not necessarily the case that
-- all reader of a buffer read the same value. This depends on which computation
-- wrote to the buffer last.
--
fusible :: Label Comp -> Label Buff -> Label Comp -> Graph -> Graph
fusible  c1 b c2 g
  | c1 == c2 = error "fusible: Cannot add fusible edge to self."
  | any (\(c1', _, c2') -> c1' == c2 && c2' == c1) (g ^. fusibleEdges)  -- Very rudimentary cycle check.
    = error "fusible: c2 Already happens before c1."
  | S.member (c2, c1) (g ^. infusibleEdges)  -- Also check the infusible edges.
    = error "fusible: c2 Already happens before c1."
  | S.notMember c1 (g ^. writers b)  -- Check if c1 is a writer of b.
    = error "fusible: c1 is not a writer of b."
  | S.notMember c2 (g ^. readers b)  -- Check if c2 is a reader of b.
    = error "fusible: c2 is not a reader of b."
  | otherwise = g & fusibleEdges %~ S.insert (c1, b, c2)

-- | Same as 'fusible', except also calls 'before' on the two computations.
infusible :: Label Comp -> Label Buff -> Label Comp -> Graph -> Graph
infusible c1 b c2 = before c1 c2 . fusible c1 b c2

-- | See 'fusible'.
(--|) :: Label Comp -> Label Buff -> Label Comp -> Graph -> Graph
(--|) = fusible

-- | '($)' Specialized to '(|->)'.
(|->) :: (Label Comp -> Graph -> Graph) -> Label Comp -> Graph -> Graph
(|->) = ($)

-- | See 'infusible'.
(==|) :: Label Comp -> Label Buff -> Label Comp -> Graph -> Graph
(==|) = infusible

-- | '($)' Specialized to '(|=>)'.
(|=>) :: (Label Comp -> Graph -> Graph) -> Label Comp -> Graph -> Graph
(|=>) = ($)



--------------------------------------------------------------------------------
-- Information for ILP construction
--------------------------------------------------------------------------------

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



--------------------------------------------------------------------------------
-- Backend specific definitions
--------------------------------------------------------------------------------

class (ShrinkArg (BackendClusterArg op), Eq (BackendVar op), Ord (BackendVar op), Eq (BackendArg op), Show (BackendArg op), Ord (BackendArg op), Show (BackendVar op)) => MakesILP op where
  mkGraph :: op args -> LabelledArgs env args -> Label Comp -> State (FullGraphState op env) ()



--------------------------------------------------------------------------------
-- Graph construction
--------------------------------------------------------------------------------

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
  , _prods   :: Producers        -- ^ Mapping from buffers to producers.
  , _symbols :: Symbols Comp op  -- ^ The symbols for the ILP.
  , _currL   :: Label Void       -- ^ The current label.
  }

type Producers = Map (Label Buff) (Label Comp)

makeLenses ''FullGraphState

-- | Lens for getting and setting the producer of a buffer.
--
-- The default value for the producer of a buffer is the buffer itself casted to
-- a computation label. This actually has some meaning, in that a buffer which
-- has yet to be written to is "produced" by @malloc@.
--
producer :: Label Buff -> Lens' (FullGraphState op env) (Label Comp)
producer b f s = fmap
  (\c -> s & prods %~ M.insert b c)
  (f (M.findWithDefault (b ^. asCLabel) b (s ^. prods)))

-- | Lens for locally adding new variables to the environment.
--
-- Any changes to the environment are local to the computation and will be
-- discarded after the computation is finished.
--
local :: GLeftHandSide v env env' -> LabelTup Buff v -> Lens' (FullGraphState op env) (FullGraphState op env')
local lhs bs f s = s <$ f (s & lenv %~ consLHS lhs bs)

-- | Lens for interpreting the currenenv %= setProducert label as a computation label.
currC :: Lens' (FullGraphState op env) (Label Comp)
currC = currL . asCLabel

-- | Lens for interpreting the current  label as a buffer label.
currB :: Lens' (FullGraphState op env) (Label Buff)
currB = currL . asBLabel

-- | Fresh computation label.
freshC :: State (FullGraphState op env) (Label Comp)
freshC = zoom currC freshL'

-- | Fresh buffer (and computation) label.
--
-- Buffers are by default their own producer so we don't need to set it, but we
-- do need to add a read edge between them.
freshB :: State (FullGraphState op env) (Label Buff, Label Comp)
freshB = do
  c <- freshC
  b <- use currB
  ilpInfo.graph %= c `writes` b
  return (b, c)

-- | Read from a buffer and maybe fuse with its producer.
(--->) :: Label Buff -> Label Comp -> State (FullGraphState op env) ()
(--->) b c = do
  p <- use $ producer b
  ilpInfo.graph %= c `reads` b
  ilpInfo.graph %= p --|b|-> c

-- | Read from a buffer and don't fuse with its producer.
(===>) :: Label Buff -> Label Comp -> State (FullGraphState op env) ()
(===>) b c = do
    p <- use $ producer b
    ilpInfo.graph %= c `reads` b
    ilpInfo.graph %= p ==|b|=> c

-- | Write to a buffer.
--
-- For a write to be safe we need to enforce the following:
-- * All (current) readers run before the writer.
-- * The producer runs before the writer.
(<===) :: Label Buff -> Label Comp -> State (FullGraphState op env) ()
(<===) b c = do
  p  <- use $ producer b
  rs <- use $ ilpInfo.graph.readers b
  ilpInfo.graph %= rs `allBefore` c
  ilpInfo.graph %= p `before` c
  ilpInfo.graph %= c `writes` b
  producer b .= c

-- | Mutate a buffer.
--
-- For a mutation to be safe we need to enforce the following:
-- * All (current) readers run before the writer.
-- * The producer runs before the writer.
-- * We can't fuse with the producer.
(<==>) :: Label Buff -> Label Comp -> State (FullGraphState op env) ()
(<==>) b c = do
        p  <- use $ producer b
        rs <- use $ ilpInfo.graph.readers b
        ilpInfo.graph %= rs `allBefore` c
        ilpInfo.graph %= c `reads`  b
        ilpInfo.graph %= c `writes` b
        ilpInfo.graph %= p ==|b|=>  c
        producer b .= c

-- | Mutate a buffer with the identity function, preventing fusion.
--
-- This is a special case of mutation where the buffer is not actually changed.
-- As a result, we only need to enforce the following:
-- * The producer runs before the writer.
-- * We can't fuse with the producer.
(<-->) :: Label Buff -> Label Comp -> State (FullGraphState op env) ()
(<-->) b c = do
    p <- use $ producer b
    ilpInfo.graph %= c `reads`  b
    ilpInfo.graph %= c `writes` b
    ilpInfo.graph %= p ==|b|=>  c
    producer b .= c



mkFullGraph :: forall op env a. (MakesILP op)
            => PreOpenAcc op env a
            -> State (FullGraphState op env) (LabelTup Buff a)
mkFullGraph (Exec op args) = do
  c <- freshC      -- Fresh computation label.
  env <- use lenv  -- Current label environment.
  let labelledArgs = labelArgs args env
  forLArgsM_ labelledArgs \case
    (LArg (ArgArray In  _ _ _) bs) -> forM_ bs (---> c)
    (LArg (ArgArray Out _ _ _) bs) -> forM_ bs (<=== c)
    (LArg (ArgArray Mut _ _ _) bs) -> forM_ bs (<==> c)
    (LArg _                    bs) -> forM_ bs (===> c)
  _ -- TODO: Query the backend.
  _ -- TODO: Create symbol.
  return TupRunit_

mkFullGraph (Alet LeftHandSideUnit _ bnd scp) =
  mkFullGraph bnd >> mkFullGraph scp

mkFullGraph (Alet lhs _ bnd scp) = do
  c <- freshC
  bndRes <- mkFullGraph bnd
  forM_ bndRes (<--> c)
  _ -- TODO: Create symbol.
  zoom (local lhs bndRes) (mkFullGraph scp)

mkFullGraph (Return vars) = do
  c <- freshC
  bs <- getVarsLTup vars <$> use lenv
  forM_ bs (<--> c)
  _ -- TODO: Create symbol.
  return bs

mkFullGraph (Compute expr) = do
  (b, c) <- freshB
  let bs = tupRlike_ (expType expr) b
  _ -- TODO: Create symbol.
  return bs

mkFullGraph (Alloc shr e sh) = do
  (b, c) <- freshB
  _ -- TODO: Create symbol.
  return (TupRsingle_ b)

mkFullGraph (Unit var) = do
  (b, c) <- freshB
  _ -- TODO: Create symbol.
  return (TupRsingle_ b)

mkFullGraph (Use sctype n buff) = do
  (b, c) <- freshB
  _ -- TODO: Create symbol.
  return (TupRsingle_ b)


mkFullGraph _ = undefined




{-
I probably want to not duplicate a buffer that is used as both input
and output. Doing so is extremely tricky because doing so requires that the
environment is updated to point to the new buffer. Because of this we can't
simply put the old environment back after a let binding.

Doing this isn't the worst, we just need to weaken the environment instead. What
is a problem is how to handle the backend. The backend needs to know which
buffers are its inputs and outputs and it needs to be able to query the graph.
Problem is, it needs to do these queries on the old graph which doesn't contain
the new buffer yet.

So avoinding duplicating buffers is probably best. In this case it's not
necessary to keep the environment in the state, but I'll do so regardless
because in most cases the environment isn't touched. I could in this case
move the graph out of the state since it might cause confusion as to whether I
am working on the full graph or some temporary subgraph that will be merged
later.

Bonus, this approach still allows for the duplication of input and ouput buffers
in a separate pass before fusion. Doing it like that won't have any of the
aforementioned problems since the buffer will be a proper part of the graph
and the environment before some operation is executed.
-}
