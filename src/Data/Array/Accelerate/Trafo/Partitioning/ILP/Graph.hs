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
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
module Data.Array.Accelerate.Trafo.Partitioning.ILP.Graph where

import Prelude hiding ( init, reads )

-- Accelerate imports
import Data.Array.Accelerate.Array.Buffer
import Data.Array.Accelerate.AST.LeftHandSide
import Data.Array.Accelerate.AST.Operation hiding (Var)
import Data.Array.Accelerate.Trafo.Operation.LiveVars
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Labels
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Solver hiding ( c )
import Data.Array.Accelerate.Representation.Shape
import Data.Array.Accelerate.Type
import Data.Array.Accelerate.Analysis.Hash.Exp

-- Data structures (including custom Multimap)
import Data.Set (Set)
import Data.Map (Map)
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Multimap (Multimap)
import qualified Data.Set as S
import qualified Data.Map as M
import qualified Data.Array.Accelerate.Trafo.Partitioning.ILP.Multimap as MM

import Lens.Micro
import Lens.Micro.TH
import Lens.Micro.Mtl
import Lens.Micro.Internal

import Control.Monad.State (State)
import Data.Foldable
import Data.Kind (Type)
import Unsafe.Coerce (unsafeCoerce)
import Data.Array.Accelerate.AST.Idx
import Data.Maybe (fromJust)

-- Temporarily thing so HLS works.
data Edge where
  (:->) :: forall a. a -> a -> Edge


--------------------------------------------------------------------------------
-- Graph
--------------------------------------------------------------------------------

-- | Program graph in adjacency list representation.
--
-- The program graph is a directed graph in which a node is either a computation
-- or a buffer. Edges between buffers and computations represent dependencies
-- between them.
-- In addition to basic data flow, the graph also contains sets of fusible- and
-- infusible edges. Fusible edges represent dependencies between computations as
-- producer and consumer. They share data over a buffer and may be fused
-- together. If the computations are not fused, these edges enforce a strict
-- ordering between computations.
-- Infusible edges represent dependencies between computations that prevent them
-- from being fused together. They also enforce a strict ordering between
-- computations such that one must execute before the other.
-- Having a fusible and an infusible edge between two computations means that
-- data does flow between them, but that they can't be fused together.
--
-- A graph represents a single block of code, there can be no nested blocks.
-- Any nesting is handled by 'FusionILPblock' and 'FusionILP'.
--
data Graph = Graph   -- TODO: Use hashmaps and hashsets in production.
  {      _readEdges :: Set (Label Buff, Label Comp)  -- ^ Edges from buffers to computations.
  ,     _writeEdges :: Set (Label Comp, Label Buff)  -- ^ Edges from computations to buffers.
  ,   _fusibleEdges :: Set (Label Comp, Label Buff, Label Comp)  -- ^ Edges that can be fused.
  , _infusibleEdges :: Set (Label Comp, Label Comp)  -- ^ Edges that enforce strict ordering.
  }

instance Semigroup Graph where
  (<>) :: Graph -> Graph -> Graph
  (<>) (Graph r1 w1 f1 i1) (Graph r2 w2 f2 i2) = Graph
    (r1 <> r2) (w1 <> w2) (f1 <> f2) (i1 <> i2)

instance Monoid Graph where
  mempty :: Graph
  mempty = Graph mempty mempty mempty mempty

makeLenses ''Graph

-- | Add a read edge from a buffer to a computation in the graph.
reads' :: Label Comp -> Label Buff -> Graph -> Graph
reads' c b g = g & readEdges  %~ S.insert (b, c)

-- | Add a write edge from a computation to a buffer.
writes' :: Label Comp -> Label Buff -> Graph -> Graph
writes' c b g = g & writeEdges  %~ S.insert (c, b)

-- | Add an infusible edge between two computations.
--
-- Infusible edges represent computations that cannot be fused together and
-- enforces a strict ordering between them.
--
-- These edges represent the fact that two computations are not allowed to be in
-- the same cluster and that one should happen before the other. This is usually
-- to avoid race-conditions when two computations write to the same buffer.
before' :: Label Comp -> Label Comp -> Graph -> Graph
before' c1 c2 g
  | c1 == c2 = error "before: Cannot add infusible edge to self."
  | guard2Cycle c1 c2 g = error "before: c2 Already happens before c1."
  | otherwise = g & infusibleEdges %~ S.insert (c1, c2)

-- | Add a fusible edge between two computations over a buffer.
--
-- Fusible edges represent computations that can be fused together but enforces
-- a strict ordering between them if they are not fused.
--
-- These edges represent the flow of data between computations. Since multiple
-- computations can write to the same buffer, it is not necessarily the case that
-- all readers of a buffer read the same value. This depends on which computation
-- wrote to the buffer last.
--
fusible' :: Label Comp -> Label Buff -> Label Comp -> Graph -> Graph
fusible'  c1 b c2 g
  | c1 == c2 = error "fusible: Cannot add fusible edge to self."
  | guard2Cycle c1 c2 g = error "fusible: c2 Already happens before c1."
  -- | S.notMember (c1, b) (g^.writeEdges) = error "fusible: c1 is not a writer of b."
  -- | S.notMember (b, c2) (g^.readEdges)  = error "fusible: c2 is not a reader of b."
  | otherwise = g & fusibleEdges %~ S.insert (c1, b, c2)
                  &   writeEdges %~ S.insert (c1, b)
                  &    readEdges %~ S.insert (b, c2)
  -- TODO: Maybe throw an warning if the edge doesn't exist?

-- | Multiple computations can fuse with another over a buffer.
allFusible' :: Labels Comp -> Label Buff -> Label Comp -> Graph -> Graph
allFusible' cs1 b c2 g
  | S.null cs1 = g
  | otherwise = foldl' (\g' c1 -> (c1 `fusible'` b) c2 g') g cs1

-- | Same as 'fusible'', except also calls 'before'' on the two computations.
infusible' :: Label Comp -> Label Buff -> Label Comp -> Graph -> Graph
infusible' c1 b c2 = before' c1 c2 . fusible' c1 b c2

-- | Guard against 2-cycles in the graph.
guard2Cycle :: Label Comp -> Label Comp -> Graph -> Bool
guard2Cycle c1 c2 g = S.member (c2, c1) (g^.infusibleEdges)
  || any (\(c1', _, c2') -> (c1', c2') == (c2, c1)) (S.toList (g^.fusibleEdges))



--------------------------------------------------------------------------------
-- The Fusion ILP.
--------------------------------------------------------------------------------

-- | A single block of the ILP.
--
-- 'FusionILPblock' stores an fusion ILP for a single block of code. This is
-- possible because there can be no fusion between different blocks of code.
-- Separating the ILP into blocks then allows us to pass much smaller ILPs to
-- the solver, which should make the whole process faster.
-- If not, we can always merge the blocks together later.
data FusionILPblock op = FusionILPblock
  { _graph        :: Graph
  , _constraints  :: Constraint op
  , _bounds       :: Bounds op
  }

makeLenses ''FusionILPblock

-- | The ILP for the whole program.
--
-- The ILP for the whole program is represented as(Label _ k) a map from the enclosing
-- parent (may be 'Nothing' for the top-level) to the ILP for that block.
--
-- During the construction of the ILP, we want to be able to treat the whole
-- ILP as a single object, because computations may try to read or write to/from
-- buffers that are not in the same block. For this purpose each block will have
-- a proxy in one other block (except for the top-level block).
--
-- The proxy is a computation (but never a buffer). This ensures that
-- computations within the block can read/write from/to buffers outside the
-- block by adding an edge not only to itself, but also to any proxies of its
-- enclosing blocks until a legal edge can be made between the buffer and the
-- proxy/computation. We DO NOT need to make an explicit proxy for a buffer when
-- a computation in a sub-block reads/writes from/to it. Because any edges
-- between computations and proxies are infusible, the computations inside the
-- proxy may assume that the buffer exists and is not mutated by external
-- computations throughout the block's execution.
--
-- It could also be the case that a computation outside of a block tries to
-- read/write from/to a buffer inside a block. Such a situation can only occur
-- when a block returns a buffer, yielding ownership of the buffer to the
-- enclosing block. At this point the enclosing block can assume that the sub-
-- computation will not mutate the buffer any further, since a return-statement
-- is always the last statement of a block. In case the return-statement is not
-- the last statement of the block, then the returned buffer will be bound by
-- a let-binding, so no value is returned.
--
-- How we handle constraints and bounds is still up for debate. I can see some
-- merits in making a single set of bounds, rather than individual ones for each
-- block. This way we only need to set the bounds of a variable once rather than
-- for each block it occurs in. This could be useful for the backend, however
-- not so much for the frontend, since those bounds are added after the fact.
-- based on the graph. So no, we will keep the bounds for each block separate.
--
newtype FusionILP op = FusionILP (Map Parent (FusionILPblock op))

instance Semigroup (FusionILPblock op) where
  (<>) :: FusionILPblock op -> FusionILPblock op -> FusionILPblock op
  (<>) (FusionILPblock g1 c1 b1) (FusionILPblock g2 c2 b2) =
    FusionILPblock (g1 <> g2) (c1 <> c2) (b1 <> b2)

instance Monoid (FusionILPblock op) where
  mempty :: FusionILPblock op
  mempty = FusionILPblock mempty mempty mempty


type instance Index (FusionILP op)   = Parent
type instance IxValue (FusionILP op) = FusionILPblock op

instance Ixed (FusionILP op) where
  ix :: Index (FusionILP op) -> Traversal' (FusionILP op) (IxValue (FusionILP op))
  ix k f (FusionILP m) = f (M.findWithDefault mempty k m) <&> \v' -> FusionILP (M.insert k v' m)


-- Here we redefine the functions for the graph

-- | Add read edges between the buffer and the computation and all the parents
--   of the computation until the parent of the computation is an ancestor of
--   the buffer.
reads :: Label Comp -> Label Buff -> FusionILP op -> FusionILP op
reads comp buff
  = (ix(comp^.parent).graph %~ comp `reads'` buff)
  . if (comp^.parent) `ancestorOf` buff then id else reads comp buff

-- | Add write edges between the computation and the buffer and all the parents
--   of the computation until the parent of the computation is an ancestor of
--   the buffer.
writes :: Label Comp -> Label Buff -> FusionILP op -> FusionILP op
writes comp buff
  = (ix(comp^.parent).graph %~ comp `writes'` buff)
  . if (comp^.parent) `ancestorOf` buff then id else writes comp buff

-- | Add strict ordering between two computations.
--
-- Adds only an infusible edge between the two computations if they share the
-- same parent. If they don't share the same parent, find the largest common
-- ancestor and add the infusible edge there.
before :: Label Comp -> Label Comp -> FusionILP op -> FusionILP op
before c1 c2 = if c1^.parent == c2^.parent
  then ix(c1^.parent).graph %~ before' c1 c2
  else case compare (level c1) (level c2) of
    LT -> before  c1           (c2^.parent')  -- c2 is deeper
    GT -> before (c1^.parent')  c2            -- c1 is deeper
    EQ -> before (c1^.parent') (c2^.parent')  -- same level

-- | Add a fusible edge to the ILP.
--
-- Adds a fusible edge between the computations if they share the same parent.
-- If they don't share the same parent, add an infusible edge instead.
fusible :: Label Comp -> Label Buff -> Label Comp -> FusionILP op -> FusionILP op
fusible prod buff cons = if prod^.parent == cons^.parent
  then ix(prod^.parent).graph %~ fusible' prod buff cons
  else infusible prod buff cons

-- | Add an infusible edge to the ILP.
--
-- Adds an infusible edge between the computations if they share the same
-- parent. If they don't share the same parent, find the largest common ancestor
-- and add the infusible edge there.
infusible :: Label Comp -> Label Buff -> Label Comp -> FusionILP op -> FusionILP op
infusible prod buff cons = if prod^.parent == cons^.parent
  then ix(prod^.parent).graph %~ infusible' prod buff cons
  else case compare (level prod) (level cons) of
    LT -> infusible  prod           buff (cons^.parent')  -- cons is deeper
    GT -> infusible (prod^.parent') buff  cons            -- prod is deeper
    EQ -> infusible (prod^.parent') buff (cons^.parent')  -- same level

-- | Add strict ordering between computations and a computation.
allBefore :: Labels Comp -> Label Comp -> FusionILP op -> FusionILP op
allBefore cs1 c2 ilp = foldl' (\ilp' c1 -> before c1 c2 ilp') ilp cs1

-- | Add a fusible edges from all producers, over the buffer, to the consumer.
allFusible :: Labels Comp -> Label Buff -> Label Comp -> FusionILP op -> FusionILP op
allFusible prods buff cons ilp = foldl' (\ilp' prod -> fusible prod buff cons ilp') ilp prods

-- | Add an infusible edge from all producers, over the buffer, to the consumer.
allInfusible :: Labels Comp -> Label Buff -> Label Comp -> FusionILP op -> FusionILP op
allInfusible prods buff cons ilp = foldl' (\ilp' prod -> infusible prod buff cons ilp') ilp prods

-- | See 'allFusible'.
(--|) :: Labels Comp -> Label Buff -> Label Comp -> FusionILP op -> FusionILP op
(--|) = allFusible

-- | '($)' Specialized to '(|->)'.
(|->) :: (Label Comp -> FusionILP op -> FusionILP op) -> Label Comp -> FusionILP op -> FusionILP op
(|->) = ($)

-- | See 'allInfusible''.
(==|) :: Labels Comp -> Label Buff -> Label Comp -> FusionILP op -> FusionILP op
(==|) = allInfusible

-- | '($)' Specialized to '(|=>)'.
(|=>) :: (Label Comp -> FusionILP op -> FusionILP op) -> Label Comp -> FusionILP op -> FusionILP op
(|=>) = ($)


--------------------------------------------------------------------------------
-- Backend specific definitions
--------------------------------------------------------------------------------

type BackendCluster op = PreArgs (BackendClusterArg op)

class ( ShrinkArg (BackendClusterArg op), Eq (BackendVar op)
      , Ord (BackendVar op), Eq (BackendArg op), Show (BackendArg op)
      , Ord (BackendArg op), Show (BackendVar op)
      ) => MakesILP op where

  -- | ILP variables for backend-specific fusion rules.
  type BackendVar op

  -- | Information that the backend attaches to arguments for use in
  --   interpreting/code generation.
  type BackendArg op
  defaultBA :: BackendArg op

  -- | Information that the backend attaches to the cluster for use in
  --   interpreting/code generation.
  data BackendClusterArg op arg
  combineBackendClusterArg
    :: BackendClusterArg op (Out sh e)
    -> BackendClusterArg op (In sh e)
    -> BackendClusterArg op (Var' sh)
  encodeBackendClusterArg  :: BackendClusterArg op arg -> Builder


  -- | Given an ILP solution, attach the backend-specific information to an
  --   argument.
  labelLabelledArg :: Solution op -> Label Comp -> LabelledArg env a -> LabelledArgOp op env a

  -- | Convert a labelled argument to a cluster argument.
  getClusterArg :: LabelledArgOp op env a -> BackendClusterArg op a

  -- | This function defines per-operation backend-specific fusion rules.
  --
  -- When this function gets called, the majority of edges have already been
  -- added to the graph. That is, we have already added read-, write-, fusible-
  -- and infusible-edges such that no race conditions exist.
  -- The backend is responsible for adding (or removing) edges to (or from) the
  -- graph to enforce any additional constraints the implementation may have.
  --
  mkBackendGraph
    :: Label Comp             -- ^ The label of the operation.
    -> op args                -- ^ The operation.
    -> LabelledArgs env args  -- ^ The arguments to the operation.
    -> State (FullGraphState op env) ()

  -- | This function lets the backend define additional constraints on the ILP.
  finalize :: [Label Buff] -> [Label Comp] -> Constraint op



--------------------------------------------------------------------------------
-- ILP Variables
--------------------------------------------------------------------------------

data Var (op :: Type -> Type)
  = Pi (Label Comp)
    -- ^ Used for acyclic ordering of clusters.
    -- Pi (Label x y) = z means that computation number x (possibly a subcomputation of y, see Label) is fused into cluster z (y ~ Just i -> z is a subcluster of the cluster of i)
  | Fused (Label Comp) (Label Comp)
    -- ^ 0 is fused (same cluster), 1 is unfused. We do *not* have one of these for all pairs, only the ones we need for constraints and/or costs!
    -- Invariant: Like edges, both labels have to have the same parent: Either on top (Label _ Nothing) or as sub-computation of the same label (Label _ (Just x)).
    -- In fact, this is the Var-equivalent to Edge: an infusible edge has a constraint (== 1).
  | Manifest (Label Buff)
    -- ^ 0 means manifest, 1 is like a `delayed array`.
    -- Binary variable; will we write the output to a manifest array, or is it fused away (i.e. all uses are in its cluster)?
  | InDir (Label Comp)
    -- ^ -3 can't fuse with anything, -2 for 'left to right', -1 for 'right to left', n for 'unpredictable, see computation n' (currently only backpermute)
  | OutDir (Label Comp)
    -- ^ See 'InDir'.
  | InFoldSize (Label Comp)
    -- ^ Keeps track of the fold that's one dimension larger than this operation, and is fused in the same cluster.
    -- This prevents something like @zipWith f (fold g xs) (fold g ys)@ from illegally fusing
  | OutFoldSize (Label Comp)
    -- ^ Keeps track of the fold that's one dimension larger than this operation, and is fused in the same cluster.
    -- This prevents something like @zipWith f (fold g xs) (fold g ys)@ from illegally fusing
  | Other String
    -- ^ For one-shot variables that don't deserve a constructor. These are also integer variables, and the responsibility is on the user to pick a unique name!
    -- It is possible to add a variation for continuous variables too, see `allIntegers` in MIP.hs.
    -- We currently use this in Solve.hs for cost functions.
  | BackendSpecific (BackendVar op)
    -- ^ Vars needed to express backend-specific fusion rules.
    -- This is what allows backends to specify how each of the operations can fuse.

deriving instance Eq   (BackendVar op) => Eq   (Var op)
deriving instance Ord  (BackendVar op) => Ord  (Var op)
deriving instance Show (BackendVar op) => Show (Var op)



--------------------------------------------------------------------------------
-- Symbol table
--------------------------------------------------------------------------------

data LabelledArgOp  op env a = LOp (Arg env a) (ArgLabels a, Labels Buff) (BackendArg op)
type LabelledArgsOp op env   = PreArgs (LabelledArgOp op env)

instance Show (LabelledArgOp op env a) where
  show :: LabelledArgOp op env a -> String
  show (LOp _ bs _) = show bs

data Symbol (op :: Type -> Type) where
  SExe  :: LabelsEnv env -> LabelledArgs      env args -> op args                              -> Symbol op
  SExe' :: LabelsEnv env -> LabelledArgsOp op env args                                         -> Symbol op
  SUse  ::                  ScalarType e -> Int -> Buffer e                                    -> Symbol op
  SITE  :: LabelsEnv env -> ExpVar env PrimBool -> Label Comp -> Label Comp                    -> Symbol op
  SWhl  :: LabelsEnv env -> Label Comp -> Label Comp -> GroundVars env a     -> Uniquenesses a -> Symbol op
  SLet  ::                  GLeftHandSide bnd env env' -> BuffersTupF bnd -> Uniquenesses a    -> Symbol op
  SFun  ::                  GLeftHandSide bnd env env' -> BuffersTupF bnd                      -> Symbol op
  SBod  ::                  BuffersTupF res                                                    -> Symbol op
  SRet  :: LabelsEnv env -> GroundVars env a                                                   -> Symbol op
  SCmp  :: LabelsEnv env -> Exp env a                                                          -> Symbol op
  SAlc  :: LabelsEnv env -> ShapeR sh -> ScalarType e -> ExpVars env sh                        -> Symbol op
  SUnt  :: LabelsEnv env -> ExpVar env e                                                       -> Symbol op

-- | Mapping from labels to symbols.
type Symbols op = Map (Label Comp) (Symbol op)



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
-- We keep track of which computation last wrote to a buffer, i.e. the producer
-- of the buffer. Under normal circumstances a buffer has one and only one
-- producer, but when we enter an if-then-else it could be that some buffer
-- is written to by both branches. In this case the buffer is mutated by both,
-- which is safe because during execution only one branch is taken.
--
-- The environment and return values contain sets of buffer for a similar
-- reason. An if-then-else could return different buffers of the same type
-- depending on which branch is taken.
--
data FullGraphState op env = FullGraphState
  { _fusionILP  :: FusionILP op   -- ^ The ILP information.
  , _labelsEnv  :: LabelsEnv env  -- ^ The label environment.
  , _writersEnv :: WritersEnv     -- ^ Mapping from buffers to producers.
  , _readersEnv :: ReadersEnv     -- ^ Mapping from buffers to consumers.
  , _symbols    :: Symbols op     -- ^ The symbols for the ILP.
  , _currComp   :: Label Comp     -- ^ The current computation label.
  , _currEnvL   :: EnvLabel       -- ^ The current environment label.
  }

type ReadersEnv = Map (Label Buff) (Labels Comp)
type WritersEnv = Map (Label Buff) (Labels Comp)

makeLenses ''FullGraphState

-- | Lens for getting and setting the writers of a buffer.
--
-- The default value for the producer of a buffer is the buffer itself casted to
-- a computation label. This actually has some meaning, in that a buffer which
-- has yet to be written to is "produced" by its allocator (which has the same
-- label).
writers :: Label Buff -> Lens' (FullGraphState op env) (Labels Comp)
writers b f s = f (M.findWithDefault (S.singleton (b^.asComp)) b (s^.writersEnv)) <&> \cases
  cs | S.null cs -> s
     | otherwise -> s & writersEnv %~ M.insert b cs

-- | Lens for getting all writers of a buffer.
allWriters :: Labels Buff -> SimpleGetter (FullGraphState op env) (Labels Comp)
allWriters bs = to (\s -> foldMap (\b -> s^.writers b) bs)

-- | Lens for getting and setting the readers of a buffer.
--
-- By default a buffer isn't read by any computations.
readers :: Label Buff -> Lens' (FullGraphState op env) (Labels Comp)
readers b f s = f (M.findWithDefault mempty b (s^.readersEnv)) <&> \cases
  cs | S.null cs -> s
     | otherwise -> s & readersEnv %~ M.insert b cs

-- | Lens for getting all readers of a buffer.
allReaders :: Labels Buff -> SimpleGetter (FullGraphState op env) (Labels Comp)
allReaders bs = to (\s -> foldMap (\b -> s^.readers b) bs)

-- | Lens for working under the scope of a computation.
--
-- It first sets the parent of the current label to the supplied computation
-- label. Then it applies the function to the 'FullGraphState' with the now
-- parented label. Finally, it sets the parent of the current label back to the
-- original parent.
scope :: Label Comp -> Lens' (FullGraphState op env) (FullGraphState op env)
scope c = with (currComp.parent) (Just c)

local :: LabelsEnv env' -> Lens' (FullGraphState op env) (FullGraphState op env')
local env' f s = (labelsEnv .~ s^.labelsEnv) <$> f (s & labelsEnv .~ env')

-- | Lens for interpreting the current  label as a buffer label.
currBuff :: Lens' (FullGraphState op env) (Label Buff)
currBuff = currComp . asBuff

-- | Fresh computation label.
freshComp :: State (FullGraphState op env) (Label Comp)
freshComp = zoom currComp freshL'

-- | Fresh buffer as a singleton set and the corresponding computation label.
--
-- Buffers are by default their own producer so we don't need to set it, but we
-- do need to add a read edge between them.
freshBuff :: State (FullGraphState op env) (Labels Buff, Label Comp)
freshBuff = do
  c <- freshComp
  b <- use currBuff
  fusionILP %= c `writes` b
  return (S.singleton b, c)

-- | Read from a buffer and maybe fuse with its writers.
(--->) :: Label Buff -> Label Comp -> State (FullGraphState op env) ()
(--->) b c = do
  ws <- use $ writers b
  fusionILP %= c `reads` b
  fusionILP %= ws --|b|-> c

-- | Read from a buffer and don't fuse with its writers.
(===>) :: Label Buff -> Label Comp -> State (FullGraphState op env) ()
(===>) b c = do
  ws <- use $ writers b
  fusionILP %= c `reads` b
  fusionILP %= ws ==|b|=> c

-- | Write to a buffer.
--
-- For a write to be safe we need to enforce the following:
-- * All (current) readers run before the writer.
-- * The producer runs before the writer.
(<===) :: Label Buff -> Label Comp -> State (FullGraphState op env) ()
(<===) b c = do
  ws <- use $ writers b
  rs <- use $ readers b
  fusionILP %= ws `allBefore` c
  fusionILP %= rs `allBefore` c
  fusionILP %= c `writes` b
  writers b .= S.singleton c
  readers b .= S.empty

-- | Mutate a buffer.
--
-- For a mutation to be safe we need to enforce the following:
-- * All (current) readers run before the writer.
-- * The producer runs before the writer.
-- * We can't fuse with the producer.
(<==>) :: Label Buff -> Label Comp -> State (FullGraphState op env) ()
(<==>) b c = do
  ws <- use $ writers b
  rs <- use $ readers b
  fusionILP %= rs `allBefore` c
  fusionILP %= c  `reads`  b
  fusionILP %= c  `writes` b
  fusionILP %= ws ==|b|=>  c
  writers b .= S.singleton c
  readers b .= S.empty

-- | Mutate a buffer with the identity function, preventing fusion.
--
-- This is a special case of mutation where the buffer is not actually changed.
-- Unlike '(<==>)', we now don't have to:
-- * Enforce the readers to run before the writer.
-- * Clear the readers of the buffer.
(<-->) :: Label Buff -> Label Comp -> State (FullGraphState op env) ()
(<-->) b c = do
  ws <- use $ writers b
  fusionILP %= c  `reads`  b
  fusionILP %= c  `writes` b
  fusionILP %= ws ==|b|=>  c
  writers b .= S.singleton c



--------------------------------------------------------------------------------
-- Graph construction
--------------------------------------------------------------------------------

mkFullGraph :: forall op env t. (MakesILP op)
            => FullGraphMaker PreOpenAcc op env t (BuffersTupF t)
mkFullGraph (Exec op args) = do
  lenv <- use labelsEnv
  renv <- use readersEnv
  wenv <- use writersEnv
  c <- freshComp
  let labelledArgs = labelArgs args lenv
  forLArgsM_ labelledArgs \case
    (L (ArgArray In  _ _ _) (Arr  _, bs)) -> for_ bs (---> c)
    (L (ArgArray Out _ _ _) (Arr  _, bs)) -> for_ bs (<=== c)
    (L (ArgArray Mut _ _ _) (Arr  _, bs)) -> for_ bs (<==> c)
    (L _                    (NotArr, bs)) -> for_ bs (===> c)
  zoom ( with readersEnv renv
       . with writersEnv wenv
       . unprotected fusionILP
       ) do
    mkBackendGraph c op labelledArgs
  symbols %= M.insert c (SExe lenv labelledArgs op)
  return TupFunit

mkFullGraph (Alet LeftHandSideUnit _ bnd scp) =
  mkFullGraph bnd >> mkFullGraph scp

mkFullGraph (Alet lhs u bnd scp) = do
  lenv <- use labelsEnv
  c <- freshComp
  bndRes <- mkFullGraph bnd
  for_ bndRes $ traverse_ (<--> c)
  symbols %= M.insert c (SLet lhs bndRes u)
  lenv' <- zoom currEnvL (weakenEnv lhs bndRes lenv)
  zoom (local lenv') (mkFullGraph scp)

mkFullGraph (Return vars) = do
  lenv <- use labelsEnv
  c <- freshComp
  let (_, bs) = getVarsFromEnv vars lenv
  for_ bs $ traverse_ (<--> c)
  symbols %= M.insert c (SRet lenv vars)
  return bs

mkFullGraph (Compute expr) = do
  lenv <- use labelsEnv
  (b, c) <- freshBuff
  for_ (getExpDeps expr lenv) (===> c)
  symbols %= M.insert c (SCmp lenv expr)
  return (tupFlike (expType expr) b)

mkFullGraph (Alloc shr e sh) = do
  lenv <- use labelsEnv
  (b, c) <- freshBuff
  for_ (getVarsDeps sh lenv) (===> c)
  symbols %= M.insert c (SAlc lenv shr e sh)
  return (TupFsingle b)

mkFullGraph (Unit var) = do
  lenv <- use labelsEnv
  (b, c) <- freshBuff
  for_ (getVarDeps var lenv) (===> c)
  symbols %= M.insert c (SUnt lenv var)
  return (TupFsingle b)

mkFullGraph (Use sctype n buff) = do
  (b, c) <- freshBuff
  symbols %= M.insert c (SUse sctype n buff)
  return (TupFsingle b)

mkFullGraph (Acond cond tacc facc) = do
  lenv <- use labelsEnv
  c_cond  <- freshComp
  c_true  <- freshComp
  c_false <- freshComp
  for_ (getVarDeps cond lenv) (===> c_cond)
  symbols %= M.insert c_cond (SITE lenv cond c_true c_false)
  (t_res, t_wenv, t_renv) <- block c_true  mkFullGraph tacc
  (f_res, f_wenv, f_renv) <- block c_false mkFullGraph facc
  writersEnv .= t_wenv <> f_wenv
  readersEnv .= t_renv <> f_renv
  let res = t_res <> f_res
  for_ res $ traverse_ (<--> c_cond)
  return res

mkFullGraph (Awhile u cond body init) = do
  lenv <- use labelsEnv
  c_while <- freshComp
  c_cond  <- freshComp
  c_body  <- freshComp
  for_ (getVarsDeps init lenv) (===> c_while)
  symbols %= M.insert c_while (SWhl lenv c_cond c_body init u)
  (_                  , cond_wenv, cond_renv) <- block c_cond mkFullGraphF cond
  (unsafeCoerce -> res, body_wenv, body_renv) <- block c_body mkFullGraphF body  -- Safe
  writersEnv .= cond_wenv <> body_wenv
  readersEnv .= cond_renv <> body_renv
  for_ res $ traverse_ (<--> c_while)
  return res



mkFullGraphF :: forall op env t. (MakesILP op)
             => FullGraphMaker PreOpenAfun op env t (BuffersTupF (Result t))
mkFullGraphF (Abody acc) = do
  c <- freshComp
  zoom (scope c) do
    res <- mkFullGraph acc
    symbols %= M.insert c (SBod res)
    for_ res $ traverse_ (<--> c)
    return (unsafeCoerce res)  -- Safe

mkFullGraphF (Alam lhs f) = do
  lenv <- use labelsEnv
  (b, c) <- freshBuff
  let bnd = tupFlike (lhsToTupR lhs) b
  lenv' <- zoom currEnvL (weakenEnv lhs bnd lenv)
  zoom (local lenv') do
    res <- mkFullGraphF f
    symbols %= M.insert c (SFun lhs bnd)
    return res


-- | A block is a subcomputation that is executed under the scope of another
--   computation.
block :: Label Comp -> FullGraphMaker f op env t (BuffersTupF r)
      -> FullGraphMaker f op env t (BuffersTupF r, WritersEnv, ReadersEnv)
block c f x = zoom (scope c . protected writersEnv . protected readersEnv) do
    res <- f x
    for_ res $ traverse_ (<--> c)
    wenv <- use writersEnv
    renv <- use readersEnv
    return (res, wenv, renv)


-- | Type of functions that take an AST and produce a graph.
type FullGraphMaker f op env t r = f op env t -> State (FullGraphState op env) r

-- | Type-level function to get the result type of a function.
--
-- Note that to make this work I needed 'unsafeCoerce', because the constructors
-- of data types we encounter use either @t@ or @s -> t@. Unfortunately GHC
-- can't distinguish between these two cases since both are of kind 'Type'.
-- The current types used in Accelerate are simply too permissive to allow for
-- rigorous proofs.
type Result :: Type -> Type
type family Result t where
  Result (_ -> t) = Result t
  Result t        = t

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

-- | Makes a ReindexPartial, which allows us to transform indices in @env@ into indices in @env'@.
-- We cannot guarantee the index is present in env', so we use the partiality of ReindexPartial by
-- returning a Maybe. Uses unsafeCoerce to re-introduce type information implied by the ELabels.
mkReindexPartial :: LabelsEnv env -> LabelsEnv env' -> ReindexPartial Maybe env env'
mkReindexPartial env env' idx = go env'
  where
    -- The ELabel in the original environment
    e = fst $ lookupIdxInEnv idx env
    go :: forall e a. LabelsEnv e -> Maybe (Idx e a)
    go ((e',_) :>>: rest) -- e' is the ELabel in the new environment
      -- Here we have to convince GHC that the top element in the environment
      -- really does have the same type as the one we were searching for.
      -- Some literature does this stuff too: 'effect handlers in haskell, evidently'
      -- and 'a monadic framework for delimited continuations' come to mind.
      -- Basically: standard procedure if you're using Ints as a unique identifier
      -- and want to re-introduce type information. :)
      -- Type applications allow us to restrict unsafeCoerce to the return type.
      | e == e' = Just $ unsafeCoerce @(Idx e _) @(Idx e a) ZeroIdx
      -- Recurse if we did not find e' yet.
      | otherwise = SuccIdx <$> go rest
    -- If we hit the end, the Elabel was not present in the environment.
    -- That probably means we'll error out at a later point, but maybe there is
    -- a case where we try multiple options? No need to worry about it here.
    go EnvNil = Nothing


--------------------------------------------------------------------------------
-- Helpers
--------------------------------------------------------------------------------

-- | Lens that protects a given value from being modified.
protected :: Lens' s a -> Lens' s s
protected l f s = (l .~ s^.l) <$> f s

-- | Lens that protects all but the given value from being modified.
unprotected :: Lens' s a -> Lens' s s
unprotected l f s = (\s' -> s & l .~ s'^.l) <$> f s

-- | Lens that temporarily uses the supplied value in place of the current
--   value, then restores the original value.
with :: Lens' s a -> a -> Lens' s s
with l a f s = (l .~ s^.l) <$> f (s & l .~ a)
