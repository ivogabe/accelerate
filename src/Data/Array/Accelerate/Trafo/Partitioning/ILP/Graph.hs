{-# LANGUAGE AllowAmbiguousTypes      #-}
{-# LANGUAGE BlockArguments           #-}
{-# LANGUAGE DataKinds                #-}
{-# LANGUAGE FlexibleContexts         #-}
{-# LANGUAGE FlexibleInstances        #-}
{-# LANGUAGE FunctionalDependencies   #-}
{-# LANGUAGE GADTs                    #-}
{-# LANGUAGE InstanceSigs             #-}
{-# LANGUAGE KindSignatures           #-}
{-# LANGUAGE LambdaCase               #-}
{-# LANGUAGE PatternSynonyms          #-}
{-# LANGUAGE RankNTypes               #-}
{-# LANGUAGE ScopedTypeVariables      #-}
{-# LANGUAGE StandaloneDeriving       #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TupleSections            #-}
{-# LANGUAGE TypeApplications         #-}
{-# LANGUAGE TypeFamilyDependencies   #-}
{-# LANGUAGE UndecidableInstances     #-}
{-# LANGUAGE ViewPatterns             #-}
{-# LANGUAGE OverloadedStrings #-}
module Data.Array.Accelerate.Trafo.Partitioning.ILP.Graph where

import Prelude hiding ( init, reads )

-- Accelerate imports
import Data.Array.Accelerate.AST.Idx
import Data.Array.Accelerate.AST.LeftHandSide
import Data.Array.Accelerate.AST.Operation hiding (Var)
import Data.Array.Accelerate.Analysis.Hash.Exp
import Data.Array.Accelerate.Array.Buffer
import Data.Array.Accelerate.Representation.Shape
import Data.Array.Accelerate.Trafo.Operation.LiveVars
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Labels
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Solver
import Data.Array.Accelerate.Type
import Data.Array.Accelerate.Error

-- Data structures (including custom Multimap)
import Data.Set (Set)
import Data.Map (Map)
import qualified Data.Set as S
import qualified Data.Map as M

import Lens.Micro
import Lens.Micro.Mtl

import Control.Monad.State.Strict (State, runState)
import Data.Foldable ( Foldable(fold, foldl'), for_, traverse_ )
import Data.Kind (Type)
import Unsafe.Coerce (unsafeCoerce)
import Data.Coerce (coerce)
import Debug.Trace

--------------------------------------------------------------------------------
-- Fusion Graph
--------------------------------------------------------------------------------

type ReadEdge      = (Label Buff, Label Comp)
type WriteEdge     = (Label Comp, Label Buff)
type StrictEdge    = (Label Comp, Label Comp)
type DataflowEdge  = (Label Comp, Label Buff, Label Comp)
type FusibleEdge   = DataflowEdge
type InfusibleEdge = DataflowEdge

-- | Program graph.
--
-- The graph consists of read/write edges, strict ordering edges and fusible
-- edges.
--
-- The read/write edges represent a read or write relation between a buffer and
-- a computation. In the ILP, these edges get a variable indicating in which
-- order a computation reads or writes an array in the buffer. Some of these
-- edges are duplicated, in which case we assert that they are equal in the
-- bounds of 'FusionILP'.
--
-- The strict ordering edges enforce a strict ordering between two computations.
-- This ordering can be due to any number of reasons, but in most cases it is to
-- prevent race conditions between two computations.
--
-- The data-flow edges represent a flow of data between two computations over a
-- buffer. These edges are used to determine which computations can be fused.
-- Data-flow edges that are also strict edges are infusible.
-- Data-flow edges that are not strict edges are fusible.
--
-- From the sets of data-flow and strict ordering edges we can derive:
-- 1. The set of write edges. @S.map (\(w,b,_) -> (w,b)) _dataflowEdges@
-- 2. The set of read edges. @S.map (\(_,b,r) -> (w,b)) _dataflowEdges@
-- 3. The set of fusible edges. @S.filter (\(w,_,r) -> S.notMember (w,r) _strictEdges) _dataflowEdges@
-- 4. The set of infusible edges. @S.filter (\(w,_,r) -> S.member (w,r) _strictEdges) _dataflowEdges@
--
-- The latter two computations may be combined as such:
--
-- @
-- (fusible, infusible) = S.partition (\(w,_,r) -> S.notMember (w,r) _strictEdges) _dataflowEdges
-- @
--
data FusionGraph = FusionGraph   -- TODO: Use hashmaps and hashsets in production.
  {      _bufferNodes :: Labels Buff       -- ^ Buffers in the graph.
  , _computationNodes :: Labels Comp       -- ^ Computations in the graph.
  ,        _readEdges :: Set ReadEdge      -- ^ Edges that represent reads.
  ,       _writeEdges :: Set WriteEdge     -- ^ Edges that represent writes.
  ,      _strictEdges :: Set StrictEdge    -- ^ Edges that enforce strict ordering.
  ,    _dataflowEdges :: Set DataflowEdge  -- ^ Edges that represent data-flow.
  }

instance Semigroup FusionGraph where
  (<>) :: FusionGraph -> FusionGraph -> FusionGraph
  (<>) (FusionGraph b1 c1 r1 w1 f1 i1) (FusionGraph b2 c2 r2 w2 f2 i2) = FusionGraph
    (b1 <> b2) (c1 <> c2) (r1 <> r2) (w1 <> w2) (f1 <> f2) (i1 <> i2)

instance Monoid FusionGraph where
  mempty :: FusionGraph
  mempty = FusionGraph mempty mempty mempty mempty mempty mempty

-- | Class for types that contain a fusion graph.
--
-- This is a manually written version of what microlens-th would generate when
-- using @makeClassy@.
class HasFusionGraph g where
  fusionGraph :: Lens' g FusionGraph

  bufferNodes :: Lens' g (Labels Buff)
  bufferNodes = fusionGraph.bufferNodes

  computationNodes :: Lens' g (Labels Comp)
  computationNodes = fusionGraph.computationNodes

  strictEdges :: Lens' g (Set StrictEdge)
  strictEdges = fusionGraph.strictEdges

  dataflowEdges :: Lens' g (Set DataflowEdge)
  dataflowEdges = fusionGraph.dataflowEdges

  readEdges :: Lens' g (Set ReadEdge)
  readEdges = fusionGraph.readEdges

  writeEdges :: Lens' g (Set WriteEdge)
  writeEdges = fusionGraph.writeEdges

-- | Base instance of 'HasFusionGraph' for 'FusionGraph'.
--
-- This instance cannot make use of lenses defined in 'HasFusionGraph' because
-- it is the base instance and would otherwise cause a loop.
instance HasFusionGraph FusionGraph where
  fusionGraph :: Lens' FusionGraph FusionGraph
  fusionGraph = id

  bufferNodes :: Lens' FusionGraph (Set (Label Buff))
  bufferNodes f s = f (_bufferNodes s) <&> \bs -> s{_bufferNodes = bs}

  computationNodes :: Lens' FusionGraph (Set (Label Comp))
  computationNodes f s = f (_computationNodes s) <&> \cs -> s{_computationNodes = cs}

  strictEdges :: Lens' FusionGraph (Set StrictEdge)
  strictEdges f s = f (_strictEdges s) <&> \es -> s{_strictEdges = es}

  dataflowEdges :: Lens' FusionGraph (Set DataflowEdge)
  dataflowEdges f s = f (_dataflowEdges s) <&> \es -> s{_dataflowEdges = es}

  readEdges :: Lens' FusionGraph (Set ReadEdge)
  readEdges f s = f (_readEdges s) <&> \es -> s{_readEdges = es}

  writeEdges :: Lens' FusionGraph (Set WriteEdge)
  writeEdges f s = f (_writeEdges s) <&> \es -> s{_writeEdges = es}

-- | Insert a buffer node into the graph.
insertBuffer :: HasFusionGraph g => Label Buff -> g -> g
insertBuffer b = bufferNodes %~ S.insert b

-- | Insert a write edge from a computation to a buffer.
insertComputation :: HasFusionGraph g => Label Comp -> g -> g
insertComputation c = computationNodes %~ S.insert c

-- | Insert a read edge from a buffer to a computation.
insertRead :: HasFusionGraph g => ReadEdge -> g -> g
insertRead (b, c) = readEdges %~ S.insert (b, c)

-- | Insert a write edge from a computation to a buffer.
insertWrite :: HasFusionGraph g => WriteEdge -> g -> g
insertWrite (c, b) = writeEdges %~ S.insert (c, b)

-- | Insert a strict relation between two computations.
insertStrict :: (HasCallStack, HasFusionGraph g) => (Label Comp, Label Comp) -> g -> g
insertStrict (c1, c2)
  | c1 == c2  = error $ "strict: Reflexive edge " ++ show (c1, c2)
  | otherwise = strictEdges %~ S.insert (c1, c2)

-- | Insert a fusible data-flow edge between two computations.
insertFusible :: (HasCallStack, HasFusionGraph g) => DataflowEdge -> g -> g
insertFusible (c1, b, c2) g
  | S.notMember (c1, b) (g^.writeEdges) = error $ "fusible: Missing write " ++ show (c1, b)
  | S.notMember (b, c2) (g^.readEdges)  = error $ "fusible: Missing read " ++ show (b, c2)
  | c1 == c2  = error $ "fusible: Reflexive edge " ++ show (c1, c2)
  | otherwise = g & dataflowEdges %~ S.insert (c1, b, c2)

-- | Insert an infusible data-flow edge between two computations.
insertInfusible :: (HasCallStack, HasFusionGraph g) => DataflowEdge -> g -> g
insertInfusible (c1, b, c2) = insertStrict (c1, c2) . insertFusible (c1, b, c2)

-- | Gets the set of fusible edges.
fusibleEdges :: HasFusionGraph g => SimpleGetter g (Set FusibleEdge)
fusibleEdges = to (\g -> S.filter (\(w, _, r) -> S.notMember (w, r) (g^.strictEdges)) (g^.dataflowEdges))

-- | Gets the set of infusible edges.
infusibleEdges :: HasFusionGraph g => SimpleGetter g (Set InfusibleEdge)
infusibleEdges = to (\g -> S.filter (\(w, _, r) -> S.member (w, r) (g^.strictEdges)) (g^.dataflowEdges))

-- | Gets the set of fusible and infusible edges.
fusionEdges :: HasFusionGraph g => SimpleGetter g (Set FusibleEdge, Set InfusibleEdge)
fusionEdges = to (\g -> S.partition (\(w, _, r) -> S.notMember (w, r) (g^.strictEdges)) (g^.dataflowEdges))

-- | Gets the set of strict edges that are not data-flow edges.
orderEdges :: HasFusionGraph g => SimpleGetter g (Set StrictEdge)
orderEdges = to (\g -> let dataflowEdges' = S.map (\(w,_,r) -> (w,r)) (g^.dataflowEdges)
                        in S.filter (\(w, r) -> S.notMember (w, r) dataflowEdges') (g^.strictEdges))

-- | Gets the input edges of a computations.
inputEdgesOf :: HasFusionGraph g => Label Comp -> SimpleGetter g (Set ReadEdge)
inputEdgesOf c = to (\g -> S.filter (\(_, r) -> r == c) (g^.readEdges))

-- | Gets the output edges of a computations.
outputEdgesOf :: HasFusionGraph g => Label Comp -> SimpleGetter g (Set WriteEdge)
outputEdgesOf c = to (\g -> S.filter (\(w, _) -> w == c) (g^.writeEdges))

-- | Gets the read edges of a buffer.
readEdgesOf :: HasFusionGraph g => Label Buff -> SimpleGetter g (Set ReadEdge)
readEdgesOf b = to (\g -> S.filter (\(b', _) -> b' == b) (g^.readEdges))

-- | Gets the write edges of a buffer.
writeEdgesOf :: HasFusionGraph g => Label Buff -> SimpleGetter g (Set WriteEdge)
writeEdgesOf b = to (\g -> S.filter (\(_, b') -> b' == b) (g^.writeEdges))



--------------------------------------------------------------------------------
-- The Fusion ILP.
--------------------------------------------------------------------------------

-- | A single block of the ILP.
--
-- 'FusionILP' stores an fusion ILP for a single block of code. This is
-- possible because there can be no fusion between different blocks of code.
-- Separating the ILP into blocks then allows us to pass much smaller ILPs to
-- the solver, which should make the whole process faster.
-- If not, we can always merge the blocks together later.
data FusionILP op = FusionILP
  { _graph       :: FusionGraph
  , _constraints :: Constraint op
  , _bounds      :: Bounds op
  }

instance Semigroup (FusionILP op) where
  (<>) :: FusionILP op -> FusionILP op -> FusionILP op
  (<>) (FusionILP g1 c1 b1) (FusionILP g2 c2 b2) =
    FusionILP (g1 <> g2) (c1 <> c2) (b1 <> b2)

instance Monoid (FusionILP op) where
  mempty :: FusionILP op
  mempty = FusionILP mempty mempty mempty

-- | Class for accessing the fusion ILP field of a data structure.
--
-- We make this because there are at least two data structures that contain a
-- fusion ILP: 'FullGraphState' and the result of graph construction. This is
-- similar to what microlens-th would generate when using @makeFields@.
class HasFusionILP s op | s -> op where
  fusionILP :: Lens' s (FusionILP op)

graph :: Lens' (FusionILP op) FusionGraph
graph f s = f (_graph s) <&> \g -> s{_graph = g}

constraints :: Lens' (FusionILP op) (Constraint op)
constraints f s = f (_constraints s) <&> \c -> s{_constraints = c}

bounds :: Lens' (FusionILP op) (Bounds op)
bounds f s = f (_bounds s) <&> \b -> s{_bounds = b}

instance HasFusionGraph (FusionILP op) where
  fusionGraph :: Lens' (FusionILP op) FusionGraph
  fusionGraph = graph

-- | Safely insert a read edge into the graph.
--
-- Since we don't know at what level the read will be used we need to make
-- a read relation between the buffer and all computations in its scope. All of
-- these read edges should be equal in the ILP, which is enforced by 'readDir'.
reads :: Label Comp -> Label Buff -> FusionILP op -> FusionILP op
reads c b = fusionGraph %~ flip (foldl' (flip (insertRead . (b,)))) cs
  where cs = allNonAncestors b c

-- | Safely insert a write edge into the graph.
--
-- Since we don't know at what level the write will be used we need to make
-- a write relation between the buffer and all computations in its scope. All of
-- these write edges should be equal in the ILP, which is enforced by 'writeDir'.
writes :: Label Comp -> Label Buff -> FusionILP op -> FusionILP op
writes c b = fusionGraph %~ flip (foldl' (flip (insertWrite . (,b)))) cs
  where cs = allNonAncestors b c

-- | Safely insert read edges between multiple computations and a buffer.
read :: Labels Comp -> Label Buff -> FusionILP op -> FusionILP op
read cs b = flip (foldl' (flip (`reads` b))) cs

-- | Safely insert write edges between multiple computations and a buffer.
write :: Labels Comp -> Label Buff -> FusionILP op -> FusionILP op
write cs b = flip (foldl' (flip (`writes` b))) cs

-- | Safely add a strict relation between two computations.
before :: HasCallStack => Label Comp -> Label Comp -> FusionILP op -> FusionILP op
before c1 c2 = fusionGraph %~ insertStrict (c1', c2')
  where c1' = oldestNonAncestor c2 c1
        c2' = oldestNonAncestor c1 c2

-- | Safely add a fusible edge between two computations.
--
-- If the computations share the same parent, add a fusible edge, otherwise add
-- an infusible edge.
fusible :: HasCallStack => Label Comp -> Label Buff -> Label Comp -> FusionILP op -> FusionILP op
fusible prod buff cons = if prod^.parent == cons^.parent
  then fusionGraph %~ insertFusible (prod, buff, cons)
  else infusible prod buff cons

-- | Safely add an infusible edge between two computations.
--
-- Infusible edges are only added to computations that share the same parent.
-- If they don't share the same parent, find the first ancestors that do.
infusible :: HasCallStack => Label Comp -> Label Buff -> Label Comp -> FusionILP op -> FusionILP op
infusible prod buff cons = fusionGraph %~ insertInfusible (prod', buff, cons')
  where prod' = oldestNonAncestor cons prod
        cons' = oldestNonAncestor prod cons

-- | Safely add strict ordering between multiple computations and another computation.
allBefore :: HasCallStack => Labels Comp -> Label Comp -> FusionILP op -> FusionILP op
allBefore cs1 c2 ilp = foldl' (\ilp' c1 -> before c1 c2 ilp') ilp cs1

-- | Safely add fusible edges from all producers to the consumer.
allFusible :: HasCallStack => Labels Comp -> Label Buff -> Label Comp -> FusionILP op -> FusionILP op
allFusible prods buff cons ilp = foldl' (\ilp' prod -> fusible prod buff cons ilp') ilp prods

-- | Safely add infusible edges from all producers to the consumer.
allInfusible :: HasCallStack => Labels Comp -> Label Buff -> Label Comp -> FusionILP op -> FusionILP op
allInfusible prods buff cons ilp = foldl' (\ilp' prod -> infusible prod buff cons ilp') ilp prods

-- | Infix synonym for 'allBefore'.
(==|-|=>) :: HasCallStack => Labels Comp -> Label Comp -> FusionILP op -> FusionILP op
(==|-|=>) = allBefore

-- | Infix synonym for 'allFusible'.
(--|) :: HasCallStack => Labels Comp -> Label Buff -> Label Comp -> FusionILP op -> FusionILP op
(--|) = allFusible

-- | Infix synonym for 'allInfusible'.
(==|) :: HasCallStack => Labels Comp -> Label Buff -> Label Comp -> FusionILP op -> FusionILP op
(==|) = allInfusible

-- | Arrow heads to complete '(--|)' and '(==|)'.
(|->), (|=>) :: (a -> b) -> a -> b
(|->) = ($)
(|=>) = ($)

--------------------------------------------------------------------------------
-- Backend specific definitions
--------------------------------------------------------------------------------

-- | The backend has access to a small state so it doesn't accidentally break
--   the state used by the frontend construction algorithm.
data BackendGraphState op env = BackendGraphState
  { _backendFusionILP  :: FusionILP op    -- ^ The entire ILP.
  , _backendBuffersEnv :: BuffersEnv env  -- ^ The buffers environment (read only).
  , _backendReadersEnv :: ReadersEnv      -- ^ The readers environment (read only).
  , _backendWritersEnv :: WritersEnv      -- ^ The writers environment (read only).
  }

instance HasFusionILP (BackendGraphState op env) op where
  fusionILP :: Lens' (BackendGraphState op env) (FusionILP op)
  fusionILP f s = f (_backendFusionILP s) <&> \ilp -> s{_backendFusionILP = ilp}

instance HasBuffersEnv (BackendGraphState op env) (BackendGraphState op env') env env' where
  buffersEnv :: Lens (BackendGraphState op env) (BackendGraphState op env') (BuffersEnv env) (BuffersEnv env')
  buffersEnv f s = f (_backendBuffersEnv s) <&> \env -> s{_backendBuffersEnv = env}

instance HasReadersEnv (BackendGraphState op env) where
  readersEnv :: Lens' (BackendGraphState op env) ReadersEnv
  readersEnv f s = f (_backendReadersEnv s) <&> \env -> s{_backendReadersEnv = env}

instance HasWritersEnv (BackendGraphState op env) where
  writersEnv :: Lens' (BackendGraphState op env) WritersEnv
  writersEnv f s = f (_backendWritersEnv s) <&> \env -> s{_backendWritersEnv = env}

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
  mkGraph
    :: Label Comp             -- ^ The label of the operation.
    -> op args                -- ^ The operation.
    -> LabelledArgs env args  -- ^ The arguments to the operation.
    -> State (BackendGraphState op env) ()

  -- | This function lets the backend define additional constraints on the ILP.
  finalize :: FusionGraph -> Constraint op

labelLabelledArgs :: MakesILP op => Solution op -> Label Comp -> LabelledArgs env args -> LabelledArgsOp op env args
labelLabelledArgs sol l (arg :>: args) = labelLabelledArg sol l arg :>: labelLabelledArgs sol l args
labelLabelledArgs _ _ ArgsNil = ArgsNil

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
  | ReadDir' (Label Buff) (Label Comp)
    -- ^ \-3 can't fuse with anything, -2 for 'left to right', -1 for 'right to left', n for 'unknown', see computation n (currently only backpermute). DO NOT USE THIS, USE 'ReadDir' INSTEAD! See 'reads' for the reason.
  | WriteDir' (Label Comp) (Label Buff)
    -- ^ See 'ReadDir'. DO NOT USE THIS, USE 'WriteDir' INSTEAD! See 'writes' for the reason.
  | InDir (Label Comp)
    -- ^ For backwards compatibility, see 'ReadDir''. For this variable to have any meaning the backend has to call 'useInDir' (or 'useInOutDir').
  | OutDir (Label Comp)
    -- ^ For backwards compatibility, see 'WriteDir''. For this variable to have any meaning the backend has to call 'useOutDir' (or 'useInOutDir').
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

-- | Safe pattern for 'ReadDir''.
pattern ReadDir :: Label Buff -> Label Comp -> Var op
pattern ReadDir b c <- ReadDir' b c where
  ReadDir b c = ReadDir' b (oldestNonAncestor b c)

-- | Safe pattern for 'WriteDir''.
pattern WriteDir :: Label Comp -> Label Buff -> Var op
pattern WriteDir c b <- WriteDir' c b where
  WriteDir c b = WriteDir' (oldestNonAncestor b c) b
{-# COMPLETE Pi, Fused, Manifest, ReadDir, WriteDir, InFoldSize, OutFoldSize, Other, BackendSpecific #-}


-- | Sets all 'ReadDir' that contain the computation @c@ to be equal to the
--   'InDir' variable of @c@. If you don't use this fuction, using 'InDir' will
--   have no effect.
--
-- This function makes it so we can write ILP's in the old style, i.e. where
-- a computation reads/writes in only one direction.
useInDir :: HasFusionILP g op => Label Comp -> State g ()
useInDir c = do
  readDirs <- map (var . uncurry ReadDir) . S.toList <$> use (fusionILP.inputEdgesOf c)
  fusionILP.constraints %= (<> equals (var (InDir c) : readDirs))

-- | Sets all 'WriteDir' that contain the computation @c@ to be equal to the
--   'OutDir' variable of @c@. If you don't use this fuction, using 'OutDir'
--   will have no effect.
--
-- This function makes it so we can write ILP's in the old style, i.e. where
-- a computation reads/writes in only one direction.
useOutDir :: HasFusionILP g op => Label Comp -> State g ()
useOutDir c = do
  writeDirs <- map (var . uncurry WriteDir) . S.toList <$> use (fusionILP.outputEdgesOf c)
  fusionILP.constraints %= (<> equals (var (OutDir c) : writeDirs))

-- | See 'useInDir' and 'useOutDir'.
useInOutDir :: HasFusionILP g op => Label Comp -> State g ()
useInOutDir c = useInDir c >> useOutDir c


-- | Constructor for 'Pi' variables.
pi :: Label Comp -> Expression op
pi = var . Pi

-- | No clue what this is for.
delayed :: Label Buff -> Expression op
delayed = notB . manifest

-- | Constructor for 'Manifest' variables.
manifest :: Label Buff -> Expression op
manifest = var . Manifest

-- | Safe constructor for 'Fused' variables.
fused :: HasCallStack => Label Comp -> Label Comp -> Expression op
fused prod cons = var $ Fused prod' cons'
  where prod' = oldestNonAncestor cons prod
        cons' = oldestNonAncestor prod cons

-- | Safe constructor for 'ReadDir' variables.
readDir :: Label Buff -> Label Comp -> Expression op
readDir buff = var . ReadDir buff

-- | Safe constructor for 'WriteDir' variables.
writeDir :: Label Comp -> Label Buff -> Expression op
writeDir comp = var . WriteDir comp



--------------------------------------------------------------------------------
-- Symbol table
--------------------------------------------------------------------------------

data Symbol (op :: Type -> Type) where
  SExe  :: BuffersEnv env -> LabelledArgs      env args -> op args                              -> Symbol op
  SExe' :: BuffersEnv env -> LabelledArgsOp op env args -> op args                              -> Symbol op
  SUse  ::                   ScalarType e -> Int -> Buffer e                                    -> Symbol op
  SITE  :: BuffersEnv env -> ExpVar env PrimBool -> Label Comp -> Label Comp                    -> Symbol op
  SWhl  :: BuffersEnv env -> Label Comp -> Label Comp -> GroundVars env bnd -> Uniquenesses bnd -> Symbol op
  SLet  ::                   BoundGLHS bnd env env' -> Label Comp           -> Uniquenesses bnd -> Symbol op
  SFun  ::                   BoundGLHS bnd env env' -> Label Comp                               -> Symbol op
  SBod  ::                   Label Comp                                                         -> Symbol op
  SRet  :: BuffersEnv env -> GroundVars env a                                                   -> Symbol op
  SCmp  :: BuffersEnv env -> Exp env a                                                          -> Symbol op
  SAlc  :: BuffersEnv env -> ShapeR sh -> ScalarType e -> ExpVars env sh                        -> Symbol op
  SUnt  :: BuffersEnv env -> ExpVar env e                                                       -> Symbol op

-- | Mapping from labels to symbols.
type Symbols op = Map (Label Comp) (Symbol op)

data LabelledArgOp  op env a = LOp (Arg env a) (ArgLabels a) (BackendArg op)
type LabelledArgsOp op env   = PreArgs (LabelledArgOp op env)

instance Show (LabelledArgOp op env a) where
  show :: LabelledArgOp op env a -> String
  show (LOp _ bs _) = show bs

unlabelop :: LabelledArgsOp op env a -> Args env a
unlabelop ArgsNil = ArgsNil
unlabelop ((LOp arg _ _) :>: args) = arg :>: unlabelop args

reindexLabelledArgOp :: Applicative f => ReindexPartial f env env' -> LabelledArgOp op env t -> f (LabelledArgOp op env' t)
reindexLabelledArgOp k (LOp (ArgVar vars               ) l o) = (\x -> LOp x l o)  .   ArgVar          <$> reindexVars k vars
reindexLabelledArgOp k (LOp (ArgExp e                  ) l o) = (\x -> LOp x l o)  .   ArgExp          <$> reindexExp k e
reindexLabelledArgOp k (LOp (ArgFun f                  ) l o) = (\x -> LOp x l o)  .   ArgFun          <$> reindexExp k f
reindexLabelledArgOp k (LOp (ArgArray m repr sh buffers) l o) = (\x -> LOp x l o) <$> (ArgArray m repr <$> reindexVars k sh <*> reindexVars k buffers)

reindexLabelledArgsOp :: Applicative f => ReindexPartial f env env' -> LabelledArgsOp op env t -> f (LabelledArgsOp op env' t)
reindexLabelledArgsOp = reindexPreArgs reindexLabelledArgOp

attachBackendLabels :: MakesILP op => Solution op -> Symbols op -> Symbols op
attachBackendLabels sol = M.mapWithKey \cases
  l (SExe lenv largs op) -> SExe' lenv (labelLabelledArgs sol l largs) op
  _  SExe'{} -> error "already converted???"
  _  con -> con



--------------------------------------------------------------------------------
-- FusionGraph construction
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
-- The environment is not passed as an argument to 'mkFullGraph'' since it may
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
  { _fusionILP  :: FusionILP op    -- ^ The ILP information.
  , _buffersEnv :: BuffersEnv env  -- ^ The label environment.
  , _readersEnv :: ReadersEnv      -- ^ Mapping from buffers to consumers.
  , _writersEnv :: WritersEnv      -- ^ Mapping from buffers to producers.
  , _symbols    :: Symbols op      -- ^ The symbols for the ILP.
  , _currComp   :: Label Comp      -- ^ The current computation label.
  , _currEnvL   :: EnvLabel        -- ^ The current environment label.
  }

type ReadersEnv = Map (Label Buff) (Labels Comp)
type WritersEnv = Map (Label Buff) (Labels Comp)

initialFullGraphState :: FullGraphState op ()
initialFullGraphState = FullGraphState mempty EnvNil mempty mempty mempty (Label 0 Nothing) 0

instance Show (FullGraphState op env) where
  show :: FullGraphState op env -> String
  show s = "FullGraphState { readersEnv=" ++ show (s^.readersEnv) ++
            ", writersEnv=" ++ show (s^.writersEnv) ++
            " }"

instance HasFusionILP (FullGraphState op env) op where
  fusionILP :: Lens' (FullGraphState op env) (FusionILP op)
  fusionILP f s = f (_fusionILP s) <&> \ilp -> s{_fusionILP = ilp}

class HasBuffersEnv s t env env' | s -> env, t -> env' where
  buffersEnv :: Lens s t (BuffersEnv env) (BuffersEnv env')

instance HasBuffersEnv (FullGraphState op env) (FullGraphState op env') env env' where
  buffersEnv :: Lens (FullGraphState op env) (FullGraphState op env') (BuffersEnv env) (BuffersEnv env')
  buffersEnv f s = f (_buffersEnv s) <&> \env -> s{_buffersEnv = env}

class HasReadersEnv s where
  readersEnv :: Lens' s ReadersEnv

instance HasReadersEnv (FullGraphState op env) where
  readersEnv :: Lens' (FullGraphState op env) ReadersEnv
  readersEnv f s = f (_readersEnv s) <&> \env -> s{_readersEnv = env}

class HasWritersEnv s where
  writersEnv :: Lens' s WritersEnv

instance HasWritersEnv (FullGraphState op env) where
  writersEnv :: Lens' (FullGraphState op env) WritersEnv
  writersEnv f s = f (_writersEnv s) <&> \env -> s{_writersEnv = env}

class HasSymbols s op | s -> op where
  symbols :: Lens' s (Symbols op)

instance HasSymbols (FullGraphState op env) op where
  symbols :: Lens' (FullGraphState op env) (Symbols op)
  symbols f s = f (_symbols s) <&> \sym -> s{_symbols = sym}

currComp :: Lens' (FullGraphState op env) (Label Comp)
currComp f s = f (_currComp s) <&> \c -> s{_currComp = c}

currEnvL :: Lens' (FullGraphState op env) EnvLabel
currEnvL f s = f (_currEnvL s) <&> \l -> s{_currEnvL = l}

-- | Lens for creating the backend graph state.
--
-- This lens sets new values for the readers and writers environments because
-- the backend needs to work with the environment from before the computation
-- was added. We don't need to do the same for the buffers environment, because
-- it only changes when a new variable is introduced.
--
-- The fusion ILP is the only value that the backend may modify, so its the only
-- value that is retrieved from the backend graph state afterwards.
backendGraphState :: ReadersEnv -> WritersEnv -> Lens' (FullGraphState op env) (BackendGraphState op env)
backendGraphState renv wenv f s = f (BackendGraphState (s^.fusionILP) (s^.buffersEnv) renv wenv)
  <&> \b -> s & fusionILP .~ b^.fusionILP

-- | Lens for getting and setting the writers of a buffer.
--
-- The default value for the producer of a buffer is the buffer itself casted to
-- a computation label. This actually has some meaning, in that a buffer which
-- has yet to be written to is "produced" by its allocator (which has the same
-- label).
writers :: HasWritersEnv s => Label Buff -> Lens' s (Labels Comp)
writers b f s = f (M.findWithDefault (S.singleton (coerce b)) b (s^.writersEnv)) <&> \cs -> s & writersEnv %~ M.insert b cs

-- | Lens for getting all writers of buffers.
allWriters :: (Foldable f, HasWritersEnv s) => f (Label Buff) -> SimpleGetter s (Labels Comp)
allWriters bs = to (\s -> foldMap (\b -> s^.writers b) bs)
-- allWriters bs = to (\s -> traverse (\b -> s^.writers b) bs)

-- | Lens for getting and setting the readers of a buffer.
--
-- By default a buffer isn't read by any computations.
readers :: HasReadersEnv s => Label Buff -> Lens' s (Labels Comp)
readers b f s = f (M.findWithDefault mempty b (s^.readersEnv)) <&> \cs -> s & readersEnv %~ M.insert b cs

-- | Lens for getting all readers of buffers.
allReaders :: (Foldable f, HasReadersEnv s) => f (Label Buff) -> SimpleGetter s (Labels Comp)
allReaders bs = to (\s -> foldMap (\b -> s^.readers b) bs)

-- | Lens for working under the scope of a computation.
--
-- It first sets the parent of the current label to the supplied computation
-- label. Then it applies the function to the 'FullGraphState' with the now
-- parented label. Finally, it sets the parent of the current label back to the
-- original parent.
scope :: Label Comp -> Lens' (FullGraphState op env) (FullGraphState op env)
scope c = with (currComp.parent) (Just c)

local :: BuffersEnv env' -> Lens' (FullGraphState op env) (FullGraphState op env')
local env' f s = (buffersEnv .~ s^.buffersEnv) <$> f (s & buffersEnv .~ env')

-- | Fresh computation label.
freshComp :: State (FullGraphState op env) (Label Comp)
freshComp = do
  comp <- zoom currComp freshL'
  fusionILP %= insertComputation comp
  return comp

-- | Fresh buffer as a singleton set and the corresponding computation label.
--
-- The implementation of 'writers' makes it so by default the buffer is produced
-- by the computation that allocates it. This is possible because they have the
-- same label just, just different types. We still need to add the read edge to
-- the graph though.
freshBuff :: State (FullGraphState op env) (Labels Buff, Label Comp)
freshBuff = do
  c <- freshComp
  fusionILP %= insertBuffer (coerce c)
  fusionILP %= insertWrite (c, coerce c)
  return (S.singleton (coerce c), c)

-- | Read from a buffer and be fusisble with its writers.
(--->) :: HasCallStack => Label Buff -> Label Comp -> State (FullGraphState op env) ()
(--->) b c = do
  traceM $ "(--->) " ++ show b ++ " " ++ show c
  ws <- use $ writers b
  traceM $ "  ws <- " ++ show ws
  fusionILP %= c `reads` b
  fusionILP %= ws --|b|-> c
  readers b %= S.insert c
  traceM $ "  readers " ++ show b ++ " %= insert " ++ show c

-- | Read from a buffer and be infusible with its writers.
(===>) :: HasCallStack => Label Buff -> Label Comp -> State (FullGraphState op env) ()
(===>) b c = do
  traceM $ "(===>) " ++ show b ++ " " ++ show c
  ws <- use $ writers b
  traceM $ "  ws <- " ++ show ws
  fusionILP %= c `reads` b
  fusionILP %= ws ==|b|=> c
  readers b %= S.insert c
  traceM $ "  readers " ++ show b ++ " %= insert " ++ show c

-- | Write to a buffer.
--
-- For a write to be safe we need to enforce the following:
-- 1. All readers run before the computation.
-- 2. All writers run before the computation.
-- 3. We become the sole writer of the buffer.
-- 4. We clear the readers of the buffer.
(<===) :: HasCallStack => Label Buff -> Label Comp -> State (FullGraphState op env) ()
(<===) b c = do
  traceM $ "(<===) " ++ show b ++ " " ++ show c
  rs <- use $ readers b
  traceM $ "  rs <- " ++ show rs
  ws <- use $ writers b
  traceM $ "  ws <- " ++ show ws
  fusionILP %= c `writes` b
  fusionILP %= rs ==|-|=> c
  fusionILP %= ws ==|-|=> c
  writers b .= S.singleton c
  traceM $ "  writers " ++ show b ++ " .= " ++ show (S.singleton c)
  readers b .= S.empty
  traceM $ "  readers " ++ show b ++ " .= empty"

-- | Mutate a buffer.
--
-- For a mutation to be safe we need to enforce the following:
-- 1. All readers run before this computation.
-- 2. All writers are infusible with this computation.
-- 3. We become the sole writer of the buffer.
-- 4. We clear the readers of the buffer.
(<==>) :: HasCallStack => Label Buff -> Label Comp -> State (FullGraphState op env) ()
(<==>) b c = do
  traceM $ "(<==>) " ++ show b ++ " " ++ show c
  rs <- use $ readers b
  traceM $ "  rs <- " ++ show rs
  ws <- use $ writers b
  traceM $ "  ws <- " ++ show ws
  fusionILP %= c `reads` b
  fusionILP %= c `writes` b
  fusionILP %= rs ==|-|=> c
  fusionILP %= ws ==|b|=> c
  writers b .= S.singleton c
  traceM $ "  writers " ++ show b ++ " .= " ++ show (S.singleton c)
  readers b .= S.empty
  traceM $ "  readers " ++ show b ++ " .= empty"

-- | Mutate a buffer with the identity function, preventing fusion.
--
-- This is a special case of mutation where the buffer is not actually changed.
-- Because of this, we now don't need to enforce rules 1 and 4 from '(<==>)'.
(<-->) :: HasCallStack => Label Buff -> Label Comp -> State (FullGraphState op env) ()
(<-->) b c = do
  traceM $ "(<-->) " ++ show b ++ " " ++ show c
  ws <- use $ writers b
  traceM $ "  ws <- " ++ show ws
  fusionILP %= c `reads` b
  fusionILP %= c `writes` b
  fusionILP %= ws ==|b|=> c
  writers b .= S.singleton c



--------------------------------------------------------------------------------
-- Full Graph construction
--------------------------------------------------------------------------------

-- The 2 instances below can be used to clean up the code in ILP.hs a bit.
instance HasFusionILP (FusionILP op, Symbols op) op where
  fusionILP :: Lens'  (FusionILP op, Symbols op) (FusionILP op)
  fusionILP f (ilp, sym) = f ilp <&> (,sym)

instance HasSymbols (FusionILP op, Symbols op) op where
  symbols :: Lens' (FusionILP op, Symbols op) (Symbols op)
  symbols f (ilp, sym) = f sym <&> (ilp,)

-- | Construct the full fusion graph for a program.
mkFullGraph :: MakesILP op => PreOpenAcc op () a -> (FusionILP op, Symbols op)
mkFullGraph acc = (s^.fusionILP & constraints <>~ manifestRes, s^.symbols)
  where
    (res, s) = runState (mkFullGraph' acc) initialFullGraphState
    manifestRes = foldMap (foldMap (\b -> manifest b .==. int 0)) res

-- | Construct the full fusion graph for a function.
mkFullGraphF :: MakesILP op => PreOpenAfun op () a -> (FusionILP op, Symbols op)
mkFullGraphF acc = (s^.fusionILP, s^.symbols)
  where
    (_, s) = runState (mkFullGraphF' acc) initialFullGraphState

mkFullGraph' :: forall op env t. MakesILP op
             => FullGraphMaker PreOpenAcc op env t (BuffersTup t)
mkFullGraph' (Exec op args) = do
  traceM $ "Exec _ " ++ show args
  lenv <- use buffersEnv
  renv <- use readersEnv
  wenv <- use writersEnv
  c    <- freshComp
  let labelledArgs = labelArgs args lenv
  let bsInArr  = selectLArgs  inArr labelledArgs
  let bsOutArr = selectLArgs outArr labelledArgs
  let bsNotArr = selectLArgs notArr labelledArgs
  for_ (bsInArr  `S.difference`   bsOutArr) (---> c)
  for_ (bsOutArr `S.difference`   bsInArr)  (<=== c)
  for_ (bsInArr  `S.intersection` bsOutArr) (<==> c)
  for_  bsNotArr                            (===> c)
  zoom (backendGraphState renv wenv) (mkGraph c op labelledArgs)
  symbols %= M.insert c (SExe lenv labelledArgs op)
  return TupFunit

mkFullGraph' (Alet LeftHandSideUnit _ bnd scp)
  = mkFullGraph' bnd >> mkFullGraph' scp

mkFullGraph' (Alet lhs u bnd scp) = do
  lenv    <- use buffersEnv
  bndRes  <- mkFullGraph' bnd
  bndResW <- traverse (use . allWriters) bndRes
  c       <- freshComp
  for_ bndRes $ traverse_ (<--> c)
  lenv' <- zoom currEnvL (weakenEnv lhs bndRes lenv)
  symbols %= M.insert c (SLet (bindLHS lhs lenv') (fromSingletonSet $ fold bndResW) u)
  zoom (local lenv') (mkFullGraph' scp)

mkFullGraph' (Return vars) = do
  lenv <- use buffersEnv
  c    <- freshComp
  let (_, bs) = getVarsFromEnv vars lenv
  for_ bs $ traverse_ (<--> c)
  symbols %= M.insert c (SRet lenv vars)
  return bs

mkFullGraph' (Compute expr) = do
  lenv   <- use buffersEnv
  (b, c) <- freshBuff
  for_ (getExpDeps expr lenv) (===> c)
  symbols %= M.insert c (SCmp lenv expr)
  return (tupFlike (expType expr) b)

mkFullGraph' (Alloc shr e sh) = do
  lenv   <- use buffersEnv
  (b, c) <- freshBuff
  for_ (getVarsDeps sh lenv) (===> c)
  symbols %= M.insert c (SAlc lenv shr e sh)
  return (TupFsingle b)

mkFullGraph' (Unit v) = do
  lenv   <- use buffersEnv
  (b, c) <- freshBuff
  for_ (getVarDeps v lenv) (===> c)
  symbols %= M.insert c (SUnt lenv v)
  return (TupFsingle b)

mkFullGraph' (Use sctype n buff) = do
  (b, c) <- freshBuff
  symbols %= M.insert c (SUse sctype n buff)
  return (TupFsingle b)

mkFullGraph' (Acond cond tacc facc) = do
  lenv    <- use buffersEnv
  c_cond  <- freshComp
  c_true  <- freshComp
  c_false <- freshComp
  for_ (getVarDeps cond lenv) (===> c_cond)
  symbols %= M.insert c_cond (SITE lenv cond c_true c_false)
  (t_res, t_wenv, t_renv) <- block c_true  mkFullGraph' tacc
  (f_res, f_wenv, f_renv) <- block c_false mkFullGraph' facc
  writersEnv .= t_wenv <> f_wenv
  readersEnv .= t_renv <> f_renv
  let res = t_res <> f_res
  for_ res $ traverse_ (<--> c_cond)
  return res

mkFullGraph' (Awhile u cond body init) = do
  lenv    <- use buffersEnv
  c_while <- freshComp
  c_cond  <- freshComp
  c_body  <- freshComp
  for_ (getVarsDeps init lenv) (===> c_while)
  symbols %= M.insert c_while (SWhl lenv c_cond c_body init u)
  (_                  , cond_wenv, cond_renv) <- block c_cond mkFullGraphF' cond
  (unsafeCoerce -> res, body_wenv, body_renv) <- block c_body mkFullGraphF' body
  writersEnv .= cond_wenv <> body_wenv
  readersEnv .= cond_renv <> body_renv
  for_ res $ traverse_ (<--> c_while)
  return res



mkFullGraphF' :: forall op env t. MakesILP op
              => FullGraphMaker PreOpenAfun op env t (BuffersTup (Result t))
mkFullGraphF' (Abody acc) = do
  c <- freshComp
  zoom (scope c) do
    res  <- mkFullGraph' acc
    resW <- traverse (use . allWriters) res
    symbols %= M.insert c (SBod (fromSingletonSet $ fold resW))
    return (unsafeCoerce res)

mkFullGraphF' (Alam lhs f) = do
  lenv   <- use buffersEnv
  (b, c) <- freshBuff
  lenv'  <- zoom currEnvL (weakenEnv lhs (tupFlike (lhsToTupR lhs) b) lenv)
  res    <- zoom (local lenv') (mkFullGraphF' f)
  resW   <- traverse (use . allWriters) res
  symbols %= M.insert c (SFun (bindLHS lhs lenv') (fromSingletonSet $ fold resW))
  return res


-- | A block is a subcomputation that is executed under the scope of another
--   computation.
block :: HasCallStack => Label Comp -> FullGraphMaker f op env t (BuffersTup r)
      -> FullGraphMaker f op env t (BuffersTup r, WritersEnv, ReadersEnv)
block c f x = zoom (scope c . protected writersEnv . protected readersEnv) do
  res  <- f x
  -- for_ res $ traverse_ (<--> c)  -- TODO: This generates a reflexive edge?
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
-- returning a Maybe. Uses unsafeCoerce to re-introduce type information implied by the EnvLabels.
mkReindexPartial :: BuffersEnv env -> BuffersEnv env' -> ReindexPartial Maybe env env'
mkReindexPartial env env' idx = go env'
  where
    -- The EnvLabel in the original environment
    e = fst $ lookupIdxInEnv idx env
    go :: forall e a. BuffersEnv e -> Maybe (Idx e a)
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


-- | Converts a singleton set into a value.
--
-- This function is partial and will throw an error if the set is not singleton.
fromSingletonSet :: HasCallStack => Set a -> a
fromSingletonSet (S.toList -> [x]) = x
fromSingletonSet _ = error "fromSingletonSet: Set is not singleton."

traceWith :: (a -> String) -> a -> a
traceWith f a = trace (f a) a


--------------------------------------------------------------------------------
-- Converting Graphs to DOT
--------------------------------------------------------------------------------

-- | Converts a graph to a DOT representation.
toDOT :: FusionGraph -> String
toDOT g = "strict digraph {\n" ++
    -- Make all computation nodes boxes:
    concatMap (\c -> "  <" ++ show c ++ "> [shape=box];\n") (g^.computationNodes) ++
    -- Make all buffer nodes circles:
    concatMap (\b -> "  <" ++ show b ++ "> [shape=circle];\n") (g^.bufferNodes) ++
    -- Make all read and write edges:
    concatMap (\(b, c) -> "  <" ++ show b ++ "> -> <" ++ show c ++ "> [];\n") (g^.readEdges) ++
    concatMap (\(c, b) -> "  <" ++ show c ++ "> -> <" ++ show b ++ "> [];\n") (g^.writeEdges) ++
    -- Make all fusible edges blue:
    concatMap (\(c1, _, c2) -> "  <" ++ show c1 ++ "> -> <" ++ show c2 ++ "> [color=blue];\n") (g^.fusibleEdges) ++
    -- Make all infusible edges red:
    concatMap (\(c1, _, c2) -> "  <" ++ show c1 ++ "> -> <" ++ show c2 ++ "> [color=red];\n") (g^.infusibleEdges) ++
    -- Make all order edges dashed:
    concatMap (\(c1, c2) -> "  <" ++ show c1 ++ "> -> <" ++ show c2 ++ "> [style=dashed];\n") (g^.orderEdges) ++
    "}\n"
