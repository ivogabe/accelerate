{-# LANGUAGE AllowAmbiguousTypes      #-}
{-# LANGUAGE BlockArguments           #-}
{-# LANGUAGE FlexibleContexts         #-}
{-# LANGUAGE FlexibleInstances        #-}
{-# LANGUAGE FunctionalDependencies   #-}
{-# LANGUAGE GADTs                    #-}
{-# LANGUAGE InstanceSigs             #-}
{-# LANGUAGE KindSignatures           #-}
{-# LANGUAGE LambdaCase               #-}
{-# LANGUAGE RankNTypes               #-}
{-# LANGUAGE ScopedTypeVariables      #-}
{-# LANGUAGE StandaloneDeriving       #-}
{-# LANGUAGE TupleSections            #-}
{-# LANGUAGE TypeFamilyDependencies   #-}
{-# LANGUAGE UndecidableInstances     #-}
{-# LANGUAGE ViewPatterns             #-}
{-# LANGUAGE OverloadedStrings        #-}
{-# OPTIONS_GHC -Wno-orphans          #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE PatternSynonyms #-}
module Data.Array.Accelerate.Trafo.Partitioning.ILP.Graph where

import Prelude hiding ( init, reads )

-- Accelerate imports
import Data.Array.Accelerate.AST.Idx
import Data.Array.Accelerate.AST.IdxSet (IdxSet(..))
import Data.Array.Accelerate.AST.LeftHandSide
import Data.Array.Accelerate.AST.Operation hiding (Var)
import Data.Array.Accelerate.Analysis.Hash.Exp
import Data.Array.Accelerate.Analysis.Match
import Data.Array.Accelerate.Array.Buffer
import Data.Array.Accelerate.Error
import Data.Array.Accelerate.Representation.Shape
import Data.Array.Accelerate.Representation.Type
import Data.Array.Accelerate.Trafo.Operation.LiveVars
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Labels
import Data.Array.Accelerate.Trafo.Partitioning.ILP.ConstraintLanguage (Constraint)
import Data.Array.Accelerate.Trafo.Partitioning.ILP.LinearConstraint
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Solver
import Data.Array.Accelerate.Type

-- Data structures
import Data.Set (Set)
import Data.Map (Map)
import Data.Text (Text)
import qualified Data.Set as S
import qualified Data.Map as M

import Lens.Micro
import Lens.Micro.Mtl

import Control.Monad.State.Strict (State, runState)
import Data.Foldable (Foldable (foldr'), traverse_, toList)
import Data.Kind (Type)


--------------------------------------------------------------------------------
-- Fusion Graph
--------------------------------------------------------------------------------

-- For backwards compatitibility:
pattern (:->) :: Node Comp -> Node Comp -> DataflowEdge
pattern w :-> r <- (w,_,r)


-- | Program graph.
--
-- The graph consists of read/write edges, strict ordering edges and fusible
-- edges.
--
-- The read/write edges represent a read or write relation between a buffer and
-- a computation. In the ILP, these edges get a variable indicating in which
-- order a computation reads or writes an array in the buffer. Some of these
-- edges are duplicated, so we use a smart constructor to make sure they get the
-- same ILP variable.
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
  { _compNodes       :: Set (Node Comp)         -- ^ Computation nodes.
  , _valueNodes      :: Set (Node GVal)         -- ^ Value nodes.
  , _strictEdges     :: Set StrictEdge          -- ^ Edges that enforce strict ordering.
  , _dataflowEdges   :: Set DataflowEdge        -- ^ Edges that represent data-flow.
  , _inplacePaths    :: Map InplacePath Number  -- ^ Summary paths between buffers for in-place updates + their weight.
  , _manifestValues  :: Set (Node GVal)         -- ^ Values forced manifest.
  , _noInplaceValues :: Set (Node GVal)         -- ^ Values that must stay live past every cluster.
  }

instance Semigroup FusionGraph where
  (<>) :: FusionGraph -> FusionGraph -> FusionGraph
  (<>) (FusionGraph c1 v1 s1 d1 i1 m1 p1) (FusionGraph c2 v2 s2 d2 i2 m2 p2)
    = FusionGraph (c1 <> c2) (v1 <> v2) (s1 <> s2) (d1 <> d2) (i1 <> i2) (m1 <> m2) (p1 <> p2)

instance Monoid FusionGraph where
  mempty :: FusionGraph
  mempty = FusionGraph mempty mempty mempty mempty mempty mempty mempty

-- | Class for types that contain a fusion graph.
--
-- This is a manually written version of what microlens-th would generate when
-- using @makeClassy@.
class HasFusionGraph g where
  fusionGraph :: Lens' g FusionGraph

  computationNodes :: Lens' g (Set (Node Comp))
  computationNodes = fusionGraph.computationNodes

  valueNodes :: Lens' g (Set (Node GVal))
  valueNodes = fusionGraph.valueNodes

  strictEdges :: Lens' g (Set StrictEdge)
  strictEdges = fusionGraph.strictEdges

  dataflowEdges :: Lens' g (Set DataflowEdge)
  dataflowEdges = fusionGraph.dataflowEdges

  inplacePaths :: Lens' g (Map InplacePath Number)
  inplacePaths = fusionGraph.inplacePaths

  manifestValues :: Lens' g (Set (Node GVal))
  manifestValues = fusionGraph.manifestValues

  noInplaceValues :: Lens' g (Set (Node GVal))
  noInplaceValues = fusionGraph.noInplaceValues

-- | Base instance of 'HasFusionGraph' for 'FusionGraph'.
--
-- This instance cannot make use of lenses defined in 'HasFusionGraph' because
-- it is the base instance and would otherwise cause a loop.
instance HasFusionGraph FusionGraph where
  fusionGraph :: Lens' FusionGraph FusionGraph
  fusionGraph = id

  computationNodes :: Lens' FusionGraph (Set (Node Comp))
  computationNodes f s = f (_compNodes s) <&> \ns -> s{_compNodes = ns}

  valueNodes :: Lens' FusionGraph (Set (Node GVal))
  valueNodes f s = f (_valueNodes s) <&> \ns -> s{_valueNodes = ns}

  strictEdges :: Lens' FusionGraph (Set StrictEdge)
  strictEdges f s = f (_strictEdges s) <&> \es -> s{_strictEdges = es}

  dataflowEdges :: Lens' FusionGraph (Set DataflowEdge)
  dataflowEdges f s = f (_dataflowEdges s) <&> \es -> s{_dataflowEdges = es}

  inplacePaths :: Lens' FusionGraph (Map InplacePath Number)
  inplacePaths f s = f (_inplacePaths s) <&> \ps -> s{_inplacePaths = ps}

  manifestValues :: Lens' FusionGraph (Set (Node GVal))
  manifestValues f s = f (_manifestValues s) <&> \ns -> s{_manifestValues = ns}

  noInplaceValues :: Lens' FusionGraph (Set (Node GVal))
  noInplaceValues f s = f (_noInplaceValues s) <&> \ns -> s{_noInplaceValues = ns}

insertComputation :: (HasCallStack, HasFusionGraph g) => Node Comp -> g -> g
insertComputation c = computationNodes %~ S.insert c

insertValue :: (HasCallStack, HasFusionGraph g) => Node GVal -> g -> g
insertValue v = valueNodes %~ S.insert v

-- | Insert a strict relation between two computations.
insertStrict :: (HasCallStack, HasFusionGraph g) => StrictEdge -> g -> g
insertStrict (c1, c2) g
  | c1 == c2                           = internalError "reflexive edge"
  | c1^.parent /= c2^.parent           = internalError "different scopes"
  | S.member (c2, c1) (g^.strictEdges) = internalError "cyclic edge"
  | otherwise = g & strictEdges %~ S.insert (c1, c2)

-- | Insert a fusible data-flow edge between two computations.
insertFusible :: (HasCallStack, HasFusionGraph g) => DataflowEdge -> g -> g
insertFusible (c1, b, c2) g
  | c1 == c2                            = internalError "reflexive edge"
  | c1^.parent /= c2^.parent            = internalError "different scopes"
  | S.member (c2, c1) (g^.strictEdges)  = internalError "cyclic edge"
  | otherwise = g & dataflowEdges %~ S.insert (c1, b, c2)

-- | Insert an infusible data-flow edge between two computations.
insertInfusible :: (HasCallStack, HasFusionGraph g) => DataflowEdge -> g -> g
insertInfusible (c1, b, c2) g
  | c1 == c2                            = internalError "reflexive edge"
  | c1^.parent /= c2^.parent            = internalError "different scopes"
  | S.member (c2, c1) (g^.strictEdges)  = internalError "cyclic edge"
  | otherwise = g & dataflowEdges %~ S.insert (c1, b, c2)
                  & strictEdges   %~ S.insert (c1,    c2)

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

readEdges :: HasFusionGraph g => SimpleGetter g (Set ReadEdge)
readEdges = to (\g -> S.map (\(_, b, r) -> (b, r)) (g^.dataflowEdges))

writeEdges :: HasFusionGraph g => SimpleGetter g (Set WriteEdge)
writeEdges = to (\g -> S.map (\(w, b, _) -> (w, b)) (g^.dataflowEdges))

-- | Gets the input edges of a computations.
inputEdgesOf :: HasFusionGraph g => Node Comp -> SimpleGetter g (Set ReadEdge)
inputEdgesOf c = to (\g -> S.filter (\(_, r) -> r == c) (g^.readEdges))

-- | Gets the output edges of a computations.
outputEdgesOf :: HasFusionGraph g => Node Comp -> SimpleGetter g (Set WriteEdge)
outputEdgesOf c = to (\g -> S.filter (\(w, _) -> w == c) (g^.writeEdges))

-- | Gets the read edges of a buffer.
readEdgesOf :: HasFusionGraph g => Node GVal -> SimpleGetter g (Set ReadEdge)
readEdgesOf b = to (\g -> S.filter (\(b',_) -> b' == b) (g^.readEdges))

-- | Gets the write edges of a buffer.
writeEdgesOf :: HasFusionGraph g => Node GVal -> SimpleGetter g (Set WriteEdge)
writeEdgesOf b = to (\g -> S.filter (\(_,b') -> b' == b) (g^.writeEdges))

-- computationNodes :: HasFusionGraph g => SimpleGetter g (Set (Node Comp))
-- computationNodes = to (\g -> S.foldr (\(w,_,r)       -> S.insert w . S.insert r) S.empty (g^.dataflowEdges)
--                           <> S.foldr (\(w,r)         -> S.insert w . S.insert r) S.empty (g^.strictEdges)
--                           <> S.foldr (\((_,r),(w,_)) -> S.insert w . S.insert r) S.empty (M.keysSet $ g^.inplacePaths))

-- bufferNodes :: HasFusionGraph g => SimpleGetter g (Set (Node GVal))
-- bufferNodes = to (\g -> S.map (\(_,b,_) -> b) (g^.dataflowEdges)
--                      <> S.foldr (\((b1,_),(_,b2)) -> S.insert b1 . S.insert b2) S.empty (M.keysSet $ g^.inplacePaths))



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
  , _constraints :: [Constraint op]
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
-- fusion ILP: 'FusionGraphState' and the result of graph construction. This is
-- similar to what microlens-th would generate when using @makeFields@.
class HasFusionILP s op | s -> op where
  fusionILP :: Lens' s (FusionILP op)

graph :: Lens' (FusionILP op) FusionGraph
graph f s = f (_graph s) <&> \g -> s{_graph = g}

constraints :: Lens' (FusionILP op) [Constraint op]
constraints f s = f (_constraints s) <&> \c -> s{_constraints = c}

bounds :: Lens' (FusionILP op) (Bounds op)
bounds f s = f (_bounds s) <&> \b -> s{_bounds = b}

instance HasFusionGraph (FusionILP op) where
  fusionGraph :: Lens' (FusionILP op) FusionGraph
  fusionGraph = graph

-- | Safely add a strict relation between two computations.
--
-- Add a strict edge at the 'ancestors'.
before :: HasCallStack => Node Comp -> Node Comp -> FusionILP op -> FusionILP op
before c1 c2 = maybe id insertStrict (ancestors c1 c2)

-- | Safely add a fusible edge between two computations.
--
-- If in the same subgraph, add a fusible edge, otherwise add an infusible edge.
fusible :: HasCallStack => Node Comp -> Node GVal -> Node Comp -> FusionILP op -> FusionILP op
fusible prod buff cons = if prod^.parent == cons^.parent
  -- Same subgraph, so we can fuse things.
  then insertFusible (prod, buff, cons)
  -- Different subgraph. This may for instance happen if either 'prod' or
  -- 'cons' is placed in an Acond. We cannot fuse over an Acond (or in general,
  -- between subgraphs). Hence we mark this edge as infusible.
  -- Note that 'infusible' needs to do some additional work to find nodes that
  -- are in the same subgraph on which we can add the infusible edge.
  else infusible prod buff cons

-- | Safely add an infusible edge between two computations.
--
infusible :: HasCallStack => Node Comp -> Node GVal -> Node Comp -> FusionILP op -> FusionILP op
-- We must add the edge on nodes in the same subgraph. 'prod' and 'cons' might
-- be in different subgraphs (if their 'parent' is different), which for
-- instance happens when one of them is nested in an Acond or Awhile. Using
-- 'ancestors', we find the first parent nodes that are in the same subgraph,
-- and we add the infusible edge between these nodes.
infusible prod buff cons = case ancestors prod cons of
  Just (prod', cons') -> insertInfusible (prod', buff, cons')
  Nothing -> id

-- | Safely add strict ordering between multiple computations and another computation.
allBefore :: HasCallStack => Nodes Comp -> Node Comp -> FusionILP op -> FusionILP op
allBefore cs1 c2 ilp = foldr' (`before` c2) ilp cs1

-- | Safely add fusible edges from all producers to the consumer.
allFusible :: HasCallStack => Nodes Comp -> Node GVal -> Node Comp -> FusionILP op -> FusionILP op
allFusible prods buff cons ilp = foldr' (\prod -> fusible prod buff cons) ilp prods

-- | Safely add infusible edges from all producers to the consumer.
allInfusible :: HasCallStack => Nodes Comp -> Node GVal -> Node Comp -> FusionILP op -> FusionILP op
allInfusible prods buff cons ilp = foldr' (\prod -> infusible prod buff cons) ilp prods

-- | Infix synonym for 'before'.
(==|-|=>) :: HasCallStack => Node Comp -> Node Comp -> FusionILP op -> FusionILP op
(==|-|=>) = before

-- | Infix synonym for 'fusible'.
(--|) :: HasCallStack => Node Comp -> Node GVal -> Node Comp -> FusionILP op -> FusionILP op
(--|) = fusible

-- | Infix synonym for 'infusible'.
(==|) :: HasCallStack => Node Comp -> Node GVal -> Node Comp -> FusionILP op -> FusionILP op
(==|) = infusible

-- | Infix synonym for 'allBefore'.
(>=|-|=>) :: HasCallStack => Nodes Comp -> Node Comp -> FusionILP op -> FusionILP op
(>=|-|=>) = allBefore

-- | Infix synonym for 'allFusible'.
(>-|) :: HasCallStack => Nodes Comp -> Node GVal -> Node Comp -> FusionILP op -> FusionILP op
(>-|) = allFusible

-- | Infix synonym for 'allInfusible'.
(>=|) :: HasCallStack => Nodes Comp -> Node GVal -> Node Comp -> FusionILP op -> FusionILP op
(>=|) = allInfusible

-- | Arrow heads to complete '(--|)', '(>-|)', '(==|)' and '(>=|)'.
(|->), (|=>) :: (a -> b) -> a -> b
(|->) = ($)
(|=>) = ($)

noInplace :: (HasCallStack, HasFusionGraph g) => Node GVal -> g -> g
noInplace node = noInplaceValues %~ S.insert node

--------------------------------------------------------------------------------
-- Backend specific definitions
--------------------------------------------------------------------------------

-- | The backend has access to a small state so it doesn't accidentally break
--   the state used by the frontend construction algorithm.
data BackendGraphState op env = BackendGraphState
  { _backendFusionILP  :: FusionILP op    -- ^ The entire ILP.
  , _backendBuffersEnv :: Env env  -- ^ The buffers environment (read only).
  , _backendReadersEnv :: ReadersEnv      -- ^ The readers environment (read only).
  , _backendWritersEnv :: WritersEnv      -- ^ The writers environment (read only).
  }

instance HasFusionILP (BackendGraphState op env) op where
  fusionILP :: Lens' (BackendGraphState op env) (FusionILP op)
  fusionILP f s = f (_backendFusionILP s) <&> \ilp -> s{_backendFusionILP = ilp}

instance HasBuffersEnv (BackendGraphState op env) (BackendGraphState op env') env env' where
  environment :: Lens (BackendGraphState op env) (BackendGraphState op env') (Env env) (Env env')
  environment f s = f (_backendBuffersEnv s) <&> \env -> s{_backendBuffersEnv = env}

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
  labelLabelledArg :: Solution op -> Node Comp -> LabelledArg env a -> LabelledArgOp op env a

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
    :: Node Comp             -- ^ The label of the operation.
    -> op args                -- ^ The operation.
    -> LabelledArgs env args  -- ^ The arguments to the operation.
    -> State (BackendGraphState op env) ()

  -- | This function lets the backend define additional constraints on the ILP.
  finalize :: FusionGraph -> [Constraint op]

-- | Attach backend-specific information to labelled arguments.
labelLabelledArgs :: MakesILP op => Solution op -> Node Comp -> LabelledArgs env args -> LabelledArgsOp op env args
labelLabelledArgs sol l (arg :>: args) = labelLabelledArg sol l arg :>: labelLabelledArgs sol l args
labelLabelledArgs _ _ ArgsNil = ArgsNil

--------------------------------------------------------------------------------
-- ILP Variables
--------------------------------------------------------------------------------

data Var (op :: Type -> Type)
  -- Variables used by fusion:
  = Pi (Node Comp)
    -- ^ Used for acyclic ordering of clusters.
    -- Pi (Node x y) = z means that computation number x (possibly a subcomputation of y, see Node) is fused into cluster z (y ~ Just i -> z is a subcluster of the cluster of i)
  | Fused (Node Comp) (Node Comp)
    -- ^ 0 is fused (same cluster), 1 is unfused. We do *not* have one of these for all pairs, only the ones we need for constraints and/or costs!
    -- Invariant: Like edges, both labels have to have the same parent: Either on top (Node _ Nothing) or as sub-computation of the same label (Node _ (Just x)).
    -- In fact, this is the Var-equivalent to Edge: an infusible edge has a constraint (== 1).
  | IsManifest (Node GVal)
    -- ^ 0 means manifest, 1 is like a `delayed array`.
    -- Binary variable; will we write the output to a manifest array, or is it fused away (i.e. all uses are in its cluster)?
  | ReadDir (Node GVal) (Node Comp)
    -- ^ \-3 can't fuse with anything, -2 for 'left to right', -1 for 'right to left', n for 'unknown', see computation n (currently only backpermute).
  | WriteDir (Node Comp) (Node GVal)
    -- ^ See 'ReadDir'.
  | InFoldSize (Node Comp)  -- Legacy? Probably needs per-edge equivalent
    -- ^ Keeps track of the fold that's one dimension larger than this operation, and is fused in the same cluster.
    -- This prevents something like @zipWith f (fold g xs) (fold g ys)@ from illegally fusing
  | OutFoldSize (Node Comp)  -- Legacy? Probably needs per-edge equivalent
    -- ^ Keeps track of the fold that's one dimension larger than this operation, and is fused in the same cluster.
    -- This prevents something like @zipWith f (fold g xs) (fold g ys)@ from illegally fusing
  | Other String
    -- ^ For one-shot variables that don't deserve a constructor. These are also integer variables, and the responsibility is on the user to pick a unique name!
    -- It is possible to add a variation for continuous variables too, see `allIntegers` in MIP.hs.
    -- We currently use this in Solve.hs for cost functions.
  | BackendSpecific (BackendVar op)
    -- ^ Vars needed to express backend-specific fusion rules.
    -- This is what allows backends to specify how each of the operations can fuse.

  -- Variables introduced for in-place updates:
  | InPlace (Node GVal) (Node Comp) (Node Comp) (Node GVal)
    -- ^ 0 means in-place, 1 means not in-place. The first label is an input of a cluster, the second label is an output of a cluster.
    -- All 'InPlace' variables need to be unique, so we can't omit the computation labels. Taking one path through a cluster is different from taking another.
  | PiMax (Node GVal)
    -- ^ The cluster number of the largest reader of the buffer, since in-place updates are only allowed on the final consumer of an array/buffer.
  | MaxCluster
    -- ^ Upper bound on the larget 'Pi' assigned to any comptation, used by the 'NumClusters'/'Everything' objectives to approximate the cluster count.
  -- | WriteDirPiMax (Node GVal)
  --   -- ^ The write direction of the largest reader of the buffer. This is used to check that all reads of the buffer are in the same direction as the write.

deriving instance Eq   (BackendVar op) => Eq   (Var op)
deriving instance Ord  (BackendVar op) => Ord  (Var op)
deriving instance Show (BackendVar op) => Show (Var op)

-- | Constructor for 'Pi' variables.
pi :: Node Comp -> Expression op
pi = var . Pi

-- | No clue what this is for.
delayed :: MakesILP op => Node GVal -> Expression op
delayed = notB . manifest

-- | Constructor for 'IsManifest' variables.
manifest :: Node GVal -> Expression op
manifest = var . IsManifest

-- | Safe constructor for 'Fused' variables.
fused :: (Node Comp, Node Comp) -> Expression op
fused = var . uncurry Fused

-- | Safe constructor for 'ReadDir' variables.
readDir :: ReadEdge -> Expression op
readDir = var . uncurry ReadDir

-- | Convert a foldable structure of 'ReadEdge' to a list of 'Expression's.
readDirs :: Foldable f => f ReadEdge -> [Expression op]
readDirs = map readDir . toList

-- | Safe constructor for 'WriteDir' variables.
writeDir :: WriteEdge -> Expression op
writeDir = var . uncurry WriteDir

-- | Convert a foldable structure of 'WriteEdge' to a list of 'Expression's.
writeDirs :: Foldable f => f WriteEdge -> [Expression op]
writeDirs = map writeDir . toList

-- | Safe constructor for 'InPlace' variables.
inplace :: InplacePath -> Expression op
inplace ((b1,c1),(c2,b2)) = var $ InPlace b1 c1 c2 b2

-- | Safe constructor for 'PiMax' variables.
pimax :: Node GVal -> Expression op
pimax = var . PiMax

maxCluster :: Expression op
maxCluster = var MaxCluster

dirToInt :: Direction -> Int
dirToInt LeftToRight = -2
dirToInt RightToLeft = -1

inFoldSize :: Node Comp -> Expression op
inFoldSize = var . InFoldSize

outFoldSize :: Node Comp -> Expression op
outFoldSize = var . OutFoldSize

--------------------------------------------------------------------------------
-- Symbol table
--------------------------------------------------------------------------------

data Symbol (op :: Type -> Type) where
  SExe  :: Env env -> LabelledArgs      env args -> op args                            -> Symbol op
  SExe' :: Env env -> LabelledArgsOp op env args -> op args                            -> Symbol op
  SUse  ::            ScalarType e -> Int -> Buffer e                                  -> Symbol op
  SITE  :: Env env -> ExpVar env PrimBool -> Node Comp -> Node Comp                    -> Symbol op
  SWhl  :: Env env -> Node Comp -> Node Comp -> GroundVars env bnd -> Uniquenesses bnd -> Symbol op
  SLet  ::            BoundGLHS bnd env env' -> Node Comp          -> Uniquenesses bnd -> Symbol op
  SFun  ::            BoundGLHS bnd env env' -> Node Comp                              -> Symbol op
  SBod  ::            GroundVals a                                                     -> Symbol op
  SBlk  ::                                                                                Symbol op
  SRet  :: Env env -> GroundVars env a                                                 -> Symbol op
  SCmp  :: Env env -> Exp env a                                                        -> Symbol op
  SAlc  :: Env env -> ShapeR sh -> ScalarType e -> ExpVars env sh                      -> Symbol op
  SUnt  :: Env env -> ExpVar env e                                                     -> Symbol op
  SAtr  :: Text -> Env env -> ArrayDescriptors env t                                   -> Symbol op
  SAsr  :: Text -> Env env -> Exp env PrimBool                                         -> Symbol op
  SAsu  :: Env env -> Exp env PrimBool                                                 -> Symbol op
  SFen  :: Env env -> IdxSet env                                                       -> Symbol op

instance Show (Symbol op) where
  show :: Symbol op -> String
  show (SExe {}) = "Exe"
  show (SExe'{}) = "Exe'"
  show (SUse {}) = "Use"
  show (SITE {}) = "ITE"
  show (SWhl {}) = "Whl"
  show (SLet {}) = "Let"
  show (SFun {}) = "Fun"
  show (SBod {}) = "Bod"
  show (SBlk {}) = "Blk"
  show (SRet {}) = "Ret"
  show (SCmp {}) = "Cmp"
  show (SAlc {}) = "Alc"
  show (SUnt {}) = "Unt"
  show (SAtr {}) = "Atr"
  show (SAsr {}) = "Asr"
  show (SAsu {}) = "Asu"
  show (SFen {}) = "Fen"

-- | Mapping from labels to symbols.
type Symbols op = Map (Node Comp) (Symbol op)

data LabelledArgOp  op env a = LOp (Arg env a) (ArgLabel a) (BackendArg op)
type LabelledArgsOp op env   = PreArgs (LabelledArgOp op env)

instance Show (LabelledArgOp op env a) where
  show :: LabelledArgOp op env a -> String
  show (LOp _ bs _) = show bs

unLabelOp :: LabelledArgsOp op env a -> Args env a
unLabelOp ArgsNil = ArgsNil
unLabelOp ((LOp arg _ _) :>: args) = arg :>: unLabelOp args

reindexLabelledArgOp :: Applicative f => ReindexPartial f env env' -> LabelledArgOp op env t -> f (LabelledArgOp op env' t)
reindexLabelledArgOp k (LOp (ArgVar vars               ) l o) = (\x -> LOp x l o)  .   ArgVar          <$> reindexVars k vars
reindexLabelledArgOp k (LOp (ArgExp e                  ) l o) = (\x -> LOp x l o)  .   ArgExp          <$> reindexExp k e
reindexLabelledArgOp k (LOp (ArgFun f                  ) l o) = (\x -> LOp x l o)  .   ArgFun          <$> reindexExp k f
reindexLabelledArgOp k (LOp (ArgArray m repr sh buffers) l o) = (\x -> LOp x l o) <$> (ArgArray m repr <$> reindexVars k sh <*> reindexVars k buffers)

reindexLabelledArgsOp :: Applicative f => ReindexPartial f env env' -> LabelledArgsOp op env t -> f (LabelledArgsOp op env' t)
reindexLabelledArgsOp = reindexPreArgs reindexLabelledArgOp

attachBackendLabels :: MakesILP op => Solution op -> Symbols op -> Symbols op
attachBackendLabels sol = M.mapWithKey \cases
  l (SExe env largs op) -> SExe' env (labelLabelledArgs sol l largs) op
  _  SExe'{} -> internalError "already converted???"
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
-- The environment is not passed as an argument to 'mkFusionGraph' since it may
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
data FusionGraphState op env = FusionGraphState
  { _fusionILP  :: FusionILP op      -- ^ The ILP information.
  , _buffersEnv :: Env env           -- ^ The label environment.
  , _readersEnv :: ReadersEnv        -- ^ Mapping from buffers to their current consumers.
  , _writersEnv :: WritersEnv        -- ^ Mapping from buffers to their current producers.
  , _allocators :: Allocators        -- ^ Mapping from buffers to their allocator.
  , _symbols    :: Symbols op        -- ^ The symbols for the ILP.
  , _currComp   :: Node Comp         -- ^ The current computation label.
  , _currFence  :: Maybe (Node Comp) -- ^ The current fence. All new nodes should be linked with an edge from currFence, so the fence is placed before that node.
  , _currEnvL   :: EnvLabel          -- ^ The current environment label.
  }

type ReadersEnv = Map (Node GVal) (Nodes Comp)
type WritersEnv = Map (Node GVal) (Nodes Comp)
type Allocators = Map (Node GVal) (Node  Comp)

initialFusionGraphState :: FusionGraphState op ()
initialFusionGraphState = FusionGraphState mempty EnvNil mempty mempty mempty mempty (Node 0 Nothing) Nothing 0

-- instance Show (FusionGraphState op env) where
--   show :: FusionGraphState op env -> String
--   show s = "FusionGraphState { readersEnv=" ++ show (s^.readersEnv) ++
--             ", writersEnv=" ++ show (s^.writersEnv) ++
--             " }"

instance HasFusionILP (FusionGraphState op env) op where
  fusionILP :: Lens' (FusionGraphState op env) (FusionILP op)
  fusionILP f s = f (_fusionILP s) <&> \ilp -> s{_fusionILP = ilp}

class HasBuffersEnv s t env env' | s -> env, t -> env' where
  environment :: Lens s t (Env env) (Env env')

instance HasBuffersEnv (FusionGraphState op env) (FusionGraphState op env') env env' where
  environment :: Lens (FusionGraphState op env) (FusionGraphState op env') (Env env) (Env env')
  environment f s = f (_buffersEnv s) <&> \env -> s{_buffersEnv = env}

class HasReadersEnv s where
  readersEnv :: Lens' s ReadersEnv

instance HasReadersEnv (FusionGraphState op env) where
  readersEnv :: Lens' (FusionGraphState op env) ReadersEnv
  readersEnv f s = f (_readersEnv s) <&> \env -> s{_readersEnv = env}

class HasWritersEnv s where
  writersEnv :: Lens' s WritersEnv

instance HasWritersEnv (FusionGraphState op env) where
  writersEnv :: Lens' (FusionGraphState op env) WritersEnv
  writersEnv f s = f (_writersEnv s) <&> \env -> s{_writersEnv = env}

class HasAllocators s where
  allocators :: Lens' s Allocators

instance HasAllocators (FusionGraphState op env) where
  allocators :: Lens' (FusionGraphState op env) Allocators
  allocators f s = f (_allocators s) <&> \alloc -> s{_allocators = alloc}

class HasSymbols s op | s -> op where
  symbols :: Lens' s (Symbols op)

instance HasSymbols (FusionGraphState op env) op where
  symbols :: Lens' (FusionGraphState op env) (Symbols op)
  symbols f s = f (_symbols s) <&> \sym -> s{_symbols = sym}

currComp :: Lens' (FusionGraphState op env) (Node Comp)
currComp f s = f (_currComp s) <&> \c -> s{_currComp = c}

currFence :: Lens' (FusionGraphState op env) (Maybe (Node Comp))
currFence f s = f (_currFence s) <&> \c -> s{_currFence = c}

currEnvL :: Lens' (FusionGraphState op env) EnvLabel
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
backendGraphState :: ReadersEnv -> WritersEnv -> Lens' (FusionGraphState op env) (BackendGraphState op env)
backendGraphState renv wenv f s = f (BackendGraphState (s^.fusionILP) (s^.environment) renv wenv)
  <&> \b -> s & fusionILP .~ b^.fusionILP

-- | Lens for getting and setting the writers of a buffer.
-- By default we throw an error if the buffer is not found in the environment.
writers :: HasWritersEnv s => Node GVal -> Lens' s (Nodes Comp)
writers b f s = f (M.findWithDefault msg b (s^.writersEnv)) <&> \cs -> s & writersEnv %~ M.insert b cs
  where msg = internalError "missing writer"

-- | Lens for getting all writers of buffers.
allWriters :: (Foldable f, HasWritersEnv s) => f (Node GVal) -> SimpleGetter s (Nodes Comp)
allWriters bs = to (\s -> foldMap (\b -> s^.writers b) bs)

-- | Lens for getting and setting the readers of a buffer.
-- By default the set of readers is empty.
readers :: HasReadersEnv s => Node GVal -> Lens' s (Nodes Comp)
readers b f s = f (M.findWithDefault S.empty b (s^.readersEnv)) <&> \cs -> s & readersEnv %~ M.insert b cs

-- | Lens for getting all readers of buffers.
allReaders :: (Foldable f, HasReadersEnv s) => f (Node GVal) -> SimpleGetter s (Nodes Comp)
allReaders bs = to (\s -> foldMap (\b -> s^.readers b) bs)

-- | Lens for getting and setting symbol of a computation.
symbol :: HasSymbols s op => Node Comp -> Lens' s (Maybe (Symbol op))
symbol c = symbols.(`M.alterF` c)

-- | Lens for getting and setting the allocator of a buffer. 'symbol' but for
--   buffers.
allocator :: HasAllocators s => Node GVal -> Lens' s (Maybe (Node Comp))
allocator b = allocators.(`M.alterF` b)

-- | Lens for working under the scope of a computation.
--
-- It first sets the parent of the current label to the supplied computation
-- label. Then it applies the function to the 'FusionGraphState' with the now
-- parented label. Finally, it sets the parent of the current label back to the
-- original parent.
scope :: Node Comp -> Lens' (FusionGraphState op env) (FusionGraphState op env)
scope c = with (currComp.parent) (Just c)

local :: Env env' -> Lens' (FusionGraphState op env) (FusionGraphState op env')
local env' f s = (environment .~ s^.environment) <$> f (s & environment .~ env')

-- | Fresh computation label.
freshComp :: State (FusionGraphState op env) (Node Comp)
freshComp = do
  c <- zoom currComp freshL'
  fence' <- use currFence
  case fence' of
    Nothing -> return ()
    Just a -> fusionILP %= a `before` c
  fusionILP %= insertComputation c
  return c

-- | Fresh buffer and the corresponding computation label.
--
-- The implementation of 'writers' makes it so by default the buffer is produced
-- by the computation that allocates it. This is possible because they have the
-- same label just, just different types. We still need to add the read edge to
-- the graph though.
freshGVal :: Node Comp -> State (FusionGraphState op env) (Node GVal)
freshGVal comp = do
  v <- zoom (currComp.asBuff) freshL'
  fusionILP   %= insertValue v
  writers   v .= S.singleton comp
  allocator v ?= comp
  return v


-- | Fresh 'Val'.
freshVal :: Node Comp -> s t -> State (FusionGraphState op env) (Val s t)
freshVal comp tp = val tp <$> freshGVal comp


-- | Fresh 'Vals'.
freshVals :: Node Comp -> TupR s t -> State (FusionGraphState op env) (Vals s t)
freshVals comp = traverseTupR (freshVal comp)


-- | Read from a buffer.
readsBuffers :: HasCallStack => Node Comp -> Nodes GVal -> State (FusionGraphState op env) ()
readsBuffers c = traverse_ \b -> do
  ws <- use $ writers b
  fusionILP %= ws >-|b|-> c
  readers b %= S.insert c

-- | Require a buffer (i.e. to index into it or pass it to a function).
-- TODO: Rename requires -> reads, reads -> input.
requiresBuffers :: HasCallStack => Node Comp -> Nodes GVal -> State (FusionGraphState op env) ()
requiresBuffers c = traverse_ \b -> do
  ws <- use $ writers b
  fusionILP %= ws >=|b|=> c
  readers b %= S.insert c


-- | Write to a buffer.
--
-- For a write to be safe we need to enforce the following:
-- 1. All readers run before the computation.
-- 2. All writers run before the computation.
-- 3. We become the sole writer of the buffer.
-- 4. We clear the readers of the buffer.
writesBuffers :: HasCallStack => Node Comp -> Nodes GVal -> State (FusionGraphState op env) ()
writesBuffers c = traverse_ \b -> do
  rs <- use $ readers b
  ws <- use $ writers b
  fusionILP %= rs >=|-|=> c
  fusionILP %= ws >=|-|=> c
  writers b .= S.singleton c
  readers b .= S.empty

-- | Mutate a buffer.
--
-- For a mutation to be safe we need to enforce the following:
-- 1. All readers run before this computation.
-- 2. All writers are infusible with this computation.
-- 3. We become the sole writer of the buffer.
-- 4. We clear the readers of the buffer.
mutatesBuffers :: HasCallStack => Node Comp -> Nodes GVal -> State (FusionGraphState op env) ()
mutatesBuffers c = traverse_ \b -> do
  rs <- use $ readers b
  ws <- use $ writers b
  fusionILP %= rs >=|-|=> c
  fusionILP %= ws >=|b|=> c
  writers b .= S.singleton c
  readers b .= S.empty

-- | Return a buffer.
--
-- This can be interpreted as mutation with the identity function (i.e. no-op).
-- Since we don't actually change the contents of the buffer, we don't need to
-- enforce 1 and 4.
returnsBuffers :: HasCallStack => Node Comp -> Nodes GVal -> State (FusionGraphState op env) ()
returnsBuffers c = traverse_ \b -> do
  ws <- use $ writers b
  fusionILP %= ws >=|b|=> c
  writers b .= S.singleton c

-- | Bind a buffer to a let.
--
-- This can be interpreted as mutation with the identity function (i.e. no-op).
-- Since we don't actually change the contents of the buffer, we don't need to
-- enforce 1 and 4. We also don't enforce 2, because doing so would prevent all
-- buffers from being non-manifest. (All buffers are bound to a let and
-- infusible edges force manifestation, so all buffers would be manifest.)
bindsBuffers :: HasCallStack => Node Comp -> Nodes GVal -> State (FusionGraphState op env) ()
bindsBuffers c = traverse_ \b -> do
  ws <- use $ writers b
  fusionILP %= ws >-|b|-> c
  writers b .= S.singleton c

-- | Registers that no in-place updates may happen on these variables.
--
-- This is needed when the uses of a variable cannot be fully tracked. This
-- happens when a variable is returned, or used as the input of an awhile loop.
noInplaceBuffers :: Nodes GVal -> State (FusionGraphState op env) ()
noInplaceBuffers = traverse_ \b -> do
  fusionILP %= noInplace b

-- -- | A computation executes another computattion.
-- executes :: HasCallStack => Node Comp -> Node Comp -> State (FusionGraphState op env) ()
-- executes c1 c2 = fusionILP %= c1 ==|-|=> c2



--------------------------------------------------------------------------------
-- Full Graph construction
--------------------------------------------------------------------------------

type FullGraph op = (FusionILP op, Symbols op, Allocators)

-- The 2 instances below can be used to clean up the code in ILP.hs a bit.
instance HasFusionILP (FullGraph op) op where
  fusionILP :: Lens'  (FullGraph op) (FusionILP op)
  fusionILP f (ilp, sym, alloc) = f ilp <&> (,sym,alloc)

instance HasSymbols (FullGraph op) op where
  symbols :: Lens' (FullGraph op) (Symbols op)
  symbols f (ilp, sym, alloc) = f sym <&> (ilp,,alloc)

instance HasAllocators (FullGraph op) where
  allocators :: Lens' (FullGraph op) Allocators
  allocators f (ilp, sym, alloc) = f alloc <&> (ilp,sym,)

-- | Construct the full fusion graph for a program.
mkFullGraph :: MakesILP op => PreOpenAcc op () t -> FullGraph op
mkFullGraph acc = finalizeInplacePaths $ makeManifest (valsNodes res) (s^.fusionILP, s^.symbols, s^.allocators)
  where (res, s) = runState (mkFusionGraph acc) initialFusionGraphState

-- | Construct the full fusion graph for a function.
mkFullGraphF :: MakesILP op => PreOpenAfun op () a -> FullGraph op
mkFullGraphF acc = finalizeInplacePaths (s^.fusionILP, s^.symbols, s^.allocators)
  where (_, s) = runState (mkFusionGraphF acc) initialFusionGraphState

-- | Make the supplied value nodes manifest.
makeManifest :: HasFusionILP g op => Nodes GVal -> g -> g
makeManifest bs = fusionILP.manifestValues <>~ bs

--------------------------------------------------------------------------------
-- FusionGraph construction
--------------------------------------------------------------------------------

-- | Construct the fusion graph of a program.
mkFusionGraph :: forall op env t. MakesILP op
              => PreOpenAcc op env t
              -> State (FusionGraphState op env) (GroundVals t)
mkFusionGraph (Exec op args) = do
  env  <- use environment
  renv <- use readersEnv
  wenv <- use writersEnv
  c    <- freshComp
  let labelledArgs = labelArgs args env
  let inpArrs      = inputArrays labelledArgs
  let outArrs      = outputArrays labelledArgs
  let notArrs      = notArrays labelledArgs
  c `readsBuffers`   (inpArrs `S.difference`   outArrs)
  c `writesBuffers`  (outArrs `S.difference`   inpArrs)
  c `mutatesBuffers` (inpArrs `S.intersection` outArrs)
  c `requiresBuffers` notArrs
  zoom (backendGraphState renv wenv) (mkGraph c op labelledArgs)
  symbol c ?= SExe env labelledArgs op
  return TupRunit

mkFusionGraph (Alet LeftHandSideUnit _ bnd body)
  = mkFusionGraph bnd >> mkFusionGraph body

-- In this definition I assume that whatever the right-hand side returns is
-- produced by a single computation, which is currently true because all
-- instructions attach themselves to the buffer.
mkFusionGraph (Alet lhs u bnd body) = do
  c       <- freshComp  -- TODO: If there is an issue with reconstruction, maybe move this behind "bndRes <- mkFusionGraph bnd". The order in which labels are generate affects the order in which the clusters are interpreted. Previously let-bindings where always in a separate cluster from the bound computation, but now they are usually in the same cluster to prevent all buffers from being manifest. That said, topsort should already be taking care of this ordering issue.
  env     <- use environment
  bndRes  <- mkFusionGraph bnd
  bndResW <- foldMapMTupR (use . allWriters . valNodes) bndRes
  c `bindsBuffers` valsNodes bndRes
  env'    <- zoom currEnvL (weakenEnv lhs bndRes u env)
  symbol c ?= SLet (bindLHS lhs env') (fromSingletonSet bndResW) u
  zoom (local env') (mkFusionGraph body)

mkFusionGraph (Return vars) = do
  env  <- use environment
  retN <- freshComp
  let (_, bs, _) = lookupVars vars env
  retN `returnsBuffers` valsNodes bs
  noInplaceBuffers $ valsNodes bs
  symbol retN ?= SRet env vars
  return bs

mkFusionGraph (Manifest buff) = do
  env  <- use environment
  retN <- freshComp
  let (_, bs, _) = lookupVar buff env
  retN `returnsBuffers` valsNodes bs
  symbol retN ?= SRet env (TupRsingle buff)
  return bs

mkFusionGraph (Compute expr) = do
  c    <- freshComp
  env  <- use environment
  c `requiresBuffers` getExpDeps expr env
  symbol c ?= SCmp env expr
  freshVals c (groundsR expr)

mkFusionGraph (Alloc shr e sh) = do
  c <- freshComp
  env   <- use environment
  c `requiresBuffers` getVarsDeps sh env
  symbol c ?= SAlc env shr e sh
  TupRsingle <$> freshVal c (GroundRbuffer e)

mkFusionGraph (Unit v) = do
  c    <- freshComp
  env <- use environment
  c `requiresBuffers` getVarDeps v env
  symbol c ?= SUnt env v
  TupRsingle <$> freshVal c (GroundRbuffer $ varType v)

mkFusionGraph (Use tp n buff) = do
  c <- freshComp
  symbol c ?= SUse tp n buff
  TupRsingle <$> freshVal c (GroundRbuffer tp)

mkFusionGraph (Acond cond tacc facc) = do
  env    <- use environment
  condN  <- freshComp
  zoom (scope condN) do
    trueN  <- freshComp
    falseN <- freshComp
    symbol condN ?= SITE env cond trueN falseN
    condN `requiresBuffers` getVarDeps cond env  -- If-then-else reads the condition variable,
    _ <- branches                                -- executes "both" branches, and
      (block trueN  $ mkFusionGraph tacc)
      (block falseN $ mkFusionGraph facc)
    res <- freshVals condN (groundsR tacc)
    condN `returnsBuffers` valsNodes res         -- returns the unified result of both branches.
    return res

mkFusionGraph (Awhile u cond body init) = do
  env    <- use environment
  whileN <- freshComp
  res    <- freshVals whileN (groundsR init)
  zoom (scope whileN) do
    condN <- freshComp
    bodyN <- freshComp
    let init_val = lookupVars init env ^. _2
    whileN `requiresBuffers` valsNodes init_val   -- While reads the initial value,
    noInplaceBuffers $ valsNodes init_val
    _ <- branches                                 -- executes "both" the condition and body,
      (block condN $ mkFusionGraphU u cond)
      (block bodyN $ mkFusionGraphU u body)
    symbol whileN ?= SWhl env condN bodyN init u
  return res                                      -- to return a fresh value of the same type as the initial value.

mkFusionGraph (Atrace msg t) = do
  c    <- freshComp
  env  <- use environment
  c `requiresBuffers` getIdxSetDeps (arrayDescriptorsIdxSet t) env
  symbol c ?= SAtr msg env t
  TupRsingle <$> freshVal c (GroundRscalar scalarTypeWord8)

mkFusionGraph (Aassert msg cond) = do
  c    <- freshComp
  env  <- use environment
  c `requiresBuffers` getExpDeps cond env
  symbol c ?= SAsr msg env cond
  TupRsingle <$> freshVal c (GroundRscalar scalarTypeWord8)

mkFusionGraph (Aassume cond) = do
  c    <- freshComp
  env  <- use environment
  c `requiresBuffers` getExpDeps cond env
  symbol c ?= SAsu env cond
  TupRsingle <$> freshVal c (GroundRscalar scalarTypeWord8)

mkFusionGraph (Fence deps next) = do
  c    <- freshComp
  env  <- use environment
  c `requiresBuffers` getIdxSetDeps deps env
  symbol c ?= SFen env deps
  currFence .= Just c -- All later nodes will be placed after this fence
  mkFusionGraph next

-- | Construct the fusion graph of a single-argument function.
mkFusionGraphU :: forall op env s t. (MakesILP op)
               => Uniquenesses s -> PreOpenAfun op env (s -> t)
               -> State (FusionGraphState op env) (Node Comp)
mkFusionGraphU _ (Abody body) = groundFunctionImpossible $ groundsR body
mkFusionGraphU u (Alam lhs f) = do
  lam  <- freshComp
  env  <- use environment
  args <- freshVals lam (lhsToTupR lhs)
  env' <- zoom currEnvL (weakenEnv lhs args u env)
  fun  <- zoom (local env') (mkFusionGraphF f)
  symbol lam ?= SFun (bindLHS lhs env') fun
  return lam



-- | Construct the fusion graph of a function.
mkFusionGraphF :: forall op env t. (MakesILP op)
               => PreOpenAfun op env t
               -> State (FusionGraphState op env) (Node Comp)
mkFusionGraphF (Alam lhs f) = mkFusionGraphU (shared $ lhsToTupR lhs) (Alam lhs f)
mkFusionGraphF (Abody acc) = do
  bodyN <- freshComp
  zoom (scope bodyN) do
    res <- mkFusionGraph acc
    symbol bodyN ?= SBod res
    id %= makeManifest (valsNodes res)
    bodyN `returnsBuffers` valsNodes res
    return bodyN



-- | A block has no effect on the graph, but the added scope they introduce is
--   required by the reconstruction algorithm.
--   The 'SBlk' symbol isn't even needed, because any time we encounter it an
--   error is thrown, but it is somewhat useful for debugging.
block :: Node Comp -> State (FusionGraphState op env) r -> State (FusionGraphState op env) r
block c f = zoom (scope c) $ symbol c ?= SBlk >> f



-- | Helper for if-then-else and while, executing both branches with the same
--   readers and writers environments, then unifying said environments.
branches :: State (FusionGraphState op env) r1
         -> State (FusionGraphState op env) r2
         -> State (FusionGraphState op env) (r1, r2)
branches f1 f2 = do
  -- Store the current readers and writers environments.
  renv <- use readersEnv
  wenv <- use writersEnv
  -- Run the left branch.
  res1 <- f1
  -- Retrieve the readers and writers environments after the branch, then restore them.
  renv' <- readersEnv <<.= renv
  wenv' <- writersEnv <<.= wenv
  -- Run the right branch.
  res2 <- f2
  -- Unify the readers and writers environments.
  readersEnv %= M.unionWith S.union renv'
  writersEnv %= M.unionWith S.union wenv'
  -- Return the results of both branches.
  return (res1, res2)



--------------------------------------------------------------------------------
-- In-place update path extension
--------------------------------------------------------------------------------

-- | Create in-place paths from a computation, one of its inputs and one of its outputs.
mkUnitInplacePaths :: HasCallStack => Number -> Node Comp -> ArgLabel (In sh e) -> ArgLabel (Out sh' e') -> Map InplacePath Number
mkUnitInplacePaths n c = mkInplacePaths n c c


-- | Create in-place paths from 2 computations, an input of the first and an output of the second.
mkInplacePaths :: HasCallStack => Number -> Node Comp -> Node Comp
               -> ArgLabel (In sh e) -> ArgLabel (Out sh' e') -> Map InplacePath Number
mkInplacePaths n r w lIn lOut
  | sameShape lIn lOut
  , bsIn  <- getLabelUniqueArrDeps lIn
  , bsOut <- getLabelUniqueArrDeps lOut
  = foldMap (\bIn -> foldMap (\bOut -> M.singleton ((bIn, r), (w, bOut)) n) bsOut) bsIn
mkInplacePaths _ _ _ _ _ = M.empty


-- | Filters the in-place update paths to only include those that are valid.
filterInplacePaths :: forall op. FullGraph op -> FullGraph op
filterInplacePaths g = g&fusionILP.inplacePaths %~ filterKeys sameElementType
  where
    -- Checks if the input and output have the same element type.
    sameElementType :: InplacePath -> Bool
    sameElementType ((b1, _), (_, b2))
      | Exists tp1 <- getElt b1
      , Exists tp2 <- getElt b2
      , Just Refl <- matchTypeR tp1 tp2 = True
      | otherwise = False

    -- Gets the element size of a buffer.
    getElt :: Node GVal -> Exists TypeR
    getElt b = case (g^.allocator b) >>= (\c -> g^.symbol c) of
      Just (SAlc _ _ e _)      -> Exists $ TupRsingle e
      Just (SUnt _ v)          -> Exists $ TupRsingle $ varType v
      Just (SUse e _ _)        -> Exists $ TupRsingle e
      Just (SFun lhs _)        -> groundsRtoTypeR $ lhsToTupR $ unbindLHS lhs
      Just (SWhl _ _ _ init _) -> groundsRtoTypeR $ groundsR init
      Just _  -> internalError "not an array allocator"
      Nothing -> internalError "no allocator found"

    -- Use exists because we don't know the exact type.
    groundsRtoTypeR :: GroundsR s -> Exists TypeR
    groundsRtoTypeR TupRunit = Exists TupRunit
    groundsRtoTypeR (TupRsingle (GroundRscalar tp)) = Exists $ TupRsingle tp
    groundsRtoTypeR (TupRsingle (GroundRbuffer tp)) = Exists $ TupRsingle tp
    groundsRtoTypeR (TupRpair e1 e2)
      | Exists tp1 <- groundsRtoTypeR e1
      , Exists tp2 <- groundsRtoTypeR e2
      = Exists $ TupRpair tp1 tp2


-- | Finalizes the in-place update paths by combining them and filtering them.
--
-- Using only merging of unit-size in-place paths does not yield a lot of in-place
-- update locations.
-- The better approach seems to be constructing paths from scratch.
-- It is then possible to still use the merging strategy, as it may yield some additional paths.
-- However, in testing it seems that almost no paths are missing.
finalizeInplacePaths :: MakesILP op => FullGraph op -> FullGraph op
finalizeInplacePaths = filterInplacePaths . mkInplacePathsFromClusters


-- | Calculate in-place update paths based on vertical clusters.
-- This approach should be able to find many more in-place update paths than
-- just combining the in-place paths of length 1, because it considers
-- computations that are not directly connected by an in-place path.
mkInplacePathsFromClusters :: forall op. MakesILP op => FullGraph op -> FullGraph op
mkInplacePathsFromClusters g = g&fusionILP.inplacePaths <>~ go initialClusters
  where
    initialClusters :: Set (Node Comp, Node Comp)
    initialClusters = S.map (\c->(c,c)) (g^.fusionILP.computationNodes)

    go :: Set (Node Comp, Node Comp) -> Map InplacePath Number
    go = foldMap $ \(r, w) -> do
      let !selfPath    = clusterInplacePaths r w
      let !selfStepped = S.map (r,) (next w)
      M.union selfPath $! go selfStepped

    -- Get the set of fusible consumers.
    next :: Node Comp -> Nodes Comp
    next = flip (M.findWithDefault S.empty) nextMap

    -- Map from producer to consumers.
    nextMap :: Map (Node Comp) (Nodes Comp)
    nextMap = foldl (flip \(c1,_,c2) -> M.insertWith (<>) c1 (S.singleton c2)) M.empty (g^.fusionILP.fusibleEdges)

    clusterInplacePaths :: Node Comp -> Node Comp -> Map InplacePath Number
    clusterInplacePaths cIn cOut = case (g^.symbol cIn, g^.symbol cOut) of
      (Just (SExe _ largsIn _), Just (SExe _ largsOut _)) ->
        foldMapInputLabels (\lIn -> foldMapOutputLabels (mkInplacePaths 1 cIn cOut lIn) largsOut) largsIn
      _ -> mempty

--------------------------------------------------------------------------------
-- Reconstruction
--------------------------------------------------------------------------------

-- | Makes a ReindexPartial, which allows us to transform indices in @env@ into indices in @env'@.
-- We cannot guarantee the index is present in env', so we use the partiality of ReindexPartial by
-- returning a Maybe. Uses unsafeCoerce to re-introduce type information implied by the EnvLabels.
mkReindexPartial :: forall env env'. Map (Node GVal) (Node GVal) -> Env env -> Env env' -> ReindexPartial Maybe env env'
mkReindexPartial m env env' idx = let node = lookupIdx idx env^._2 in case idxOf (inplaceOf node) env' of
    Just idx' -> Just idx'
    -- Note: we are not yet sure what happens if the variable after in-place updates is not found,
    -- but the variable before in-place updates is found. It might be that this never occurs.
    -- Currently we throw an error in this case.
    -- Instead, we could gracefully fall back to using the original value instead of the one defined by an in-place update.
    -- This is a bit unsafe, because there is no guarantee anything has been written to this value, or even that it exists at all.
    -- That said, I (Timo) think this can only happen when a value is returned, thus causing both the original value and the in-place updated value to be out-of-scope.
    -- The returned value is then stored in another scope, so if the return statement properly replaces the original value with the in-place updated value, then the resulting program should bind the in-place updated value instead of the original.
    -- See https://github.com/ivogabe/accelerate/pull/11#discussion_r2424009960
    Nothing
      | inplaceOf node /= node
      , Just _ <- (idxOf node env') ->
        internalError $ "mkReindexPartial: index of in-place updated buffer not found. Original buffer (without in-place updates taken into account) is available, but using that might not be sound."
      | otherwise -> Nothing
  where
    -- Replace the buffer with the one we will actually write the data to.
    inplaceOf :: GroundVals a -> GroundVals a
    inplaceOf (TupRsingle (Val tp n)) = TupRsingle $ Val tp $ M.findWithDefault n n m
    inplaceOf (TupRpair bs1 bs2) = TupRpair (inplaceOf bs1) (inplaceOf bs2)
    inplaceOf TupRunit = TupRunit

    -- Find the corresponding EnvLabel in the new environment.
    idxOf :: forall e a. GroundVals a -> Env e -> Maybe (Idx e a)
    idxOf bs ((_,bs',_) :>>: rest) -- bs' is the GroundVals in the new environment
      -- Here we have to convince GHC that the top element in the environment
      -- really does have the same type as the one we were searching for.
      -- Some literature does this stuff too: 'effect handlers in haskell, evidently'
      -- and 'a monadic framework for delimited continuations' come to mind.
      -- Basically: standard procedure if you're using Ints as a unique identifier
      -- and want to re-introduce type information. :)
      -- Type applications allow us to restrict unsafeCoerce to the return type.
      | Just Refl <- matchGroundValsType bs bs'
      , bs == bs' = Just ZeroIdx
      -- Recurse if we did not find e' yet.
      | otherwise = SuccIdx <$> idxOf bs rest
    -- If we hit the end, the Elabel was not present in the environment.
    -- That probably means we'll error out at a later point, but maybe there is
    -- a case where we try multiple options? No need to worry about it here.
    idxOf _ EnvNil = Nothing


--------------------------------------------------------------------------------
-- Helpers
--------------------------------------------------------------------------------

-- | Groups a map by a function.
groupByMap :: (Ord k, Ord k') => (k -> v -> k') -> Map k v -> Map k' (Map k v)
groupByMap f = M.foldlWithKey (\m k v -> M.insertWith M.union (f k v) (M.singleton k v) m) M.empty

-- | Groups a set by a function.
groupBySet :: (Ord k, Ord v) => (v -> k) -> Set v -> Map k (Set v)
groupBySet f = S.foldl (\m v -> M.insertWith S.union (f v) (S.singleton v) m) M.empty

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
fromSingletonSet _ = internalError "set is not singleton"

-- | Converts a triple (a, b, c) into ((a, b), c)
tripleToLeftRec :: (a, b, c) -> ((a, b), c)
tripleToLeftRec (x, y, z) = ((x, y), z)

filterKeys :: (k -> Bool) -> Map k a -> Map k a
filterKeys p = M.filterWithKey (\k _ -> p k)

(&&&) :: (a -> Bool) -> (a -> Bool) -> a -> Bool
(&&&) p1 p2 x = p1 x && p2 x



--------------------------------------------------------------------------------
-- Converting Graphs to DOT
--------------------------------------------------------------------------------

-- | Converts a graph to a DOT representation.
toDOT :: FusionGraph -> Symbols op -> String
toDOT g syms = "strict digraph {\n" ++
  concatMap (\c -> "  <" ++ show c ++ "> [shape=box, label=\"" ++ show (syms M.! c) ++ tail (show c) ++ "\"];\n") (g^.computationNodes) ++
  concatMap (\b -> "  <" ++ show b ++ "> [shape=ellipse, label=\"" ++ show b ++ "\"];\n") (g^.valueNodes) ++
  concatMap (\(b,c) -> "  <" ++ show b ++ "> -> <" ++ show c ++ "> [];\n") (g^.readEdges) ++
  concatMap (\(c,b) -> "  <" ++ show c ++ "> -> <" ++ show b ++ "> [];\n") (g^.writeEdges) ++
  concatMap (\((b1, _), (_, b2)) -> "  <" ++ show b1 ++ "> -> <" ++ show b2 ++ "> [color=gray, style=dotted];\n") (M.keysSet $ g^.inplacePaths) ++
  concatMap (\(c1,_,c2) -> "  <" ++ show c1 ++ "> -> <" ++ show c2 ++ "> [color=green];\n") (g^.fusibleEdges) ++
  concatMap (\(c1,_,c2) -> "  <" ++ show c1 ++ "> -> <" ++ show c2 ++ "> [color=red];\n") (g^.infusibleEdges) ++
  concatMap (\(c1,c2) -> "  <" ++ show c1 ++ "> -> <" ++ show c2 ++ "> [style=dashed, color=red];\n") (g^.orderEdges) ++
  "}\n"
