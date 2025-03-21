{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}

module Data.Array.Accelerate.Trafo.Partitioning.ILP.Graph where


-- accelerate imports
import Data.Array.Accelerate.Array.Buffer
import Data.Array.Accelerate.AST.Idx
import Data.Array.Accelerate.AST.Operation hiding ( Var )
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Labels
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Solver
import Data.Array.Accelerate.Type
import Data.Array.Accelerate.Analysis.Hash.Exp

import Data.Array.Accelerate.Trafo.Operation.LiveVars

-- Data structures
-- In this file, order often subly matters.
-- To keep this clear, we use Set whenever it does not,
-- and [] only when it does. It's also often efficient
-- by removing duplicates.
import Data.Set ( Set )
import Data.Map ( Map )
import qualified Data.Set as S
import qualified Data.Map as M

import Lens.Micro
import Lens.Micro.Mtl
import Lens.Micro.TH

-- GHC imports
import Control.Monad.State
import Data.Kind ( Type )
import Unsafe.Coerce (unsafeCoerce)
import Data.Maybe (isJust, fromJust)
import Data.Array.Accelerate.Representation.Type (TupR)
import Data.Array.Accelerate.AST.LeftHandSide (LeftHandSide (LeftHandSideSingle, LeftHandSideWildcard, LeftHandSidePair, LeftHandSideUnit))
import Data.Array.Accelerate.Representation.Shape (ShapeR)
import Data.Bifunctor (first)
import GHC.Stack
import qualified Debug.Trace

-- | Directed edge (a :-> b): `b` depends on `a`.
-- We only ever want to have these edges if a and b have the same parent, see `-?>` for a safe constructor.
data Edge = Label :-> Label
  deriving (Eq, Ord, Show)

-- | Safe constructor for edges: finds the lowest pairs of ancestors that are in the same subcomputation, and adds the constraint there.
-- Useful if `y` uses some result of `x`, and there is no clear guarantee that they have the same origin. Always gives a legal edge,
-- and if x and y are not equal nor ancestors of each other then it will never return an 'identity edge'.
(-?>) :: Label -> Label -> Edge
x@(Label _ a) -?> y@(Label _ b)
  -- all fromJusts are safe, because @level x > 0 => parent x ~ Just _@
  | a == b            = x          :-> y            -- arrow is legal
  | level x < level y = x          -?> fromJust b   -- y is more deeply nested, so we recurse one up
  | level x > level y = fromJust a -?> y            -- x is more deeply nested, so we recurse one up
  | otherwise         = fromJust a -?> fromJust b   -- they are equally deep, but have different parents. This means that the parent of x must happen before the parent of y

data Graph = Graph
  { _graphNodes     :: Set Label
  , _fusibleEdges   :: Set Edge  -- Can   be fused over, otherwise `a` before `b`.
  , _infusibleEdges :: Set Edge  -- Can't be fused over: always    `a` before `b`.
  } deriving Show
instance Semigroup Graph where
  Graph n f i <> Graph n' f' i' = Graph (n <> n') (f <> f') (i <> i')
instance Monoid Graph where
  mempty = Graph mempty mempty mempty

-- The graph is the 'common part' of the ILP, each backend has to encode its own constraints
-- describing the fusion rules. From the graph, more constraints and bounds will be generated.
data Information op = Info
  { _graphI :: Graph
  , _constr :: Constraint op
  , _bounds :: Bounds op
  }
instance Semigroup (Information op) where
  Info x y z <> Info x' y' z' = Info (x <> x') (y <> y') (z <> z')
instance Monoid (Information op) where
  mempty = Info mempty mempty mempty



data Var (op :: Type -> Type)
  = Pi Label
    -- ^ Used for acyclic ordering of clusters.
    -- Pi (Label x y) = z means that computation number x (possibly a subcomputation of y, see Label) is fused into cluster z (y ~ Just i -> z is a subcluster of the cluster of i)
  | Fused Label Label
    -- ^ 0 is fused (same cluster), 1 is unfused. We do *not* have one of these for all pairs, only the ones we need for constraints and/or costs!
    -- Invariant: Like edges, both labels have to have the same parent: Either on top (Label _ Nothing) or as sub-computation of the same label (Label _ (Just x)).
    -- In fact, this is the Var-equivalent to Edge: an infusible edge has a constraint (== 1).
  | ManifestOutput Label
    -- ^ 0 means manifest, 1 is like a `delayed array`.
    -- Binary variable; will we write the output to a manifest array, or is it fused away (i.e. all uses are in its cluster)?
  | InDir Label
  -- ^ -3 can't fuse with anything, -2 for 'left to right', -1 for 'right to left', n for 'unpredictable, see computation n' (currently only backpermute)
  | OutDir Label -- ^ as InDir, but for the output of this label
  | InFoldSize Label
    -- ^ Keeps track of the fold that's one dimension larger than this operation, and is fused in the same cluster.
    -- This prevents something like `zipWith f (fold g xs) (fold g ys)` from illegally fusing
  | OutFoldSize Label
    -- ^ Keeps track of the fold that's one dimension larger than this operation, and is fused in the same cluster.
    -- This prevents something like `zipWith f (fold g xs) (fold g ys)` from illegally fusing
  | Other String
    -- ^ For one-shot variables that don't deserve a constructor. These are also integer variables, and the responsibility is on the user to pick a unique name!
    -- It is possible to add a variation for continuous variables too, see `allIntegers` in MIP.hs.
    -- We currently use this in Solve.hs for cost functions.
  | BackendSpecific (BackendVar op)
    -- ^ Vars needed to express backend-specific fusion rules.
    -- This is what allows backends to specify how each of the operations can fuse.

deriving instance Eq   (BackendVar op) => Eq   (Var op)
deriving instance Ord  (BackendVar op) => Ord  (Var op) -- for translating to ILP format, see MIP.hs
deriving instance Show (BackendVar op) => Show (Var op)


-- convenience synonyms
pi :: Label -> Expression op
pi l      = c $ Pi l

delayed :: Label -> Expression op
delayed = notB . manifest
manifest :: Label -> Expression op
manifest = c . ManifestOutput
-- | Safe constructor for Fused variables
fused :: HasCallStack => Label -> Label -> Expression op
fused x y = let x' :-> y' = x -?> y
            in if x' /= y' then c $ Fused x' y' else error $ "reflexive fused variable " <> show x'

data LabelledArgOp op env a = LOp (Arg env a) (ALabels a) (BackendArg op)
instance Show (LabelledArgOp op env a) where
  show (LOp _ l _) = show l
type LabelledArgsOp op env = PreArgs (LabelledArgOp op env)

reindexLabelledArgOp :: Applicative f => ReindexPartial f env env' -> LabelledArgOp op env t -> f (LabelledArgOp op env' t)
reindexLabelledArgOp k (LOp (ArgVar vars               ) l o) = (\x -> LOp x l o)  .   ArgVar          <$> reindexVars k vars
reindexLabelledArgOp k (LOp (ArgExp e                  ) l o) = (\x -> LOp x l o)  .   ArgExp          <$> reindexExp k e
reindexLabelledArgOp k (LOp (ArgFun f                  ) l o) = (\x -> LOp x l o)  .   ArgFun          <$> reindexExp k f
reindexLabelledArgOp k (LOp (ArgArray m repr sh buffers) l o) = (\x -> LOp x l o) <$> (ArgArray m repr <$> reindexVars k sh <*> reindexVars k buffers)

reindexLabelledArgsOp :: Applicative f => ReindexPartial f env env' -> LabelledArgsOp op env t -> f (LabelledArgsOp op env' t)
reindexLabelledArgsOp = reindexPreArgs reindexLabelledArgOp

unLabelOp :: LabelledArgsOp op env args -> Args env args
unLabelOp = mapArgs $ \(LOp arg _ _) -> arg

unOpLabels :: LabelledArgsOp op env args -> LabelledArgs env args
unOpLabels = mapArgs $ \(LOp arg l _) -> L arg l

type BackendCluster op = PreArgs (BackendClusterArg op)

class (ShrinkArg (BackendClusterArg op), Eq (BackendVar op), Ord (BackendVar op), Eq (BackendArg op), Show (BackendArg op), Ord (BackendArg op), Show (BackendVar op)) => MakesILP op where
  -- Vars needed to express backend-specific fusion rules.
  type BackendVar op
  -- Information that the backend attaches to the argument for reconstruction,
  -- i.e. to identify when two instances of an array are to be fused.
  type BackendArg op
  defaultBA :: BackendArg op -- anything that's equal to itself

  -- Information that the backend attaches to the cluster, for use in interpreting/code generation.
  data BackendClusterArg op arg
  combineBackendClusterArg :: BackendClusterArg op (Out sh e) -> BackendClusterArg op (In sh e) -> BackendClusterArg op (Var' sh)
  encodeBackendClusterArg :: BackendClusterArg op arg -> Builder


  -- | This function only needs to do the backend-specific things, that is, things which depend on the definition of @op@.
  -- That includes "BackendVar op's" and all their constraints/bounds, but also some (in)fusible edges.
  -- As a conveniece, fusible edges have already been made from all (non-Out) labels in the LabelArgs to the current label.
  -- These can be 'strengthened' by adding a corresponding infusible edge, in which case the fusible edge will later be optimised away.
  mkGraph :: op args -> LabelledArgs env args -> Label -> Information op

  -- using the ILP solution, attach the required information to each argument
  labelLabelledArg :: Solution op -> Label -> LabelledArg env a -> LabelledArgOp op env a
  getClusterArg :: LabelledArgOp op env a -> BackendClusterArg op a

  -- allow the backend to add constraints/bounds for every node
  finalize :: [Label] -> Constraint op

-- use finalize = finalizeNoFusion to prevent all fusion in a backend
finalizeNoFusion :: [Label] -> Constraint op
finalizeNoFusion = foldMap $ \l -> manifest l .==. int 0 -- each array is manifest
                                <> c (InDir  l) .==. int (_labelId l) -- each operation reads in its own order
                                <> c (OutDir l) .==. int (_labelId l) -- each operation writes in its own order


  -- -- e.g. for backpermutes. This allows the backend to say that horizontal fusion should not be possible between
  -- -- two edges from the same source that have different Ints in this map.
  -- -- this default implementation just uses InDir, a backend may choose to change it if other variables are also relevant.
  -- horizontalFusionPreventingIdentifiers :: Solution op -> M.Map Edge Int
  -- horizontalFusionPreventingIdentifiers s
  --   = M.fromList
  --   . concatMap mkedgepairs
  --   . filter (\case
  --     (InDir _,_) -> True
  --     _ -> False)
  --   $ M.toList s
  --   where
  --     mkedgepairs (InDir l, i)
  --       = map (\p -> (p:->l,i))
  --       $ map (\(Fused p _) -> p)
  --       $ filter (\case
  --         Fused _ c -> c==l
  --         _ -> False)
  --       $ M.keys s


-- Control flow cannot be fused, so we make separate ILPs for e.g.
-- then-branch and else-branch. In the future, a possible optimisation is to
-- generate code for the awhile-condition twice: once maybe fused after the body,
-- once maybe fused after input. For now, condition and body are both treated
-- as 'foreign calls', like if-then-else.
-- The Map maps from a label to the corresponding ILP (only for things treated
-- as 'foreign calls', like control flow).
-- A program can result in multiple ILPs, for example, the body of an 'awhile' cannot be fused with anything outside of it.
-- you `can` encode this in the ILP, but since the solutions are independant of each other it should be much more efficient
-- to solve them separately. This avoids many 'infusible edges', and significantly reduces the search space. The extracted
-- subtree gets encoded as a sort of 'foreign call', preventing all fusion. TODO test with 'nested foreign functions':
-- Does the algorithm work if a while contains other Awhile or Acond nodes in its condition or body?


-- In the Operation-based AST, everything is powered by side effects.
-- This makes a full-program analysis like this much more difficult,
-- luckily the Args give us all the information we really require.
-- For each node, we get the set of incoming edges and the set
-- of outgoing edges. Let-bindings are easy, but the array-level
-- control flow (acond and awhile) compensate: their bodies form separate
-- graphs.
-- We can practically ignore 'Return' nodes.
-- Let bindings are more tricky, because of the side effects. Often,
-- a let will not add to the environment but instead mutate it.


-- We put all variables in either FGState or FGResult, so our full traversal is of type
-- @State (FGState env) (FGResult op)@. The state has temporary variables like counters,
-- whereas the result is a monoid of produced information.

-- Not a monoid/semigroup!
data FullGraphState env = FGState
  { _lenv  :: LabelEnv env -- sources of open outgoing edges for env
  , _currL :: Label  -- current counter. Note that this also includes the current parent
  , _currE :: ELabel -- current counter. Use freshL or freshE to get an unused one.
  }
-- | A monoid, so could just put it in the state too. Tradeoff between simplifying code and encoding that this is really 'output info'
data FullGraphResult op = FGRes
  { _info   :: Information op
  , _l_res   :: Maybe Label    -- result
  , _construc :: Map Label (Construction op)
  }
-- Unlawful instances, but useful shorthand. Putting these convenience functions in the typeclass allows use of functions like <>~
instance Semigroup (FullGraphResult op) where
  FGRes x _ z <> FGRes x' _ z' = FGRes (x <> x') Nothing (M.unionWith (error "constrconflict") z z')
instance Monoid (FullGraphResult op) where
  mempty = FGRes mempty Nothing mempty


-- Version of LeftHandSide that doesn't encode the environment type, but has ELabels to allow recreating one on new Labelled environments
data MyLHS s v where
  LHSSingle :: s v -> ELabels -> MyLHS s v
  LHSWildcard :: TupR s v -> MyLHS s v
  LHSPair :: MyLHS s v1 -> MyLHS s v2 -> MyLHS s (v1, v2)

type MyGLHS = MyLHS GroundR

instance Show (MyGLHS v) where
  show (LHSSingle _ x0) = "LHSSingle " <> show x0
  show (LHSWildcard _) = "LHSWild"
  show (LHSPair ml ml') = "LHSPair (" <> show ml <> ") (" <> show ml' <> ")"



unEnvLHS :: LeftHandSide s v env env' -> LabelEnv env' -> MyLHS s v
unEnvLHS (LeftHandSideSingle sv) (l :>>: _) = LHSSingle sv l
unEnvLHS (LeftHandSideWildcard tr) _ = LHSWildcard tr
unEnvLHS (LeftHandSidePair l r) e = LHSPair (unEnvLHS l (stripLHS r e)) (unEnvLHS r e)

stripLHS :: LeftHandSide s v env env' -> LabelEnv env' -> LabelEnv env
stripLHS (LeftHandSideSingle _) (_ :>>: le') = le'
stripLHS (LeftHandSideWildcard _) le = le
stripLHS (LeftHandSidePair l r) le = stripLHS l (stripLHS r le)

createLHS :: MyGLHS a
          -> LabelEnv env
          -> ( forall env'
             . LabelEnv env'
            -> GLeftHandSide a env env'
            -> r)
          -> r
createLHS (LHSSingle g e) env k = k (e :>>: env) (LeftHandSideSingle g)
createLHS (LHSWildcard t) env k = k env (LeftHandSideWildcard t)
createLHS (LHSPair l r)   env k =
  createLHS   l env  $ \env'  l' ->
    createLHS r env' $ \env'' r' ->
      k env'' (LeftHandSidePair l' r')


-- | Information to construct AST nodes. Generally, constructors contain
-- both actual information, and a LabelEnv of the original environment
-- which helps to re-index into the new environment later.
-- next iteration might want to use 'dependant-map', to store some type information at type level.
data Construction (op :: Type -> Type) where
  -- small ugly thing: We make CExe' in this file, then translate it into CExe using the ILP solution.
  -- Duplicating the entire datatype is overkill, and passing the solution to the consumer of Construction
  -- is also ugly.
  CExe' :: LabelEnv env -> LabelledArgs      env args -> op args                         -> Construction op
  CExe  :: LabelEnv env -> LabelledArgsOp op env args -> op args -> Construction op
  CUse  ::                 ScalarType e -> Int -> Buffer e                               -> Construction op
  CITE  :: LabelEnv env -> ExpVar env PrimBool -> Label -> Label                         -> Construction op
  CWhl  :: LabelEnv env -> Label -> Label -> GroundVars env a          -> Uniquenesses a -> Construction op
  CLHS  ::                 MyGLHS a -> Label                           -> Uniquenesses a -> Construction op
  CFun  ::                 MyGLHS a -> Label                                             -> Construction op
  CBod  ::   Label   ->                                                                     Construction op
  CRet  :: LabelEnv env -> GroundVars env a                                              -> Construction op
  CCmp  :: LabelEnv env -> Exp env a                                                     -> Construction op
  CAlc  :: LabelEnv env -> ShapeR sh -> ScalarType e -> ExpVars env sh                   -> Construction op
  CUnt  :: LabelEnv env -> ExpVar env e                                                  -> Construction op
instance Show (Construction op) where
  show CExe{} = "exe"
  show CExe'{} = "exe'"
  show CUse{} = "use"
  show CITE{} = "ite"
  show CWhl{} = "whl"
  show CLHS{} = "lhs"
  show CFun{} = "fun"
  show CBod{}  = "bod"
  show CRet{} = "ret"
  show CCmp{} = "cmp"
  show CAlc{} = "alc"
  show CUnt{} = "unt"

backendConstruc :: forall op. (MakesILP op) => Solution op -> Map Label (Construction op) -> Map Label (Construction op)
backendConstruc sol = M.mapWithKey f
  where
    f :: Label -> Construction op -> Construction op
    f l con = case con of
      CExe{} -> error "already converted???"
      CExe' lenv largs op -> CExe lenv (g l largs) op
      _ -> con
    g :: Label -> LabelledArgs env args -> LabelledArgsOp op env args
    g _ ArgsNil = ArgsNil
    g l (arg :>: args) = labelLabelledArg sol l arg :>: g l args
    -- -- using toAscList and fromAscList is probably slightly faster
    -- smallermap :: Map (BackendVar op) Int
    -- smallermap = M.fromList . map (first (\(BackendSpecific x) -> x)) . filter ((\case
    --                                                     BackendSpecific{} -> True
    --                                                     _ -> False) . fst) $ M.toList sol


-- strips underscores from constructor names
makeLenses ''FullGraphState
makeLenses ''FullGraphResult
makeLenses ''Graph
makeLenses ''Information

-- The below functions use the combination of lenses and the state monad, it seemed the most clear and maintainable
-- solution. Stare at Lens.Micro.Mtl for a while if it doesn't make sense.

makeFullGraph :: (MakesILP op)
              => PreOpenAcc op () a
              -> (Information op, Map Label (Construction op))
makeFullGraph acc = (i & constr <>~ maybe mempty (\l -> manifest l .==. int 0) output, constrM)
  where
    (FGRes i output constrM, _) = runState (mkFullGraph acc) (FGState LabelEnvNil (Label 0 Nothing) 0)

makeFullGraphF :: (MakesILP op)
               => PreOpenAfun op () a
               -> (Information op, Map Label (Construction op))
makeFullGraphF fun = (i, constrM)
  where
    (FGRes i _ constrM, _) = runState (mkFullGraphF fun) (FGState LabelEnvNil (Label 0 Nothing) 0)

mkFullGraph :: forall op env a. (MakesILP op)
            => PreOpenAcc op env a
            -> State (FullGraphState env) (FullGraphResult op)
mkFullGraph (Exec op args) = do
  l <- freshL
  env <- use lenv
  lenv %= flip (updateLabelEnv args) l -- replace the labels of the buffers of output arrays with l
  let labelledArgs = getLabelArgs args env -- uses the old env! Notably, gets the Alloc (or its lhs?) for empty arrays, and the previous writer for Permute
  let    fuseedges = S.map (-?> l) $ getInputArgLabels args env -- add fusible edges to all inputs
  let nonfuseedges = S.map (-?> l) $ getOutputArgLabels args env -- add infusible edges to the allocator/last user of the previous value in the buffer we use for output
  let backInfo = mkGraph op labelledArgs l -- query the backend for its fusion information - we add l and fuseedges next line
  return $ FGRes (backInfo
                    & graphI.graphNodes    %~ S.insert l
                    & graphI.fusibleEdges <>~ fuseedges
                    & graphI.infusibleEdges <>~ nonfuseedges)
                 Nothing
                 (M.singleton l $ CExe' env labelledArgs op)

mkFullGraph (Alet LeftHandSideUnit _ bnd scp) = do
  -- Note that this does not store any LeftHandSides. Instead, in the reconstruction, we will manually insert a LeftHandSideUnit on top of Executes.
  -- This is safe, because Exec is the only ()-returning operation that we cannot ignore on the left side of an Alet.
  res1 <- mkFullGraph bnd
  res2 <- mkFullGraph scp
  return $ (res1 <> res2)
         & l_res .~ (res2 ^. l_res)

-- In contrast to the case above, this case does enforce a strict ordering. Yes, this could prevent fusion that should be legal,
-- but (I think) not in the shapes that we actually get.
-- TODO: check somehow whether this orderng can prevent fusion. Think of a different encoding that doesn't?
-- TODO: check: I think we only ever really generate these non-unit letbindings for binding 1 infusible node (conditional, alloc) at a time?
-- Could enforce this in the types
mkFullGraph (Alet (lhs :: GLeftHandSide bnd env env') u bnd scp) = do
  l <- freshL
  bndRes <- mkFullGraph bnd
  (scpRes, mylhs) <- zoomState lhs l (mkFullGraph scp)
  case scpRes ^. l_res of
    Just scpResL -> return  $ (bndRes <> scpRes)
                            & info.graphI.graphNodes %~ S.insert l
                            & info.graphI.infusibleEdges <>~ S.fromList [ fromJust (bndRes ^. l_res) -?> l
                                                                        ,                          l -?> scpResL
                                                                        ]
                            & construc                    %~ M.insert l (CLHS mylhs (fromJust $ bndRes ^. l_res) u)
                            & l_res                       ?~ scpResL
    -- The right-hand side of this let-binding had no result (e.g. an Execute)
    Nothing -> return $ (bndRes <> scpRes)
                      & info.graphI.graphNodes %~ S.insert l
                      & info.graphI.infusibleEdges <>~ S.singleton (fromJust (bndRes ^. l_res) -?> l)
                      & construc                    %~ M.insert l (CLHS mylhs (fromJust $ bndRes ^. l_res) u)
                      & l_res ?~ l


mkFullGraph (Return vars)    = mkFullGraphHelper $ \env ->
      ( getLabelsTup vars env ^. _2
      , CRet env vars)

mkFullGraph (Compute expr)   = mkFullGraphHelper $ \env ->
      ( getLabelsExp expr env ^. _2
      , CCmp env expr)

mkFullGraph (Alloc shr e sh) = mkFullGraphHelper $ \env ->
      ( getLabelsTup sh env ^. _2
      , CAlc env shr e sh)

mkFullGraph (Unit var)       = mkFullGraphHelper $ \env ->
      ( getLabelsVar var env ^. _2
      , CUnt env var)


mkFullGraph (Use sctype n buff) = do
  l <- freshL
  return $ mempty
         & info.graphI.graphNodes .~ S.singleton l
         & l_res                  ?~ l
         & construc               .~ M.singleton l (CUse sctype n buff)

mkFullGraph (Acond cond tacc facc) = do
  condres <- mkFullGraphHelper $ \env ->
    ( getLabelsVar cond env ^. _2
    , CITE undefined undefined undefined undefined) -- set a placeholder Construction, fill it in at the end
  env <- use lenv
  l_acond <- use currL -- the one set by mkFullGraphHelper
  currL.parent .= Just l_acond -- set the parent of l_true and l_false to be the acond
  l_true  <- freshL
  l_false <- freshL
  -- Set the parent before recursing
  currL.parent .= Just l_true
  tRes <- mkFullGraph tacc
  tEnv <- use lenv
  -- restore environment and set parent before recursing
  lenv .= env
  currL.parent .= Just l_false
  fRes <- mkFullGraph facc
  -- To handle either of the conditional branches writing to a mutable array, we want the union of the resulting states:
  lenv <>= tEnv
  -- Restore the old parent
  currL.parent .= l_acond ^. parent
  return $ (tRes <> fRes <> condres)
         & l_res    ?~ l_acond
         & info.graphI.graphNodes <>~ S.fromList [l_acond, l_true, l_false]
         & construc %~ M.adjust (\CITE{} -> CITE env cond l_true l_false) l_acond

-- like Acond. The biggest difference is that 'cond' is a function instead of an expression here.
-- For the graph, we use 'startvars' much like we used 'cond' in Acond, and we use
-- 'cond' and 'bdy' much like we used 'tbranch' and 'fbranch'.
mkFullGraph (Awhile u cond bdy startvars) = do
  varsres <- mkFullGraphHelper $ \env ->
    ( getLabelsTup startvars env ^. _2
    , CWhl undefined undefined undefined undefined undefined)
  l_while <- use currL
  currL.parent .= Just l_while
  l_cond  <- freshL
  l_body  <- freshL
  env  <- use lenv
  currL.parent .= Just l_cond
  cRes <- mkFullGraphF cond
  cEnv <- use lenv
  lenv .= env
  currL.parent .= Just l_body
  bRes <- mkFullGraphF bdy
  lenv <>= cEnv
  currL.parent .= l_while ^. parent
  return $ (cRes <> bRes <> varsres)
         & l_res    ?~ l_while
         & info.graphI.graphNodes <>~ S.fromList [l_while, l_cond, l_body]
         & construc %~ M.adjust (\CWhl{} -> CWhl env l_cond l_body startvars u) l_while


-- | Like mkFullGraph, but for @PreOpenAfun@.
mkFullGraphF :: (MakesILP op)
             => PreOpenAfun op env a
             -> State (FullGraphState env) (FullGraphResult op)
mkFullGraphF (Abody acc) = do
  l <- freshL
  currL.parent .= Just l
  res <- mkFullGraph acc
  let output = res ^. l_res
  currL.parent .= l ^. parent
  return $ res
         & info . constr <>~ maybe (error "what to do here?") (\l' -> manifest l' .==. int 0) output
         & l_res    ?~ l
         & info.graphI.graphNodes %~ S.insert l
         & construc %~ M.insert l (CBod $ fromJust output)

mkFullGraphF (Alam lhs f) = do
  l <- freshL
  (res, mylhs) <- zoomState lhs l (mkFullGraphF f) -- "zooming" into a _larger_ env
  return $ res
         & l_res    ?~ l
         & info.graphI.graphNodes %~ S.insert l
         & construc %~ M.insert l (CFun mylhs $ fromJust $ res ^. l_res)

-- for the simple cases
mkFullGraphHelper :: (LabelEnv env -> (Labels, Construction op)) -> State (FullGraphState env) (FullGraphResult op)
mkFullGraphHelper f = do
  l <- freshL
  env <- use lenv
  let (labels, con) = f env
  let nonfuse = S.map (-?> l) labels -- TODO add outgoing infusible edges too
  return $ mempty
         & info.graphI.graphNodes %~ S.insert l
         & info.graphI.infusibleEdges .~ nonfuse
         & l_res                      ?~ l
         & construc                   .~ M.singleton l con




-- Create a fresh L or E and update the state. freshL does not change the parent, which is the most common use case
freshL :: State (FullGraphState env) Label
freshL = currL <%= (labelId +~ 1)
freshE :: State (FullGraphState env) ELabel
freshE = zoom currE freshE'

zoomState :: forall env env' a x. GLeftHandSide x env env' -> Label -> State (FullGraphState env') a -> State (FullGraphState env) (a, MyGLHS x)
zoomState lhs l f = do
    env <- use lenv
    env' <- zoom currE (addLhs lhs (S.singleton l) env)
    let mylhs = unEnvLHS lhs env'
    (, mylhs) <$> zoom (zoomStateLens env') f
  where
    -- | This lens allows us to `zoom` into a state computation with a bigger environment,
    -- by first setting `lenv` to `env'`, and afterwards weakening it with `weakLhsEnv`.
    -- It's not a lawful lens (violates `view l (set l v s) ≡ v`), but the only information that is lost
    -- is the part of `LabelEnv env'` that falls outside of `LabelEnv env`. This information is only locally
    -- relevant for the state computations, so the top-level function 'zoomState' is safe.
    -- In other words: this lens is an implementation detail, and I think it's less error prone than manually
    -- wrapping/unwrapping the State (where you can e.g. accidentally use the old environment).
    zoomStateLens :: LabelEnv env' -> Lens' (FullGraphState env) (FullGraphState env')
    zoomStateLens env' changeToScpState bndState = (lenv %~ weakLhsEnv lhs) <$> changeToScpState (bndState & lenv .~ env')


-- TODO do these get used anywhere?
constructExe :: LabelEnv env' -> LabelEnv env
             -> Args env args -> op args
             -> Maybe (PreOpenAcc op env' ())
constructExe env' env args op = Exec op <$> reindexArgs (mkReindexPartial env env') args
constructUse :: ScalarType e -> Int -> Buffer e
             -> PreOpenAcc op env (Buffer e)
constructUse = Use
constructITE :: LabelEnv env' -> LabelEnv env
             -> ExpVar env PrimBool -> PreOpenAcc op env' a -> PreOpenAcc op env' a
             -> Maybe (PreOpenAcc op env' a)
constructITE env' env cond tbranch fbranch = Acond <$> reindexVar (mkReindexPartial env env') cond
                                                   <*> pure tbranch
                                                   <*> pure fbranch
constructWhl :: LabelEnv env' -> LabelEnv env
             -> Uniquenesses a -> PreOpenAfun op env' (a -> PrimBool) -> PreOpenAfun op env' (a -> a) -> GroundVars env a
             -> Maybe (PreOpenAcc op env' a)
constructWhl env' env u cond bdy start = Awhile u cond bdy <$> reindexVars (mkReindexPartial env env') start





-- | Makes a ReindexPartial, which allows us to transform indices in @env@ into indices in @env'@.
-- We cannot guarantee the index is present in env', so we use the partiality of ReindexPartial by
-- returning a Maybe. Uses unsafeCoerce to re-introduce type information implied by the ELabels.
mkReindexPartial :: LabelEnv env -> LabelEnv env' -> ReindexPartial Maybe env env'
mkReindexPartial env env' idx = go env'
  where
    -- The ELabel in the original environment
    e = getELabelIdx idx env
    go :: forall e a. LabelEnv e -> Maybe (Idx e a)
    go ((e',_) :>>: rest) -- e' is the ELabel in the new environment
      -- Here we have to convince GHC that the top element in the environment
      -- really does have the same type as the one we were searching for.
      -- Some literature does this stuff too: 'effect handlers in haskell, evidently'
      -- and 'a monadic framework for delimited continuations' come to mind.
      -- Basically: standard procedure if you're using Ints as a unique identifier
      -- and want to re-introduce type information. :)
      -- Type applications allow us to restrict unsafeCoerce to the return type.
      | e == e' = Just $ unsafeCoerce @(Idx e _)
                                      @(Idx e a)
                                      ZeroIdx
      -- Recurse if we did not find e' yet.
      | otherwise = SuccIdx <$> go rest
    -- If we hit the end, the Elabel was not present in the environment.
    -- That probably means we'll error out at a later point, but maybe there is
    -- a case where we try multiple options? No need to worry about it here.
    go LabelEnvNil = Nothing


-- Not the most efficient implementation.
setMapMaybe :: Ord b => (a -> Maybe b) -> Set a -> Set b
setMapMaybe f = S.mapMonotonic fromJust . S.filter isJust . S.map f

-- | Modify a part of the state by <> it with a value.
-- This exists in Control.Lens, not in Lens.Micro.Mtl
(<>=) :: (MonadState s m, Semigroup a) => ASetter' s a -> a -> m ()
l <>= m = l %= (<> m)

-- Probably exists under some name somewhere, but not in Microlens I think
eitherLens :: Lens' a x -> Lens' b x -> Lens' (Either a b) x
eitherLens ax bx f ab = case ab of
  Left  a -> Left  <$> ax f a
  Right b -> Right <$> bx f b
