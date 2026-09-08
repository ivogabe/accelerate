{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}



-- _Significantly_ speeds up compilation of this file, but at an obvious cost!
-- Even in GHC 9.0.1, which has Lower Your Guards, these checks take some time (though no longer quite as long).
-- Recommended to disable these options when working on this file, and restore them when you're done.
-- {-# OPTIONS_GHC
--   -Wno-overlapping-patterns
--   -Wno-incomplete-patterns
-- #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE BangPatterns #-}

module Data.Array.Accelerate.Trafo.Partitioning.ILP.Clustering where

import Data.Array.Accelerate.AST.LeftHandSide ( Exists(..), LeftHandSide (..), lhsToTupR )
import Data.Array.Accelerate.AST.Partitioned
import Data.Array.Accelerate.AST.Var
import Data.Array.Accelerate.Representation.Type
import Data.Array.Accelerate.Type ( scalarType )
import Data.Array.Accelerate.Trafo.Operation.Simplify
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Graph hiding (readEdges, writeEdges, strictEdges, dataflowEdges, symbols, graph)
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Labels
import Data.Array.Accelerate.Analysis.Match
import Data.Array.Accelerate.Error

import qualified Data.Map as M
import qualified Data.Graph as G
import qualified Data.Set as S
import Data.Maybe (fromJust)
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Solve (ClusterLs (Execs, NonExec))
import Data.Array.Accelerate.AST.Environment (weakenWithLHS)

import Prelude hiding ( take )
import Lens.Micro.Extras (view)
import Data.Array.Accelerate.Representation.Array (ArrayR (ArrayR))
import Data.Functor.Identity
import qualified Data.Tree as T
import Data.Array.Accelerate.Representation.Shape (shapeType)

import Data.String (fromString)
import qualified Data.Array.Accelerate.Pretty.Operation as P
import qualified Data.Array.Accelerate.Pretty.Exp as P

import Lens.Micro

{-
Within each cluster (Labels), we do a topological sort using the edges in Graph
((a,b) means a before b in ordering). Then, we can simply cons them on top of each other.
Data.Graph (containers) has a nice topological sort.
-}

(!??) :: (Ord a1, Show a1, HasCallStack) => M.Map a1 a2 -> a1 -> a2
map' !?? key = case map' M.!? key of
  Just x -> x
  Nothing -> error ("error: map with keys " <> show (M.keys map') <> " does not contain key " <> show key)

-- instance Show (Exists a) where
--   show (Exists x) = "exis"

-- The caller of this function tells us what the result type should be
-- (namely, what it was before fusion), via an GroundsR.
-- Since fusion goes via an untyped ILP, during reconstruction we need to rebuild the program and temporarily
-- fulfill this contract: if something goes wrong during fusion or at the caller, bad things happen.
reconstruct :: forall op a. (MakesILP op, SimplifyOperation op) => GroundsR a -> Bool -> FusionGraph -> [ClusterLs] -> M.Map (Node Comp) [ClusterLs] -> Symbols op -> ReadDirM -> InplaceM -> PreOpenAcc (Clustered op) () a
reconstruct repr a b c d e f g = case openReconstruct a EnvNil b c d e f g of
          Exists res -> expectType repr res

reconstructF :: forall op a. (MakesILP op, SimplifyOperation op) => PreOpenAfun op () a -> Bool -> FusionGraph -> [ClusterLs] -> M.Map (Node Comp) [ClusterLs] -> Symbols op -> ReadDirM -> InplaceM -> PreOpenAfun (Clustered op) () a
reconstructF original a b c d e f g = case openReconstructF a EnvNil b c (Node 1 Nothing) d e f g of
          Exists res -> expectFunTypeEqual original res


-- ordered list of labels
data ClusterL = ExecL [Node Comp] | NonExecL (Node Comp)
  deriving Show

foldC :: (Node Comp -> b -> b) -> b -> ClusterL -> b
foldC f x (ExecL ls) = foldr f x ls
foldC f x (NonExecL l) = f l x

type ReadDirM = M.Map ReadEdge Int
type InplaceM = M.Map (Node GVal) (Node GVal)

topSort :: Bool -> FusionGraph -> Nodes Comp -> ReadDirM -> [ClusterL]
topSort _ _ (S.toList -> [l]) _ = [ExecL [l]]  -- If the cluster is empty.
topSort singletons (FusionGraph _ _ strictEdges dataflowEdges _) cluster readDirM =
  if singletons then concatMap (map (ExecL . pure)) topsorteds else map ExecL topsorteds
  where
    buildGraph =
            G.graphFromEdges
          . map (\(a,b) -> (a,a,b))
          . M.toList
          . flip (S.fold (\(x,i,y) -> M.adjust ((y,defaultDir):) (x,i))) edges
          . M.fromList
          . map (,[])
          . S.toList

    fedges, fpedges :: S.Set (Node Comp, Node GVal, Node Comp)
    (fedges, fpedges) = S.partition (\(c1, _, c2) -> S.notMember (c1, c2) strictEdges) dataflowEdges

    -- Make a graph of all these labels and their incoming edges (for horizontal fusion)...
    fpparents = S.unions $ S.map (\l -> (S.\\ cluster) $ S.map (\(w,_,_)->w) $ S.filter (\(_,_,r)->l==r) fpedges) cluster
    parents   = (S.\\ fpparents) $ S.unions $ S.map (\l -> (S.\\ cluster) $ S.map (\(w,_,_)->w) $ S.filter (\(_,_,r)->l==r) fedges ) cluster
    parentsPlusEdges :: S.Set (Node Comp, Int, Node Comp) -- (Parent, Order, Target)
    parentsPlusEdges = S.unions $ S.unions $ S.map (\l -> let relevantEdges = S.filter (\(w,_,r)->l==w && r `S.member` cluster) (fedges S.\\ fpedges)
                                                              -- TODO: why not just `ordersWithEdges = S.map (\e@(_ :->b) -> (l,readOrderOf e,b)) relevantEdges`?
                                                              orders = S.map readOrderOf relevantEdges
                                                              ordersWithEdges = S.map (\o -> S.map (\(_,_,r) -> (l,o,r)) $ S.filter (\e-> readOrderOf e == o) relevantEdges) orders
                                                          in ordersWithEdges) parents

    nodes = S.map (,defaultDir) cluster <> S.map (\(x,y,_)-> (x,y)) parentsPlusEdges
    edges = S.union parentsPlusEdges $ S.map (\(a,_,b) -> (a,defaultDir,b)) dataflowEdges
    (graph, getAdj, _) = buildGraph nodes

    -- .. split it into connected components and remove those parents from last step,
    components = map (S.filter (\(l,_)->l `S.member` cluster) . S.fromList . map ((^._1) . getAdj) . T.flatten) $ G.components graph
    -- and make a graph of each of them...
    graphs = if singletons then [buildGraph $ S.map (,defaultDir) cluster] else map buildGraph components
    -- .. and finally, topologically sort each of those to get the labels per cluster sorted on dependencies
    topsorteds = map (\(graph', getAdj', _) -> map (view (_1 . _1) . getAdj') $ G.topSort graph') graphs

    readOrderOf :: HasCallStack => DataflowEdge -> Int
    readOrderOf (_,b,r) = case readDirM M.!? (b,r) of
      Just i  -> i
      Nothing -> error $ "can't get readorder " ++ show (b,r)

    defaultDir = 0


openReconstruct   :: (MakesILP op, SimplifyOperation op)
                  => Bool
                  -> Env aenv
                  -> FusionGraph
                  -> [ClusterLs]
                  -> M.Map (Node Comp) [ClusterLs]
                  -> Symbols op
                  -> ReadDirM
                  -> InplaceM
                  -> Exists (PreOpenAcc (Clustered op) aenv)
openReconstruct  a b c d   e f g h =
    case openReconstruct' a b c d Nothing e f g h of
      Left x  -> x
      Right{} -> error "TODO WALL: NON-EXHAUSTIVE PATTERN MATCH"

openReconstructF  :: (MakesILP op, SimplifyOperation op)
                  => Bool
                  -> Env aenv
                  -> FusionGraph
                  -> [ClusterLs]
                  -> Node Comp
                  -> M.Map (Node Comp) [ClusterLs]
                  -> Symbols op
                  -> ReadDirM
                  -> InplaceM
                  -> Exists (PreOpenAfun (Clustered op) aenv)
openReconstructF a b c d l e f g h =
    case openReconstruct' a b c d (Just l) e f g h of
      Right x -> x
      Left{}  -> error "TODO WALL: NON-EXHAUSTIVE PATTERN MATCH"

openReconstruct' :: forall op aenv. (MakesILP op, SimplifyOperation op) => Bool -> Env aenv -> FusionGraph -> [ClusterLs] -> Maybe (Node Comp) -> M.Map (Node Comp) [ClusterLs] -> Symbols op -> ReadDirM -> InplaceM -> Either (Exists (PreOpenAcc (Clustered op) aenv)) (Exists (PreOpenAfun (Clustered op) aenv))
openReconstruct' singletons labelenv graph clusterslist mlab subclustersmap symbols readDirM inplaceM =
  case mlab of
  Just l  -> Right $ makeASTF labelenv l
  Nothing -> Left $ makeAST labelenv clusters
  where
    mkReindexPartial' :: Env env -> Env env' -> ReindexPartial Maybe env env'
    mkReindexPartial' = mkReindexPartial inplaceM

    -- Make a tree of let bindings

    -- In mkFullGraph, we make sure that the bound body of a let will be in an earlier cluster.
    -- Those are stored in the 'prev' argument.
    -- Note also that we currently assume that the final cluster is the return argument: If all computations are relevant
    -- and our analysis is sound, the return argument should always appear last. If not.. oops
    makeAST :: forall env. Env env -> [ClusterL] -> Exists (PreOpenAcc (Clustered op) env)
    makeAST _ [] = error "empty AST"
    makeAST env [cluster] = case makeCluster env cluster of
      Fold c args -> Exists $ Exec c $ unLabelOp args
      InitFold o l args -> singleton l args o $
                            \c args' ->
                                Exists $ Exec c (mapArgs (\(LOp a _ _) -> a) args')
      EmptyFold -> Exists $ Return TupRunit
      NotFold con -> case con of
        SExe {}    -> error "should be Fold/InitFold!"
        SExe'{}    -> error "should be Fold/InitFold!"
        SUse se  n be             -> Exists $ Use se n be
        SITE env' c t f   -> case (makeAST env (subcluster t), makeAST env (subcluster f)) of
          (Exists tacc, Exists facc) -> Exists $ tryBuildAcond
            (fromJust $ reindexVar (mkReindexPartial' env' env) c)
            tacc
            facc
        SWhl env' c b i u -> case (subcluster c, subcluster b) of
          (findTopOfF -> c', findTopOfF -> b') -> case (makeASTF env c', makeASTF env b') of
            (Exists cfun, Exists bfun) -> Exists $ tryBuildAwhile
              u
              cfun
              bfun
              (fromJust $ reindexVars (mkReindexPartial' env' env) i)
        SLet {} -> error "let without scope"
        SFun {} -> error "wrong type: function"
        SBod {} -> error "wrong type: function"
        SBlk {} -> error "wrong type: block"
        SRet env' vars     -> Exists $ Return          (fromJust $ reindexVars (mkReindexPartial' env' env) vars)
        SCmp env' expr     -> Exists $ Compute         (fromJust $ reindexExp  (mkReindexPartial' env' env) expr)
        SAtr msg env' t    -> Exists $ Atrace msg      (fromJust $ reindexArrayDescriptors (mkReindexPartial' env' env) t)
        SAsr msg env' expr -> Exists $ Aassert msg     (fromJust $ reindexExp  (mkReindexPartial' env' env) expr)
        SAsu env' expr     -> Exists $ Aassume         (fromJust $ reindexExp  (mkReindexPartial' env' env) expr)
        SAlc env' shr e sh -> Exists $ Alloc shr e     (fromJust $ reindexVars (mkReindexPartial' env' env) sh)
        SUnt env' evar     -> Exists $ Unit            (fromJust $ reindexVar  (mkReindexPartial' env' env) evar)
        SFen {} -> Exists $ Return TupRunit -- Fence with no futher terms does nothing
    makeAST env (cluster:ctail) =
      -- TODO: use guards to fuse these two identical cases
      case makeCluster env cluster of
        NotFold con
          | SLet mylhs b u <- con ->
            case makeAST env [NonExecL b] of
              Exists bnd -> createLHS mylhs env $ \env' lhs ->
                case makeAST env' ctail of
                  Exists scp
                    -> Exists $ tryBuildAlet lhs u bnd scp
          | SFen env' set' <- con ->
            case makeAST env ctail of
              Exists next ->
                Exists $ Fence (fromJust $ reindexIdxSet (mkReindexPartial' env' env) set') next
        _ -> let res = makeAST env [cluster] in case cluster of
              ExecL _ -> case (res, makeAST env ctail) of
                (Exists exec@Exec{}, Exists scp) -> Exists $ Alet LeftHandSideUnit (shared TupRunit) exec scp
                (Exists (Return TupRunit), Exists scp) -> Exists scp
                _ -> error "nope"
              NonExecL _ -> makeAST env ctail

    makeASTF :: forall env. Env env -> Node Comp -> Exists (PreOpenAfun (Clustered op) env)
    makeASTF env l = case makeCluster env (NonExecL l) of
      NotFold (SBod _l') -> case makeAST env (subcluster l) of
          Exists acc -> Exists $ Abody acc
      NotFold (SFun lhs l') -> createLHS lhs env $ \env' lhs' ->
        case makeASTF env' l' of
          Exists fun -> Exists $ Alam lhs' fun
      NotFold _sym -> error $ "wrong type: acc"
      _ -> error "not a notfold"

    findTopOfF :: [ClusterL] -> Node Comp
    findTopOfF [] = error "empty list"
    findTopOfF [NonExecL x] = x
    findTopOfF (x@(NonExecL l):xs) = case symbols !?? l of
      SBod _    -> findTopOfF xs
      SFun _ l' -> findTopOfF $ filter (nonExecLNotEqual l') xs ++ [x]
      _ -> error "should be a function"
      -- findTopOfF $ filter (\(NonExecL l) -> Just l /= p) xs ++ [x]
    findTopOfF _ = error "should be a function"

    nonExecLNotEqual :: Node Comp -> ClusterL -> Bool
    nonExecLNotEqual l' = \case
      NonExecL l'' -> l'' /= l'
      ExecL{}      -> error "TODO WALL: NON-EXHAUSTIVE PATTERN MATCH"

    -- do the topological sorting for each set
    -- TODO: add 'backend-specific' edges to the graph for sorting, see 3.3.1 in the PLDI paper
    clusters = concatMap (\case
                      Execs ls -> topSort singletons graph ls readDirM
                      NonExec l -> [NonExecL l]) clusterslist
    subclusters = M.map (concatMap ( \case
                      Execs ls  -> topSort singletons graph ls readDirM
                      NonExec l -> [NonExecL l])) subclustersmap

    subcluster :: HasCallStack => Node Comp -> [ClusterL]
    subcluster l = subclusters !?? l

    makeCluster :: HasCallStack => Env env -> ClusterL -> FoldType op env
    makeCluster env (ExecL ls) =
       foldr1 (flip fuseCluster)
                    $ map ( \l -> case symbols !?? l of
                              SExe' env' args op ->
                                -- At first thought, this `fromJust` might error if we fuse an array away.
                                -- It does not: The array will still be in the environment, but after we finish
                                -- the `foldr1`, the input argument will dissapear. The output argument does not:
                                -- we clean that up in the SLV pass, if this was vertical fusion. If this is diagonal fusion,
                                -- it stays.
                                let args' = fromJust $ reindexLabelledArgsOp (mkReindexPartial inplaceM env' env) args
                                in
                                  if isNoOp op (unLabelOp args') then
                                    -- Remove operations that became a no-op by in-place updates.
                                    -- For instance, 'map id xs ys' may become 'map id xs xs',
                                    -- which is a no-op.
                                    EmptyFold
                                  else
                                    InitFold op l args'
                              _                 -> error "avoid this next refactor" -- c -> NotFold c
                          ) ls
    makeCluster _ (NonExecL l) = NotFold $ symbols !?? l

    fuseCluster :: FoldType op env -> FoldType op env -> FoldType op env
    fuseCluster EmptyFold f = f
    fuseCluster f EmptyFold = f
    fuseCluster (Fold cluster cargs) (InitFold op l largs) =
      consCluster l largs op cargs cluster Fold
    fuseCluster (InitFold op l largs) x = singleton l largs op $ \c cargs -> fuseCluster (Fold c cargs) x
    fuseCluster Fold{} Fold{} = error "fuseCluster got non-leaf as second argument" -- Should never happen
    fuseCluster NotFold{}   _ = error "fuseCluster encountered NotFold" -- Should only occur in singleton clusters
    fuseCluster _   NotFold{} = error "fuseCluster encountered NotFold" -- Should only occur in singleton clusters

weakenAcc :: LeftHandSide s t env env' -> PreOpenAcc op env a -> PreOpenAcc op env' a
weakenAcc lhs =  runIdentity . reindexAcc (weakenReindex $ weakenWithLHS lhs)

-- | Internal datatype for `makeCluster`.

data FoldType op env
  = forall args. Fold (Clustered op args) (LabelledArgsOp op env args)
  | forall args. InitFold (op args) (Node Comp) (LabelledArgsOp op env args)
  | EmptyFold
  | NotFold (Symbol op)


louttovar :: LabelledArgOp op env (Out sh e) -> LabelledArgOp op env (Var' sh)
louttovar (LOp a l b) = LOp (outvar a) (NotArr $ getLabelDeps l) b -- unsafe marker: maybe this NotArr ends up a problem?

tryUpdateList :: (a -> Bool) -> (a -> a) -> [a] -> Maybe [a]
tryUpdateList _ _ [] = Nothing
tryUpdateList p f (x : xs)
  | p x = Just $ f x : xs
  | otherwise = tryUpdateList p f xs




consCluster :: forall env args extra op r
             . MakesILP op
            => Node Comp
            -> LabelledArgsOp op env extra
            -> op extra
            -> LabelledArgsOp op env args
            -> Clustered op args
            -> (forall args'. Clustered op args' -> LabelledArgsOp op env args' -> r)
            -> r
consCluster l lop op lcluster cluster k = singleton l lop op $ \c lop' ->
  fuse
    lop'
    lcluster
    lop'
    lcluster
    c
    cluster
    fuseVertically
    $ flip k

fuseVertically :: LabelledArgOp op env (Out sh e) -> LabelledArgOp op env (In sh e) -> LabelledArgOp op env (Var' sh)
fuseVertically
  (LOp (ArgArray Out (ArrayR shr _) sh _) (getLabelDeps -> bs)  b)
  (LOp (ArgArray In  _              _  _) (getLabelDeps -> bs') _)
  = LOp (ArgVar $ groundToExpVar (shapeType shr) sh) (NotArr $ bs <> bs') b

expectType :: HasCallStack => GroundsR t -> PreOpenAcc op env s -> PreOpenAcc op env t
expectType repr term
  | Just Refl <- matchGroundsR repr $ groundsR term = term
  | otherwise
    = internalError $ fromString $
      "Result of fusion has incompatible type.\nExpected: "
      ++ show (P.prettyTupR (const P.prettyGroundR) 0 repr)
      ++ "\nActual: "
      ++ show (P.prettyTupR (const P.prettyGroundR) 0 $ groundsR term)

expectFunTypeEqual :: PreOpenAfun op1 () t -> PreOpenAfun op2 () s -> PreOpenAfun op2 () t
expectFunTypeEqual f1 f2
  | Just Refl <- matchFunType f1 f2 = f2
  | otherwise = internalError "Result of fused function has incompatible type"

matchFunType :: PreOpenAfun op1 env t -> PreOpenAfun op2 env' s -> Maybe (t :~: s)
matchFunType (Alam lhs1 f1) (Alam lhs2 f2)
  | Just Refl <- matchGroundsR (lhsToTupR lhs1) (lhsToTupR lhs2)
  , Just Refl <- matchFunType f1 f2
  = Just Refl
matchFunType (Abody b1) (Abody b2) = matchGroundsR (groundsR b1) (groundsR b2)
matchFunType _ _ = Nothing

tryBuildAcond :: HasCallStack => ExpVar env PrimBool -> PreOpenAcc op env t1 -> PreOpenAcc op env t2 -> PreOpenAcc op env t1
tryBuildAcond cond true false
  | Just Refl <- matchGroundsR (groundsR true) (groundsR false)
  = Acond cond true false
  | otherwise
  = internalError "Cannot reconstruct Acond: branches have incompatible types"

tryBuildAlet
  :: HasCallStack
  => GLeftHandSide t1 env1 env2
  -> Uniquenesses t1
  -> PreOpenAcc op env1 t2
  -> PreOpenAcc op env2 s
  -> PreOpenAcc op env1 s
tryBuildAlet lhs u bnd next
  | Just Refl <- matchGroundsR (lhsToTupR lhs) (groundsR bnd)
  = Alet lhs u bnd next
  | otherwise
  = internalError "Cannot reconstruct Alet: left hand side and binding have incompatible types"

tryBuildAwhile
  :: Uniquenesses a
  -> PreOpenAfun op env c
  -> PreOpenAfun op env s
  -> GroundVars     env a
  -> PreOpenAcc  op env a
tryBuildAwhile u c@(Alam lhsCond (Abody cond)) s@(Alam lhsStep (Abody step)) initial
  | Just Refl <- matchGroundsR tp $ lhsToTupR lhsCond
  , Just Refl <- matchGroundsR (TupRsingle $ GroundRscalar $ scalarType @PrimBool) $ groundsR cond
  , Just Refl <- matchGroundsR tp $ lhsToTupR lhsStep
  , Just Refl <- matchGroundsR tp $ groundsR step
  = Awhile u c s initial
  where
    tp = varsType initial
tryBuildAwhile _ _ _ _ = internalError "Cannot reconstruct Awhile: condition or step has invalid type"
