{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
module Data.Array.Accelerate.Trafo.Partitioning.ILP.Clustering where

import Control.Category
import Data.Array.Accelerate.AST.LeftHandSide
import Data.Array.Accelerate.AST.Partitioned
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Graph
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Labels
import Data.Bifunctor
import Data.Maybe
import Prelude hiding (id, (.))
import qualified Data.Map as M
import Unsafe.Coerce (unsafeCoerce)


-- "open research question"
-- -- Each set of ints corresponds to a set of Constructions, which themselves contain a set of ints (the things they depend on).
-- -- Some of those ints will refer to nodes in previous clusters, others to nodes in this cluster.
-- One pass over these datatypes (back-to-front) should identify the 'output type' of each cluster: which nodes are needed in later clusters?
-- Then, we can construct the clusters front-to-back:
--    identify the nodes that only depend on nodes outside of the cluster, they are the initials
--    the `output type` indicates which nodes we will need to keep: they are all either a final node in the cluster, or get diagonally fused
-- How exactly we can use this information (and a dep. graph) to construct a cluster of ver,hor,diag is not clear.. Will also depend on the exact cluster definition.

{-
Within each cluster (Labels), we do a topological sort using the edges in Graph
((a,b) means a before b in ordering). Then, we can simply insert them front-to-back:
existing `In` arguments are never touched, existing `Out` arguments are matched with
new `In` arguments vertically or diagonally (depending on if they'll be needed still),
new `Out` arguments are never touched. We can even do the re-ordering of Args as we go
on the fresh leaves, never need to touch the existing tree.
  Note that we basically build a list instead of a binary tree. 
  Could refactor Cluster to reflect this.

Data.Graph (containers) has a nice topological sort. Then we just need to know, given
such an ordering, what the live args should be at each point, or even just the death points
of each arg.
-}


-- Note that the return type `a` is not existentially qualified: The caller of this function tells
-- us what the result type should be (namely, what it was before fusion). We use unsafe tricks to
-- fulfill this contract: if something goes wrong during fusion or at the caller, bad things happen.
reconstruct :: forall op a. Graph -> [Labels] -> M.Map Label (Construction op) -> PreOpenAcc (Cluster op) () a
reconstruct a b c = case openReconstruct LabelEnvNil a b c of
          -- see [NOTE unsafeCoerce result type]
          Exists res -> unsafeCoerce @(PartitionedAcc op () _)
                                     @(PartitionedAcc op () a)
                                     res

-- ordered list of labels
type ClusterL = [Label]

-- Internally uses Data.Graph.Graph for utilities. This is nice, maybe refactor to use it all the way?
-- type G.Graph = A.Array Label [Label]
topSortDieMap :: Graph -> Labels -> (M.Map Label Labels, ClusterL)
topSortDieMap = undefined

-- | This function can - and, until it's stable, will - throw errors. 
-- It is very partial, even ignoring the unsafeCoerce:
-- - fromJust calls are used when a re-indexing is expected to succeed
-- - errors are thrown when certain invariants are not met
-- - partial indexing is used in the M.Map Labels
-- none of these situations can be recovered from, so we crash and hope to diagnose the stack trace.
-- Some errors, in particular the second category, which explicitly calls 'error', could reasonably
-- be statically avoided. The rest is a result of the inherently partial practice of constructing
-- a strongly typed AST using the ILP output.
openReconstruct :: forall op aenv. LabelEnv aenv -> Graph -> [Labels] -> M.Map Label (Construction op) -> Exists (PreOpenAcc (Cluster op) aenv)
openReconstruct labelenv graph clustersets construction = undefined
  -- recurseHere labelenv clusters
  -- where
  --   -- do the topological sorting and computing of dieMap for each set
  --   (dieMapC, clusters) =               first mconcat . unzip . map (topSortDieMap graph)  $ clustersets
  --   (dieMapI, ilps) = sequence . M.map (first mconcat . unzip . map (topSortDieMap graph)) $ ilpsets
  --   --                   ^ uses monoid instance of Map Label to union the dieMaps
  --   dieMap = dieMapC <> dieMapI

  --   -- calls makeCluster on each cluster, and let-binds them together.
  --   -- both of these functions still lack something.. need to construct
  --   -- LHS's, but no type information is available. Back to the construction definition?
  --   recurseHere  :: LabelEnv env -> [ClusterL] -> Exists (PreOpenAcc  (Cluster op) env)
  --   recurseHere env = assembleLets . map (`makeCluster` env)
  --   -- recurseHere env []  = error "empty program?"
  --   -- recurseHere env [c] = makeCluster c env
  --   -- recurseHere env (c:cs)                              = recurseHere' env _ cs
    
  --   -- recurseHere' :: LabelEnv env -> PreOpenAcc (Cluster op) env a -> [ClusterL] -> Exists (PreOpenAcc (Cluster op) env)
  --   -- recurseHere' _ acc [] = acc
  --   -- recurseHere' env acc (c:cs) = case makeCluster c env of
  --   --   Exists   (bnd :: PreOpenAcc (Cluster op) env  a) -> case recurseHere _ cs  of
  --   --     Exists (scp :: PreOpenAcc (Cluster op) env' b) ->
  --   --       Exists (Alet _ _ bnd scp)

  --   -- equivalent to the above for PreOpenAfun
  --   -- currently only called by while-loops, both cond and body, both have only 1 argument.
  --   -- this is a scary assumption to make though! Can we just change the definition of Afun
  --   -- to always be uncurried? TODO
  --   recurseHereF :: LabelEnv env -> [ClusterL] -> Exists (PreOpenAfun (Cluster op) env)
  --   recurseHereF env cs = case recurseHere _ cs of
  --     Exists acc -> Exists $ Alam _ $ Abody acc

  --   assembleLets :: [FoldType op env] -> Exists (PreOpenAcc (Cluster op) env)
  --   assembleLets [] = error "impossible"
  --   assembleLets [FT cluster args] = Exists $ Exec cluster args
  --   assembleLets [NotFold acc] = Exists acc
  --   assembleLets [Weaken _] = error "impossible"
  --   assembleLets _ = _

  --       -- makeAcc (FT cluster args) = Exists $ Exec cluster args
  --       -- makeAcc (NotFold acc) = Exists acc
  --   makeCluster :: forall env. 
  --                  ClusterL
  --               -> LabelEnv env
  --               -> FoldType op env -- We don't know the result type of this AST right now
  --   makeCluster [] _ = error "empty cluster"
  --   makeCluster (label:labels) env = foldl cons (makeLeaf label) labels
  --     where
  --       cons :: FoldType op env -> Label -> FoldType op env
  --       cons (FT cluster args) l =
  --         let verticalLabels = dieMap M.! l
  --         in case makeLeaf l of
  --           -- do some swapping and combining. verticalLabels stores the ones that get vertically fused away.
  --           FT (Leaf op Start) args' -> FT (Branch cluster (Leaf op _) _) _
  --             where
  --               _ = _ args args' verticalLabels
  --           FT _ _ -> error "impossible"
  --           _ -> error "cluster contains non-clusterable acc after head"
  --       cons _ _ = error "cluster with size (>1) contains non-clusterable acc at head"

  --       makeLeaf :: Label -> FoldType op env
  --       makeLeaf l = case M.lookup l construction of
  --         Nothing -> error $ "not in construction map: " ++ show l
  --         Just (CExe env' args op) -> FT (Leaf op id) (fromJust $ reindexArgs (mkReindexPartial env' env) args)
  --         Just (CUse sctype buff) -> NotFold $ Use sctype buff
  --         -- for these two, recurse up (so not makeCluster, but its caller or smth) to the point where
  --         -- you can call the sub-ILP.
  --         Just (CITE env' cond t f)                             -> case recurseHere env (ilps M.! t) of
  --           Exists   (tbranch :: PreOpenAcc (Cluster op) env a) -> case recurseHere env (ilps M.! f) of
  --             Exists (fbranch :: PreOpenAcc (Cluster op) env b) ->
  --               NotFold $ Acond (fromJust $ reindexVar (mkReindexPartial env' env) cond)
  --                               tbranch
  --                               -- see [NOTE unsafeCoerce result type]
  --                               (unsafeCoerce @(PreOpenAcc (Cluster op) env b)
  --                                             @(PreOpenAcc (Cluster op) env a)
  --                                             fbranch)
  --         Just (CWhl env' u c b (start :: GroundVars env' a)) -> case recurseHereF env (ilps M.! c) of
  --           Exists   (cond :: PreOpenAfun (Cluster op) env c) -> case recurseHereF env (ilps M.! b) of
  --             Exists (body :: PreOpenAfun (Cluster op) env b) ->
  --               NotFold $ Awhile  u
  --                                 -- see [NOTE unsafeCoerce result type]
  --                                 (unsafeCoerce @(PreOpenAfun (Cluster op) env c)
  --                                               @(PreOpenAfun (Cluster op) env (a -> PrimBool))
  --                                               cond)
  --                                 -- see [NOTE unsafeCoerce result type]
  --                                 (unsafeCoerce @(PreOpenAfun (Cluster op) env b)
  --                                               @(PreOpenAfun (Cluster op) env (a -> a))
  --                                               body)
  --                                 (fromJust $ reindexVars (mkReindexPartial env' env) start)
  --         Just (CLHS lhs _) -> Weaken lhs



-- | Internal datatype for `makeCluster`.

data FoldType op env
  = forall args. FT (Cluster op args) (Args env args) -- add LabelArgs
  -- We say that all Constructions other than Exe are 'not foldable', meaning they cannot be in a cluster:
  -- they are either control-flow, or a 'Use' statement (which we can also safely consider not fusible)
  | forall a. NotFold (PreOpenAcc (Cluster op) env a)
  | forall a env' env''. Weaken (GLeftHandSide a env' env'')

{- [NOTE unsafeCoerce result type]

  Because we lose some type information by rebuilding the AST from scratch, we use
  unsafeCoerce to tell GHC what the result type of the computation is.
  TypeApplications allows us to specify the exact types unsafeCoerce works on,
  which in turn helps retain as much typesafety as possible.

-}
