{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}
{-# OPTIONS_HADDOCK hide #-}
-- |
-- Module      : Data.Array.Accelerate.Trafo.Operation.Bounds.Environment
-- Copyright   : [2012..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.Trafo.Operation.Bounds.Environment where

import Data.Array.Accelerate.AST.Environment
import Data.Array.Accelerate.AST.Idx
import Data.Array.Accelerate.AST.IdxSet (IdxSet(..))
import Data.Array.Accelerate.AST.Graph (InEdge(..))
import qualified Data.Array.Accelerate.AST.Graph as Graph
import qualified Data.Array.Accelerate.AST.IdxSet as IdxSet
import Data.Array.Accelerate.AST.LeftHandSide
import Data.Array.Accelerate.AST.Operation
import Data.Array.Accelerate.Analysis.Match
import Data.Array.Accelerate.Trafo.WeakenedEnvironment
import Data.Array.Accelerate.Trafo.Substitution
import Data.Array.Accelerate.Trafo.Exp.Substitution
import Data.Array.Accelerate.Trafo.Operation.Substitution ()
import Data.Array.Accelerate.Representation.Type
import Data.Array.Accelerate.Type
import Data.Array.Accelerate.Error

import qualified Data.Functor.Const as Functor

import Data.Array.Accelerate.Trafo.Operation.Bounds.Algebra

import Data.Maybe
import Data.List (foldl')

type BoundsGraph = Graph.Graph Node Edge

data BoundsEnv benv env = BoundsEnv
  { boundsGraph :: BoundsGraph (UniformEnv benv env)
  -- way to go from index in 'benv' to index in 'UniformEnv benv env'
  , boundsSkipBenv :: Skip (UniformEnv benv env) (Append ((), Int) benv)
  -- reference to the last index in 'UniformEnv benv env', representing the zero value
  , boundsZero :: Idx (UniformEnv benv env) Int
  , boundsBindings :: WEnv Binding benv
  }

data Binding benv t where
  -- No important information
  BindNone :: Binding benv t

  -- This variable is defined with a Compute node
  BindExp :: Exp benv t -> Binding benv t

  -- This variable is defined with an AAssert or AAssume,
  -- and can be synchronised with a Fence
  BindAssertAssume :: Exp benv PrimBool -> Binding benv PrimBool

emptyEnv :: BoundsEnv () ()
emptyEnv = BoundsEnv (Graph.pushNode Graph.empty Node PEnd PEnd) SkipNone ZeroIdx WEmpty

instance Sink Binding where
  weaken _ BindNone = BindNone
  weaken k (BindExp expr) = BindExp $ mapArrayInstr (weaken k) expr
  weaken k (BindAssertAssume expr) = BindAssertAssume $ mapArrayInstr (weaken k) expr

-- | Construct one global environment, consisting of:
-- * One artificial node to represent the constant value zero
-- * All identifiers in the buffer environment
-- * All identifiers in the scalar environment
type UniformEnv benv env = (Append (Append ((), Int) benv) env)

accIdx :: BoundsEnv benv env -> Idx benv t -> Idx (UniformEnv benv env) t
accIdx (BoundsEnv _ s _ _) ix = weaken (skipWeakenIdx s) $ extendIdx @((), Int) ix

-- This function currently assumes that the scalar environment is (),
-- as that is the case in all current uses. If this changes in the future,
-- we can generalize this function. We should then pass a 'BoundsEnv benv env'
-- as argument.
accIdxSet :: IdxSet benv -> IdxSet (UniformEnv benv ())
accIdxSet (IdxSet penv) = IdxSet $ accPartialEnv penv

accPartialEnv :: PartialEnv f benv -> PartialEnv f (UniformEnv benv ())
accPartialEnv (PPush set a) = accPartialEnv set `PPush` a
accPartialEnv (PNone set) = PNone $ accPartialEnv set
accPartialEnv PEnd = PEnd

-- First argument is not used, but by including it in the type,
-- the type becomes non-ambiguous
expIdx :: forall benv env t. BoundsEnv benv env -> Idx env t -> Idx (UniformEnv benv env) t
expIdx _ idx = extendIdx @(Append ((), Int) benv) idx

-- This type is ambiguous. 'lbenv' must always be explicitely instantiated.
extendIdx :: forall lenv renv t. Idx renv t -> Idx (Append lenv renv) t
extendIdx ZeroIdx = ZeroIdx
extendIdx (SuccIdx idx) = SuccIdx $ extendIdx @lenv idx

boundOfAcc :: BoundsEnv benv env -> Idx benv t -> TermBound (UniformEnv benv env) t
boundOfAcc env ix = TermBound
  (mapPartialEnv (\(Graph.InEdge (Edge d)) -> Graph.InEdge $ Edge d) $ Graph.inn (boundsGraph env) ix')
  (mapPartialEnv (\(Edge d) -> Edge d) $ Graph.out (boundsGraph env) ix')
  where
    ix' = accIdx env ix

data Node t = Node

pushScalar :: BoundsEnv benv env -> TermBound (UniformEnv benv env) t -> BoundsEnv benv (env, t)
pushScalar (BoundsEnv g s z bs) bound = BoundsEnv
  (Graph.pushNode g Node (lower bound) (partialEnvSkip $ upper bound))
  (SkipSucc' s)
  (SuccIdx z)
  bs

pushScalars :: forall benv env env' t. BoundsEnv benv env -> (ELeftHandSide t env env', TermBounds (UniformEnv benv env) t) -> BoundsEnv benv env'
pushScalars env (LeftHandSideWildcard _, _) = env
pushScalars env (LeftHandSideSingle _, TupRsingle b) = pushScalar env b
pushScalars env (LeftHandSidePair l1 l2, TupRpair p1 p2)
  = pushScalars (pushScalars env (l1, p1)) (l2, mapTupR (weakenBound l1) p2)
  where
    weakenBound :: ELeftHandSide s env1 env2 -> TermBound (UniformEnv benv env1) a -> TermBound (UniformEnv benv env2) a
    weakenBound lhs b = TermBound
      (partialEnvSkipLHS' lhs $ lower b)
      (partialEnvSkipLHS' lhs $ upper b)

    partialEnvSkipLHS' :: ELeftHandSide s env1 env2 -> PartialEnv u (UniformEnv benv env1) -> PartialEnv u (UniformEnv benv env2)
    partialEnvSkipLHS' (LeftHandSideWildcard _) e = e
    partialEnvSkipLHS' (LeftHandSideSingle _)   e = partialEnvSkip e
    partialEnvSkipLHS' (LeftHandSidePair h1 h2) e = partialEnvSkipLHS' h2 $ partialEnvSkipLHS' h1 e
pushScalars _ _ = internalError "Tuple mismatch"

-- | Pushes information to the buffer environment.
-- Note that this can either be a buffer or a scalar value (in the buffer
-- environment).
pushBuffer :: BoundsEnv benv () -> TermBound (UniformEnv benv ()) t -> BoundsEnv (benv, t) ()
pushBuffer (BoundsEnv g _ z bs) bound = BoundsEnv
  (Graph.pushNode g Node (lower bound) (partialEnvSkip $ upper bound))
  SkipNone
  (SuccIdx z)
  (WPushB bs BindNone)

pushBuffers :: BoundsEnv benv () -> (LeftHandSide r t benv benv', TermBounds (UniformEnv benv ()) t) -> BoundsEnv benv' ()
pushBuffers env (LeftHandSideWildcard _, _) = env
pushBuffers env (LeftHandSideSingle _, TupRsingle b) = pushBuffer env b
pushBuffers env (LeftHandSidePair l1 l2, TupRpair p1 p2)
  = pushBuffers (pushBuffers env (l1, p1)) (l2, mapTupR (weakenBound l1) p2)
  where
    weakenBound :: LeftHandSide r s benv1 benv2 -> TermBound (UniformEnv benv1 ()) a -> TermBound (UniformEnv benv2 ()) a
    weakenBound lhs b = TermBound
      (partialEnvSkipLHS' lhs $ lower b)
      (partialEnvSkipLHS' lhs $ upper b)

    partialEnvSkipLHS' :: LeftHandSide r s benv1 benv2 -> PartialEnv u (UniformEnv benv1 ()) -> PartialEnv u (UniformEnv benv2 ())
    partialEnvSkipLHS' (LeftHandSideWildcard _) e = e
    partialEnvSkipLHS' (LeftHandSideSingle _)   e = partialEnvSkip e
    partialEnvSkipLHS' (LeftHandSidePair h1 h2) e = partialEnvSkipLHS' h2 $ partialEnvSkipLHS' h1 e
pushBuffers _ _ = internalError "Tuple mismatch"

makeTransitives :: BoundsEnv benv env -> TermBounds (UniformEnv benv env) t -> TermBounds (UniformEnv benv env) t
makeTransitives env = mapTupR (makeTransitive env)

makeTransitive :: BoundsEnv benv env -> TermBound (UniformEnv benv env) t -> TermBound (UniformEnv benv env) t
makeTransitive env = makeTransitiveLower env . makeTransitiveUpper env

-- | Make the lowerbound transitively closed
makeTransitiveLower :: BoundsEnv benv env -> TermBound (UniformEnv benv env) t -> TermBound (UniformEnv benv env) t
makeTransitiveLower env b = TermBound
  (mapPartialEnv (\(Functor.Const d) -> InEdge $ Edge d) $ partialEnvTail dists)
  (upper b)
  where
    BoundsEnv g _ _ _ = pushScalar env b
    dists = Graph.shortestPathsTo distance g ZeroIdx

-- | Make the upperbound transitively closed
makeTransitiveUpper :: BoundsEnv benv env -> TermBound (UniformEnv benv env) t -> TermBound (UniformEnv benv env) t
makeTransitiveUpper env b = TermBound
  (lower b)
  (mapPartialEnv (\(Functor.Const d) -> Edge d) $ partialEnvTail dists)
  where
    BoundsEnv g _ _ _ = pushScalar env b
    dists = Graph.shortestPathsFrom distance g ZeroIdx

assumeTrue
  :: forall benv env.
     BoundsEnv benv env
  -> OpenExp env benv PrimBool
  -> BoundsEnv benv env
assumeTrue env (PrimApp PrimLAnd (Pair e1 e2)) = assumeTrue (assumeTrue env e1) e2
assumeTrue env (PrimApp PrimLNot expr) = assumeFalse env expr
assumeTrue env (PrimApp (PrimCmp tp c) (Pair e1 e2))
  | NumSingleType (IntegralNumType _) <- tp
  , Just (Exists node1, dist1) <- extractArg e1
  , Just (Exists node2, dist2) <- extractArg e2
  = case c of
    CmpLt ->
      env{ boundsGraph =
        Graph.insertEdgeWith min node1 node2 (Edge $ dist2 - dist1 - 1) $ boundsGraph env
      }

    CmpGtEq ->
      env{ boundsGraph =
        -- Note that node2 and node1 are swapped here, as we encode greater-than as a less-than edge.
        Graph.insertEdgeWith min node2 node1 (Edge $ dist1 - dist2) $ boundsGraph env
      }

    CmpEq ->
      env{ boundsGraph =
        -- Add same edge in both directions
        Graph.insertEdgeWith min node1 node2 (Edge $ dist2 - dist1) $
        Graph.insertEdgeWith min node2 node1 (Edge $ dist1 - dist2) $
        boundsGraph env  
      }

    CmpNEq -> env -- Cannot encode this
    -- TODO: If based on the current bounds information, one operand is the
    -- upper or lowerbound of the other operand, then we can convert not-equals
    -- to less-than, and we can handle that in our analysis.
  where
    extractArg :: OpenExp env benv a -> Maybe (Exists (Idx (UniformEnv benv env)), Integer)
    extractArg (Evar var) = Just (Exists $ expIdx env $ varIdx var, 0)
    extractArg (ArrayInstr (Parameter var) _) = Just (Exists $ accIdx env $ varIdx var, 0)
    extractArg (Const (SingleScalarType (NumSingleType (IntegralNumType t))) value)
      | IntegralDict <- integralDict t = Just (Exists $ boundsZero env, fromIntegral value)
    -- Note that expressions like `var + 1` are not handled. Since these
    -- additions (and subtractions) may overflow, we cannot in general analyse
    -- them safely. We could do a check here to see if we already know no
    -- overflow will occur. Then we could track those scenarios.
    -- Though I don't know how often this would trigger, and if it is thus
    -- worth it to include this in the analysis.
    extractArg _ = Nothing
assumeTrue env _ = env -- Cannot use the information of this expression

assumeFalse :: BoundsEnv benv env -> OpenExp env benv PrimBool -> BoundsEnv benv env
assumeFalse env (PrimApp PrimLOr (Pair e1 e2)) = assumeFalse (assumeFalse env e1) e2
assumeFalse env (PrimApp PrimLNot expr) = assumeTrue env expr
assumeFalse env (PrimApp (PrimCmp tp c) expr)
  | NumSingleType (IntegralNumType _) <- tp
  = assumeTrue env (PrimApp (PrimCmp tp (negateCmp c)) expr)
assumeFalse env _ = env -- Cannot use the information of this expression

assumeTrue' :: env1 :?> env2 -> BoundsEnv benv env2 -> OpenExp env1 benv PrimBool -> BoundsEnv benv env2
assumeTrue' k env (PrimApp PrimLAnd (Pair e1 e2)) = assumeTrue' k (assumeTrue' k env e1) e2
assumeTrue' k env expr
  | Just expr' <- strengthenE k expr = assumeTrue env expr'
  | otherwise = env

-- | Finds an lowerbound on the given term.
-- Only follows a direct edge between the node and zero.
lowerConst :: BoundsEnv benv env -> TermBound (UniformEnv benv env) t -> Maybe Integer
lowerConst (BoundsEnv _ _ zero _) b = (\(InEdge edge) -> negate $ distance edge) <$> prjPartial zero (lower b)

-- | Finds an upperbound on the given term.
-- Only follows a direct edge between the node and zero.
upperConst :: BoundsEnv benv env -> TermBound (UniformEnv benv env) t -> Maybe Integer
upperConst (BoundsEnv _ _ zero _) b = distance <$> prjPartial zero (upper b)

strengthenBound :: BoundsGraph (env, s) -> TermBound (env, s) t -> TermBound env t
strengthenBound graph bound = TermBound lower' upper'
  where
    lower' = case lower bound of
      PPush edges (InEdge (Edge dist)) ->
        unionPartialEnv (\(InEdge a) (InEdge b) -> InEdge $ min a b) edges
          $ mapPartialEnv (\(InEdge (Edge d)) -> InEdge $ Edge $ d + dist)
          $ partialEnvTail
          $ Graph.inn graph ZeroIdx
      PNone edges -> edges
      PEnd -> PEnd

    upper' = case upper bound of
      PPush edges (Edge dist) ->
        unionPartialEnv min edges
          $ mapPartialEnv (\(Edge d) -> Edge $ d + dist)
          $ partialEnvTail
          $ Graph.out graph ZeroIdx
      PNone edges -> edges
      PEnd -> PEnd

strengthenBoundsWithScalarLHS
  :: forall benv env env' r t s.
     BoundsGraph (UniformEnv benv env')
  -> LeftHandSide r t env env'
  -> TermBounds (UniformEnv benv env') s
  -> (BoundsGraph (UniformEnv benv env), TermBounds (UniformEnv benv env) s)
strengthenBoundsWithScalarLHS graph lhs bound = case lhs of
  LeftHandSideWildcard _ -> (graph, bound)
  LeftHandSideSingle _ -> (Graph.dropNode graph, mapTupR (strengthenBound graph) bound)
  LeftHandSidePair l1 l2
    | (graph', bound') <- strengthenBoundsWithScalarLHS @benv graph l2 bound
    -> strengthenBoundsWithScalarLHS @benv graph' l1 bound'

strengthenBoundsWithBufferLHS
  :: forall benv benv' r t s.
     BoundsGraph (UniformEnv benv' ())
  -> LeftHandSide r t benv benv'
  -> TermBounds (UniformEnv benv' ()) s
  -> (BoundsGraph (UniformEnv benv ()), TermBounds (UniformEnv benv ()) s)
strengthenBoundsWithBufferLHS graph lhs bounds = case lhs of
  LeftHandSideWildcard _ -> (graph, bounds)
  -- Call boundsGraphClearNode before dropNode, to propagate information of the
  -- first node to other nodes. See comment of boundsGraphClearNode
  LeftHandSideSingle _ -> (Graph.dropNode (boundsGraphClearNode graph ZeroIdx), mapTupR (strengthenBound graph) bounds)
  LeftHandSidePair l1 l2
    | (graph', bounds') <- strengthenBoundsWithBufferLHS graph l2 bounds
    -> strengthenBoundsWithBufferLHS graph' l1 bounds'

-- Removes the information of the given node in the graph.
-- Before removing it, it propagates the information on that node to other
-- nodes. For instance, if there is an edge from x to y, and an edge from y to
-- z, and y is removed, then this function adds an edge from x to z (with the
-- sum of the previous two edges).
--
-- This function can be used when the contents of a buffer is overwritten, to
-- invalidate the existing information on that buffer. It can also be used to
-- strengthen an environment, as we then need to drop a variable (node) from
-- the environment (graph) but we still want to preserve the information it
-- implies on other variables (nodes).
boundsGraphClearNode
  :: BoundsGraph env
  -> Idx env t
  -> BoundsGraph env
boundsGraphClearNode graph idx
  = Graph.removeEdgesOf idx
  $ Graph.insertCartesianEdgesWith
    min
    (\(InEdge (Edge a)) (Edge b) -> Edge $ a + b)
    (Graph.inn graph idx)
    (Graph.out graph idx)
    graph

boundsGraphClearNodes
  :: BoundsGraph env
  -> IdxSet env
  -> BoundsGraph env
boundsGraphClearNodes graph set =
  foldl' (\g (Exists idx) -> boundsGraphClearNode g idx) graph
    $ IdxSet.toList set

lookupAssertion
  :: forall benv.
     WEnv Binding benv
  -> Exp benv PrimBool
  -> Maybe (Idx benv PrimBool)
lookupAssertion wenv expr = listToMaybe $ mapMaybe f $ wenvToList wenv
  where
    f :: EnvBinding (Binding benv) benv -> Maybe (Idx benv PrimBool)
    f (EnvBinding idx (BindAssertAssume expr'))
      | Just _ <- matchOpenExp expr expr' = Just idx
    f _ = Nothing
