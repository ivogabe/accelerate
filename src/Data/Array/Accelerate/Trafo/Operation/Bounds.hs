{-# LANGUAGE GADTs               #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}
{-# OPTIONS_HADDOCK hide #-}
-- |
-- Module      : Data.Array.Accelerate.Trafo.Operation.Bounds
-- Copyright   : [2012..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.Trafo.Operation.Bounds (
  boundsOptimizeAfun,
  OperationBounds(..),
  -- Default implementations for OperationBounds
  boundsOptimizeOpDefault, boundsOptimizeGenerate,
  boundsOptimizeBackpermute, boundsOptimizeMap,
  boundsOptimizeFold, boundsOptimizeFold1,
  boundsOptimizeScan, boundsOptimizeScan1, boundsOptimizeScan',
  -- Utilities for implementing OperationBounds
  InputBounds(..), OutputBounds(..), InputBoundArgs, OutputBoundArgs,
  boundsOptimizeFun, boundsOptimizeFun1, boundsOptimizeFun2, boundsOptimizeExp,
) where

import Data.Array.Accelerate.AST.Exp
import Data.Array.Accelerate.AST.Environment
import qualified Data.Array.Accelerate.AST.Graph as Graph
import Data.Array.Accelerate.AST.Idx
import Data.Array.Accelerate.AST.IdxSet (IdxSet)
import qualified Data.Array.Accelerate.AST.IdxSet as IdxSet
import Data.Array.Accelerate.AST.LeftHandSide
import Data.Array.Accelerate.AST.Operation
import Data.Array.Accelerate.Trafo.Exp.Shrink
import Data.Array.Accelerate.Trafo.Exp.Simplify
import Data.Array.Accelerate.Trafo.Substitution
import Data.Array.Accelerate.Trafo.WeakenedEnvironment
import Data.Array.Accelerate.Representation.Array
import Data.Array.Accelerate.Representation.Type
import Data.Array.Accelerate.Type
import Data.Array.Accelerate.Error
import Data.Array.Accelerate.Analysis.Match

import Data.Array.Accelerate.Trafo.Operation.Bounds.Algebra
import Data.Array.Accelerate.Trafo.Operation.Bounds.Environment

import Data.Maybe (mapMaybe)
import Data.List (foldl')

boundsOptimizeAfun
  :: forall op f.
     OperationBounds op
  => OperationAfun op () f
  -> OperationAfun op () f
boundsOptimizeAfun = snd . boundsOptimizeOpenAfun emptyEnv

boundsOptimizeOpenAfun
  :: forall benv op f.
     OperationBounds op
  => BoundsEnv benv ()
  -> OperationAfun op benv f
  -> (IdxSet benv, OperationAfun op benv f)
boundsOptimizeOpenAfun env@(BoundsEnv _ _ zero _) = \case
  Alam lhs f
    | env1 <- env `pushBuffers` (lhs, bottomsGround zero $ lhsToTupR lhs)
    , (modified, f') <- boundsOptimizeOpenAfun env1 f ->
      (IdxSet.drop' lhs modified, Alam lhs f')
  Abody acc
    | (modified, _, _, acc') <- boundsOptimizeAcc env acc ->
      (modified, Abody acc')

boundsOptimizeAcc
  :: forall benv op t.
     OperationBounds op
  => BoundsEnv benv ()
  -> OperationAcc op benv t
  -- Returns the set of arrays that have been modified,
  -- A new BoundsEnv (extended with new information from this term),
  -- the bounds of the return value and a transformed term.
  -> (IdxSet benv, BoundsEnv benv (), TermBounds (UniformEnv benv ()) t, OperationAcc op benv t)
boundsOptimizeAcc env@(BoundsEnv _ _ zero bindings) acc = case acc of
  Exec op args
    | modified <- IdxSet.fromList $ argsOutputs args
    , input <- boundsInputs env args
    -- Remove all references to 'modified' in the bounds graph and input
    , (graph', input') <- boundsGraphWithArgsClearNodes (boundsGraph env, input) $ accIdxSet modified
    , env' <- env{ boundsGraph = graph' }
    , (output, args') <- boundsOptimizeOp op env input' args
    , env'' <- envWriteArgs args' output env' -- Update env' with output
    -> (modified, env'', TupRunit, Exec op args')

  Return vars ->
    ( IdxSet.empty
    , env
    , mapTupR (boundVar zero . accIdx env . varIdx) vars
    , Return vars )

  Manifest var
    | ix <- accIdx env $ varIdx var
    -> (IdxSet.empty, env, TupRsingle $ boundVar zero ix, Manifest var)

  Compute expr
    | (bounds, expr') <- boundsOptimizeExp env expr
    -> (IdxSet.empty, env, bounds, Compute expr')

  Unit var
    | bound <- boundVar zero $ accIdx env $ varIdx var
    -> (IdxSet.empty, env, TupRsingle $ castTermBound bound, Unit var)

  Alet lhs uniquenesses bnd body
    | (modified1, env1, bndBounds, bnd') <- boundsOptimizeAcc env bnd
    , env2 <- env1 `pushBuffers` (lhs, bndBounds)
    -- If this binds a single expression, an assertion or an assumption,
    -- mark this binding in the environment
    , env3 <- case lhs of
      LeftHandSideSingle _
        | Compute expr <- bnd -> env2{ boundsBindings = boundsBindings env1 `WPushB` weaken (weakenSucc weakenId) (BindExp expr) }
        | Aassert _ expr <- bnd -> env2{ boundsBindings = boundsBindings env1 `WPushB` weaken (weakenSucc weakenId) (BindAssertAssume expr) }
        | Aassume expr <- bnd -> env2{ boundsBindings = boundsBindings env1 `WPushB` weaken (weakenSucc weakenId) (BindAssertAssume expr) }
      _ -> env2
    , (modified2, env4, bodyBounds, body') <- boundsOptimizeAcc env3 body
    , (graph, bodyBounds') <- strengthenBoundsWithBufferLHS (boundsGraph env4) lhs bodyBounds ->
      ( modified1 `IdxSet.union` IdxSet.drop' lhs modified2
      , env{ boundsGraph = graph }
      , bodyBounds'
      , Alet lhs uniquenesses bnd' body'
      )

  Acond condVar trueOp falseOp
    | cond <- case wprj (varIdx condVar) (boundsBindings env) of
      BindExp expr -> expr
      _ -> ArrayInstr (Parameter condVar) Nil
    , (modified1, _, trueBounds, true') <- boundsOptimizeAcc (assumeTrue env cond) trueOp
    , (modified2, _, falseBounds, false') <- boundsOptimizeAcc (assumeFalse env cond) falseOp
    , modified <- IdxSet.union modified1 modified2
    -- We cannot easily intersect the two environments (yet), so we just remove any
    -- invalid information from the original environment and return that.
    -- TODO: Can we take the intersection of two environments?
    , env' <- env{ boundsGraph = boundsGraphClearNodes (boundsGraph env) $ accIdxSet modified }
    , bounds <- unions (makeTransitives env trueBounds) (makeTransitives env falseBounds)
    -> (modified, env', bounds, Acond condVar true' false')

  Awhile uniquenesses cond step initial
    | (modified1, cond') <- boundsOptimizeOpenAfun env cond
    , (modified2, step') <- boundsOptimizeOpenAfun env step
    , modified <- IdxSet.union modified1 modified2
    , env' <- env{ boundsGraph = boundsGraphClearNodes (boundsGraph env) $ accIdxSet modified }
    -> (modified, env', bottomsGround zero $ mapTupR varType initial, Awhile uniquenesses cond' step' initial)

  Fence set body
    | assertions <-
      mapMaybe
        (\case
          Exists (BindAssertAssume term) -> Just term
          _ -> Nothing
        )
        $ wprjSet set (boundsBindings env)
    , env' <- foldl' assumeTrue env assertions
    , (modified, _, _, body') <- boundsOptimizeAcc env' body
    -- We cannot propagate any information from within the body of this fence.
    -- If we do that, and later act on it, then we may let other code work
    -- without using the values computed here. That may make this code dead,
    -- and that may cause that the assertions referenced by this fence are not
    -- ran.
    --
    -- TODO: If all variables in the set refer to assertions that we already
    -- proved to be true, or assumes, then we can actually keep this
    -- information.
    --
    -- We thus return the environment from before this fence, with the
    -- information of mutated buffers removed.
    , env'' <- env{ boundsGraph = boundsGraphClearNodes (boundsGraph env) $ accIdxSet modified }
    -> (IdxSet.empty, env'', bottomsGround zero $ groundsR acc, Fence set $ body')

  Atrace msg t -> (IdxSet.empty, env, TupRsingle $ bottom zero scalarTypeWord8, Atrace msg t)

  Aassert msg expr
    | (_, expr') <- boundsOptimizeExp env expr
    , expr'' <- simplifyExp expr'
    -> case expr'' of
      Const _ 1 -> (IdxSet.empty, env, TupRsingle $ bottom zero $ scalarTypeWord8, Compute $ Const scalarTypeWord8 1)
      _ | Just idx <- lookupAssertion bindings expr'' ->
        (IdxSet.empty, env, TupRsingle $ bottom zero $ scalarTypeWord8, Fence (IdxSet.singleton idx) $ Compute $ Const scalarTypeWord8 1)
      _ -> (IdxSet.empty, env, TupRsingle $ bottom zero $ scalarTypeWord8, Aassert msg expr')

  Aassume expr
    | (_, expr') <- boundsOptimizeExp env expr
    -> (IdxSet.empty, env, TupRsingle $ bottom zero $ scalarTypeWord8, Aassume expr')

  -- Default
  Alloc{} -> defaultBottom
  Use{} -> defaultBottom
  where
    -- Default, for expressions that don't mutate buffers,
    -- have no subexpressions and whose bound should be bottom.
    defaultBottom :: (IdxSet benv, BoundsEnv benv (), TermBounds (UniformEnv benv ()) t, OperationAcc op benv t)
    defaultBottom = (IdxSet.empty, env, bottomsGround zero $ groundsR acc, acc)

boundsOptimizeFun
  :: BoundsEnv benv env
  -> OpenFun env benv f
  -> OpenFun env benv f
boundsOptimizeFun env@(BoundsEnv _ _ zero _) = \case
  Lam lhs f
    | env' <- env `pushScalars` (lhs, bottoms zero $ lhsToTupR lhs) ->
      Lam lhs $ boundsOptimizeFun env' f
  Body expr -> Body $ snd $ boundsOptimizeExp env expr

boundsOptimizeFun1
  :: forall benv s t.
     BoundsEnv benv ()
  -> Arg benv (Fun' (s -> t))
  -> TermBounds (UniformEnv benv ()) s
  -> (TermBounds (UniformEnv benv ()) t, Arg benv (Fun' (s -> t)))
boundsOptimizeFun1 env (ArgFun (Lam lhs (Body expr))) argBounds
  | env' <- env `pushScalars` (lhs, argBounds)
  , (retBounds, expr') <- boundsOptimizeExp env' expr =
    ( snd $ strengthenBoundsWithScalarLHS @benv (boundsGraph env') lhs retBounds
    , ArgFun $ Lam lhs $ Body expr'
    )
boundsOptimizeFun1 _ _ _ = internalError "Expected unary function"

boundsOptimizeFun2
  :: forall benv r s t.
     BoundsEnv benv ()
  -> Arg benv (Fun' (r -> s -> t))
  -> TermBounds (UniformEnv benv ()) r
  -> TermBounds (UniformEnv benv ()) s
  -> (TermBounds (UniformEnv benv ()) t, Arg benv (Fun' (r -> s -> t)))
boundsOptimizeFun2 env (ArgFun (Lam lhs1 (Lam lhs2 (Body expr)))) argBounds1 argBounds2
  | lhs <- LeftHandSidePair lhs1 lhs2
  , env' <- env `pushScalars` (lhs, TupRpair argBounds1 argBounds2)
  , (retBounds, expr') <- boundsOptimizeExp env' expr =
    ( snd $ strengthenBoundsWithScalarLHS @benv (boundsGraph env') lhs retBounds
    , ArgFun $ Lam lhs1 $ Lam lhs2 $ Body expr'
    )
boundsOptimizeFun2 _ _ _ _ = internalError "Expected binary function"

boundsOptimizeExp
  :: forall benv env t.
     BoundsEnv benv env
  -> OpenExp env benv t
  -> (TermBounds (UniformEnv benv env) t, OpenExp env benv t)
boundsOptimizeExp env@(BoundsEnv _ _ zero _) expr = detectConst env $ case expr of
  Const (SingleScalarType (NumSingleType (IntegralNumType tp))) val
    | IntegralDict <- integralDict tp ->
      ( TupRsingle $ boundConst zero $ fromIntegral val
      , expr )
  
  Const tp _ ->
    ( TupRsingle $ bottom zero tp
    , expr )

  Undef tp ->
    ( TupRsingle $ undefBound zero tp
    , expr )

  Let lhs bnd body
    | (bndBounds, bnd') <- boundsOptimizeExp env bnd
    , env' <- env `pushScalars` (lhs, bndBounds)
    , (bodyBounds, body') <- boundsOptimizeExp env' body ->
      ( snd $ strengthenBoundsWithScalarLHS @benv (boundsGraph env') lhs bodyBounds
      , Let lhs bnd' body' )

  Evar (Var _ ix)
    | ix' <- expIdx env ix ->
      -- Mark this value as equal to the variable
      ( TupRsingle $ boundVar zero ix', expr )
  ArrayInstr arr arg -> case arr of
    Parameter (Var _ ix)
      | ix' <- accIdx env ix ->
        -- Mark this value as equal to the variable
        ( TupRsingle $ boundVar zero ix', expr )

    Index (Var (GroundRscalar tp) _) -> bufferImpossible tp
    Index v@(Var (GroundRbuffer _) ix)
      | _ix' <- accIdx env ix ->
        -- This value has the same bounds as the buffer.
        ( TupRsingle $ castTermBound $ boundOfAcc env ix
        , ArrayInstr (Index v) $ travE arg
        )

  Foreign tp asm f x -> (bottoms zero tp, Foreign tp asm f $ travE x) -- TODO: Optimize the fallback of Foreign
  Pair a b
    | (aBounds, a') <- boundsOptimizeExp env a
    , (bBounds, b') <- boundsOptimizeExp env b ->
      (TupRpair aBounds bBounds, Pair a' b')
  Nil -> (TupRunit, Nil)

  -- Analysis doesn't (yet) track SIMD vectors
  VecPack   vecR e -> bottomExpr $ VecPack   vecR $ travE e
  VecUnpack vecR e -> bottomExpr $ VecUnpack vecR $ travE e

  ToIndex shr sh ix -> bottomExpr $ ToIndex shr (travE sh) (travE ix)
  FromIndex shr sh ix
    | (shBounds, sh') <- boundsOptimizeExp env sh
    , (TupRsingle ixBound, ix') <- boundsOptimizeExp env ix ->
      (fromIndex zero shr shBounds ixBound, FromIndex shr sh' ix')
  
  ShapeSize shr sh -> bottomExpr $ ShapeSize shr (travE sh)

  Case _ [] (Just def) -> boundsOptimizeExp env def
  Case _ [] Nothing -> internalError "Illegal empty case"
  Case tag alts def
    | (bounds, alts', def') <- caseAlts alts def ->
      (bounds, Case (travE tag) alts' def')
  
  Cond c trueExp falseExp -> case travE c of
    -- Check if the condition is already known based on the bounds analysis
    Const _ 1 -> boundsOptimizeExp env trueExp
    Const _ 0 -> boundsOptimizeExp env falseExp

    c'
      | (trueBounds, true') <- boundsOptimizeExp (assumeTrue env c') trueExp
      , (falseBounds, false') <- boundsOptimizeExp (assumeFalse env c') falseExp ->
        ( unions (makeTransitives env trueBounds) (makeTransitives env falseBounds)
        , Cond c' true' false' )

  Select c t f -> case travE c of
    -- Check if the condition is already known based on the bounds analysis
    Const _ 1 -> boundsOptimizeExp env t
    Const _ 0 -> boundsOptimizeExp env f

    c' ->
      let (trueBounds, t') = boundsOptimizeExp env t
          (falseBounds, f') = boundsOptimizeExp env f
          bs = unions (makeTransitives env trueBounds)
                      (makeTransitives env falseBounds)

          isBoolBounds :: TermBounds (UniformEnv benv env) Word8 -> Bool
          isBoolBounds (TupRsingle bound) = boundIsBool (boundsZero env) $ makeTransitive env bound

          simplify
            | Just Refl <- matchTypeR (expType t') (TupRsingle scalarTypeWord8)
            , isBoolBounds trueBounds
            , isBoolBounds falseBounds
            = case (t', f') of
                (_        , Const _ 0)  -> (bs, PrimApp PrimLAnd (Pair c' t'))                    -- c ? t : 0 => c && t
                (Const _ 0, _        )  -> (bs, PrimApp PrimLAnd (Pair (PrimApp PrimLNot c') f')) -- c ? 0 : f => (not c) && f
                (Const _ 1, _        )  -> (bs, PrimApp PrimLOr  (Pair c' f'))                    -- c ? 1 : f => c || f
                (_        , Const _ 1)  -> (bs, PrimApp PrimLOr  (Pair (PrimApp PrimLNot c') t')) -- c ? t : 1 => (not c) || t
                _                       -> (bs, Select c' t' f')
            | otherwise                 =  (bs, Select c' t' f')
        in simplify

  Assert msg c body -> case travE c of
    Const _ 1 -> boundsOptimizeExp env body
    c'@(Const _ 0) -> Assert msg c' <$> boundsOptimizeExp env (undefs $ expType body)
    c'
      | (_, body') <- boundsOptimizeExp (assumeTrue env c') body ->
        -- Don't propagate the bounds of the body,
        -- as acting on them could cause this expression to not be used any more,
        -- and that could cause that the assertion is not ran at all.
        bottomExpr $ Assert msg c' body'

  Assume c body -> case travE c of
    Const _ 1 -> boundsOptimizeExp env body
    Const _ 0 -> boundsOptimizeExp env (undefs $ expType body)
    c'
      | (bodyBounds, body') <- boundsOptimizeExp (assumeTrue env c') body ->
        (bodyBounds, Assume c' body')

  While cond step initial
    | cond' <- travF cond
    , Lam lhsCond (Body bodyCond) <- cond'
    , Lam lhsStep (Body bodyStep) <- step
    , env' <- env `pushScalars` (lhsStep, bottoms zero $ lhsToTupR lhsStep)
    , env'' <- assumeTrue' (strengthenShrunkLHS lhsCond lhsStep Just) env' bodyCond
    , (stepBounds, bodyStep') <- boundsOptimizeExp env'' bodyStep
    , stepBounds' <- snd $ strengthenBoundsWithScalarLHS @benv (boundsGraph env'') lhsStep stepBounds
    , (initialBounds, initial') <- boundsOptimizeExp env initial ->
      ( unions (makeTransitives env initialBounds) (makeTransitives env stepBounds')
      , While cond' (Lam lhsStep $ Body bodyStep') initial' )
    | otherwise ->
      internalError "Expected unary functions"

  PrimApp f arg
    | (argBounds, arg') <- boundsOptimizeExp env arg ->
      app zero f arg' argBounds (makeTransitives env argBounds)

  Coerce t1 t2 a -> case boundsOptimizeExp env a of
    (TupRsingle bound, a') ->
      ( TupRsingle $ cast zero t1 t2 bound
      , Coerce t1 t2 a' )
    (TupRunit, _) -> unitImpossible t1
    (TupRpair _ _, _) -> pairImpossible t1

  where
    travE :: OpenExp env benv s -> OpenExp env benv s
    travE = snd . boundsOptimizeExp env

    travF :: OpenFun env benv f -> OpenFun env benv f
    travF = boundsOptimizeFun env

    bottomExpr :: OpenExp env benv t -> (TermBounds (UniformEnv benv env) t, OpenExp env benv t)
    bottomExpr e = (bottoms zero $ expType e, e)

    caseAlts :: [(TAG, OpenExp env benv b)] -> Maybe (OpenExp env benv b) -> (TermBounds (UniformEnv benv env) b, [(TAG, OpenExp env benv b)], Maybe (OpenExp env benv b))
    caseAlts alts (Just def)
      | (altsBounds, alts', _) <- caseAlts alts Nothing
      , (defBounds, def') <- boundsOptimizeExp env def
      = (unions altsBounds $ makeTransitives env defBounds, alts', Just def')
    caseAlts alts Nothing
      | (altsBoundss, alts') <- unzip $ map (\(t, e) -> let (b, e') = boundsOptimizeExp env e in (b, (t, e'))) alts
      = (foldl1 unions $ map (makeTransitives env) altsBoundss, alts', Nothing)

detectConst :: BoundsEnv benv env -> (TermBounds (UniformEnv benv env) t, OpenExp env benv t) -> (TermBounds (UniformEnv benv env) t, OpenExp env benv t)
detectConst env (bound, expr)
  | TupRsingle b <- bound
  , Just a <- upperConst env b
  , Just a == lowerConst env b
  , TupRsingle tp <- expType expr
  , SingleScalarType (NumSingleType (IntegralNumType t)) <- tp
  , IntegralDict <- integralDict t
  = (bound, Const tp $ fromIntegral a)
  | otherwise
  = (bound, expr)

boundsOptimizeArg :: BoundsEnv benv () -> Arg benv t -> Arg benv t
boundsOptimizeArg env = \case
  ArgFun fun -> ArgFun $ boundsOptimizeFun env fun
  ArgExp expr -> ArgExp $ snd $ boundsOptimizeExp env expr
  arg -> arg -- ArgVar or ArgArray

data InputBounds benv s where
  InputIn
    :: TermBounds (UniformEnv benv ()) sh
    -> TermBounds (UniformEnv benv ()) t
    -> InputBounds benv (In sh t)

  InputMut
    :: TermBounds (UniformEnv benv ()) sh
    -> TermBounds (UniformEnv benv ()) t
    -> InputBounds benv (Mut sh t)

  InputOut
    :: TermBounds (UniformEnv benv ()) sh
    -> InputBounds benv (Out sh t)

  InputVar
    :: TermBounds (UniformEnv benv ()) t
    -> InputBounds benv (Var' t)

  InputExp
    :: InputBounds benv (Exp' t)

  InputFun
    :: InputBounds benv (Fun' f)

data OutputBounds benv s where
  OutputOut
    :: TermBounds (UniformEnv benv ()) t
    -> OutputBounds benv (Out sh t)

  OutputMut
    :: TermBounds (UniformEnv benv ()) t
    -> OutputBounds benv (Out sh t)
  
  OutputNone
    :: OutputBounds benv s

envWriteArgs :: forall benv args. Args benv args -> OutputBoundArgs benv args -> BoundsEnv benv () -> BoundsEnv benv ()
envWriteArgs ArgsNil _ env = env
envWriteArgs (arg :>: args) (output :>: outputs) env
  | ArgArray _ (ArrayR _ tp) _ buffers <- arg
  , Just bounds <- case output of
    OutputOut b -> Just b
    OutputMut b -> Just b
    OutputNone -> Nothing
  = envWriteArgs args outputs $ go tp buffers bounds env
  | otherwise = envWriteArgs args outputs env
  where
    go :: forall t. TypeR t -> GroundVars benv (Buffers t) -> TermBounds (UniformEnv benv ()) t -> BoundsEnv benv () -> BoundsEnv benv ()
    go (TupRsingle tp) (TupRsingle var) (TupRsingle bound) env1
      | Refl <- reprIsSingle @ScalarType @t @Buffer tp
      , idx <- accIdx env $ varIdx var
      , bound' <- castTermBound bound
      = env1{ boundsGraph =
          Graph.insertEdgesFromWith min idx (upper bound')
            $ Graph.insertEdgesToWith min (lower bound') idx
            $ boundsGraph env1      
        }
    go (TupRpair t1 t2) (TupRpair v1 v2) (TupRpair b1 b2) env1
      = go t1 v1 b1 $ go t2 v2 b2 env1
    go TupRunit TupRunit TupRunit env1 = env1
    go _ _ _ _ = internalError "Tuple mismatch"

type InputBoundArgs benv args = PreArgs (InputBounds benv) args
type OutputBoundArgs benv args = PreArgs (OutputBounds benv) args

boundsInputs :: BoundsEnv benv () -> Args benv args -> InputBoundArgs benv args
boundsInputs env = mapArgs (boundsInput env)

boundsInput :: BoundsEnv benv () -> Arg benv arg -> InputBounds benv arg
boundsInput env = \case
  ArgArray In (ArrayR _ tp) sh buffers -> InputIn
    (mapTupR (\sz -> boundVar (boundsZero env) $ accIdx env $ varIdx sz) sh)
    (unBufferTermBounds tp $ mapTupR (\buffer -> boundOfAcc env $ varIdx buffer) buffers)
  ArgArray Mut (ArrayR _ tp) sh buffers -> InputMut
    (mapTupR (\sz -> boundVar (boundsZero env) $ accIdx env $ varIdx sz) sh)
    (unBufferTermBounds tp $ mapTupR (\buffer -> boundOfAcc env $ varIdx buffer) buffers)
  ArgArray Out _ sh _ -> InputOut
    (mapTupR (\sz -> boundVar (boundsZero env) $ accIdx env $ varIdx sz) sh)
  ArgVar vars -> InputVar
    (mapTupR (\var -> boundVar (boundsZero env) $ accIdx env $ varIdx var) vars)
  ArgExp _ -> InputExp
  ArgFun _ -> InputFun

-- Variant of 'boundsGraphClearNode' that works on a graph *and Args*.
-- Assumes that the Idx refers to a Buffer.
boundsGraphWithArgsClearNode
  :: forall benv args t.
     (BoundsGraph (UniformEnv benv ()), InputBoundArgs benv args)
  -> Idx (UniformEnv benv ()) t
  -> (BoundsGraph (UniformEnv benv ()), InputBoundArgs benv args)
boundsGraphWithArgsClearNode (graph, args) idx = (boundsGraphClearNode graph idx, mapArgs f args)
  where
    idxLower = Graph.inn graph idx
    idxUpper = Graph.out graph idx

    f :: InputBounds benv s -> InputBounds benv s
    f (InputIn sh buffers) = InputIn sh $ mapTupR g buffers
    f (InputMut sh buffers) = InputMut sh $ mapTupR g buffers
    f bounds = bounds -- Does not contain buffers

    g :: TermBound (UniformEnv benv ()) s -> TermBound (UniformEnv benv ()) s
    g bound = TermBound lower' upper'
      where
        lower'
          | Just (Graph.InEdge (Edge d)) <- prjPartial idx $ lower bound =
            partialRemove idx
              $ unionPartialEnv
                (\(Graph.InEdge x) (Graph.InEdge y) -> Graph.InEdge $ min x y)
                (lower bound)
              $ mapPartialEnv
                (\(Graph.InEdge (Edge d')) -> Graph.InEdge $ Edge $ d + d')
                idxLower
          | otherwise = lower bound
        upper'
          | Just (Edge d) <- prjPartial idx $ upper bound =
            partialRemove idx
              $ unionPartialEnv min (upper bound)
              $ mapPartialEnv (\(Edge d') -> Edge $ d + d') idxUpper
          | otherwise = upper bound

-- Variant of 'boundsGraphClearNodes' that works on a graph *and Args*.
-- Assumes that the Idx refers to a Buffer.
boundsGraphWithArgsClearNodes
  :: (BoundsGraph (UniformEnv benv ()), InputBoundArgs benv args)
  -> IdxSet (UniformEnv benv ())
  -> (BoundsGraph (UniformEnv benv ()), InputBoundArgs benv args)
boundsGraphWithArgsClearNodes graphArgs set =
  foldl' (\ga (Exists idx) -> boundsGraphWithArgsClearNode ga idx) graphArgs
    $ IdxSet.toList set

class OperationBounds op where
  boundsOptimizeOp
    :: op args
    -> BoundsEnv benv ()
    -> InputBoundArgs benv args
    -> Args benv args
    -> (OutputBoundArgs benv args, Args benv args)

boundsOptimizeOpDefault
  :: BoundsEnv benv ()
  -> InputBoundArgs benv args
  -> Args benv args
  -> (OutputBoundArgs benv args, Args benv args)
boundsOptimizeOpDefault env _ args =
    ( mapArgs (\_ -> OutputNone) args
    , mapArgs (boundsOptimizeArg env) args )

boundsOptimizeMap
  :: args ~ (Fun' (s -> t) -> In sh s -> Out sh t -> ())
  => BoundsEnv benv ()
  -> InputBoundArgs benv args
  -> Args benv args
  -> (OutputBoundArgs benv args, Args benv args)
boundsOptimizeMap env (_ :>: InputIn _ inBounds :>: _) (f :>: input :>: output :>: _)
  | (outBounds, f') <- boundsOptimizeFun1 env f inBounds =
    ( OutputNone :>: OutputNone :>: OutputOut outBounds :>: ArgsNil
    , f' :>: input :>: output :>: ArgsNil )

boundsOptimizeGenerate
  :: args ~ (Fun' (sh -> t) -> Out sh t -> ())
  => BoundsEnv benv ()
  -> InputBoundArgs benv args
  -> Args benv args
  -> (OutputBoundArgs benv args, Args benv args)
boundsOptimizeGenerate env (_ :>: InputOut shBounds :>: _) (f :>: output :>: _)
  | (outBounds, f') <- boundsOptimizeFun1 env f (indexBounds (boundsZero env) shBounds) =
    ( OutputNone :>: OutputOut outBounds :>: ArgsNil
    , f' :>: output :>: ArgsNil )

boundsOptimizeBackpermute
  :: args ~ (Fun' (sh' -> sh) -> In sh t -> Out sh' t -> ())
  => BoundsEnv benv ()
  -> InputBoundArgs benv args
  -> Args benv args
  -> (OutputBoundArgs benv args, Args benv args)
boundsOptimizeBackpermute env (_ :>: InputIn _ inBounds :>: InputOut shBounds :>: _) (f :>: input :>: output :>: _)
  | (_, f') <- boundsOptimizeFun1 env f (indexBounds (boundsZero env) shBounds) =
    ( OutputNone :>: OutputNone :>: OutputOut inBounds :>: ArgsNil
    , f' :>: input :>: output :>: ArgsNil )

-- TODO: Add default implementations for permute and permuteUnique

boundsOptimizeFold
  :: args ~ (Fun' (e -> e -> e) -> Exp' e -> In (sh, Int) e -> Out sh e -> ())
  => BoundsEnv benv ()
  -> InputBoundArgs benv args
  -> Args benv args
  -> (OutputBoundArgs benv args, Args benv args)
boundsOptimizeFold env (_ :>: _ :>: inBounds :>: _) (f :>: ArgExp seed :>: input :>: output :>: _)
  | (seedBounds, seed') <- boundsOptimizeExp env seed
  , f' <- boundsOptimizeArg env f
  , (_, foldBounds) <-
    boundsOptimizeScanlike env
      (InputFun :>: inBounds :>: ArgsNil)
      (f' :>: input :>: ArgsNil)
      (Just (seedBounds, ArgExp seed'))
  =
    ( OutputNone :>: OutputNone :>: OutputNone :>: OutputOut foldBounds :>: ArgsNil
    , f' :>: ArgExp seed' :>: input :>: output :>: ArgsNil
    )

boundsOptimizeFold1
  :: args ~ (Fun' (e -> e -> e) -> In (sh, Int) e -> Out sh e -> ())
  => BoundsEnv benv ()
  -> InputBoundArgs benv args
  -> Args benv args
  -> (OutputBoundArgs benv args, Args benv args)
boundsOptimizeFold1 env (_ :>: inBounds :>: _) (f :>: input :>: output :>: _)
  | f' <- boundsOptimizeArg env f
  , (_, foldBounds) <-
    boundsOptimizeScanlike env
      (InputFun :>: inBounds :>: ArgsNil)
      (f' :>: input :>: ArgsNil)
      Nothing
  =
    ( OutputNone :>: OutputNone :>: OutputOut foldBounds :>: ArgsNil
    , f' :>: input :>: output :>: ArgsNil
    )

boundsOptimizeScan
  :: args ~ (Fun' (e -> e -> e) -> Exp' e -> In (sh, Int) e -> Out (sh, Int) e -> ())
  => BoundsEnv benv ()
  -> InputBoundArgs benv args
  -> Args benv args
  -> (OutputBoundArgs benv args, Args benv args)
boundsOptimizeScan env (_ :>: _ :>: inBounds :>: _) (f :>: ArgExp seed :>: input :>: output :>: _)
  | (seedBounds, seed') <- boundsOptimizeExp env seed
  , f' <- boundsOptimizeArg env f
  , (scanBounds, foldBounds) <-
    boundsOptimizeScanlike env
      (InputFun :>: inBounds :>: ArgsNil)
      (f' :>: input :>: ArgsNil)
      (Just (seedBounds, ArgExp seed'))
  =
    ( OutputNone :>: OutputNone :>: OutputNone :>: OutputOut (unions scanBounds foldBounds) :>: ArgsNil
    , f' :>: ArgExp seed' :>: input :>: output :>: ArgsNil
    )

boundsOptimizeScan'
  :: args ~ (Fun' (e -> e -> e) -> Exp' e -> In (sh, Int) e -> Out (sh, Int) e -> Out sh e -> ())
  => BoundsEnv benv ()
  -> InputBoundArgs benv args
  -> Args benv args
  -> (OutputBoundArgs benv args, Args benv args)
boundsOptimizeScan' env (_ :>: _ :>: inBounds :>: _) (f :>: ArgExp seed :>: input :>: outputScan :>: outputFold :>: _)
  | (seedBounds, seed') <- boundsOptimizeExp env seed
  , f' <- boundsOptimizeArg env f
  , (scanBounds, foldBounds) <-
    boundsOptimizeScanlike env
      (InputFun :>: inBounds :>: ArgsNil)
      (f' :>: input :>: ArgsNil)
      (Just (seedBounds, ArgExp seed'))
  =
    ( OutputNone :>: OutputNone :>: OutputNone :>: OutputOut scanBounds :>: OutputOut foldBounds :>: ArgsNil
    , f' :>: ArgExp seed' :>: input :>: outputScan :>: outputFold :>: ArgsNil
    )

boundsOptimizeScan1
  :: args ~ (Fun' (e -> e -> e) -> In (sh, Int) e -> Out (sh, Int) e -> ())
  => BoundsEnv benv ()
  -> InputBoundArgs benv args
  -> Args benv args
  -> (OutputBoundArgs benv args, Args benv args)
boundsOptimizeScan1 env (_ :>: inBounds :>: _) (f :>: input :>: output :>: _)
  | f' <- boundsOptimizeArg env f
  , (scanBounds, foldBounds) <-
    boundsOptimizeScanlike env
      (InputFun :>: inBounds :>: ArgsNil)
      (f' :>: input :>: ArgsNil)
      Nothing
  =
    ( OutputNone :>: OutputNone :>: OutputOut (unions scanBounds foldBounds) :>: ArgsNil
    , f' :>: input :>: output :>: ArgsNil
    )

boundsOptimizeScanlike
  :: args ~ (Fun' (e -> e -> e) -> In (sh, Int) e -> ())
  => BoundsEnv benv ()
  -> InputBoundArgs benv args
  -> Args benv args
  -> Maybe (TermBounds (UniformEnv benv ()) e, Arg benv (Exp' e))
  -> (TermBounds (UniformEnv benv ()) e, TermBounds (UniformEnv benv ()) e)
boundsOptimizeScanlike env (_ :>: InputIn inShape inBounds :>: _) (f :>: input :>: _) seed
  -- Detect a scan (+) over an array of zeros and ones.
  | ArgArray _ (ArrayR _ (TupRsingle tp)) _ _ <- input
  , SingleScalarType (NumSingleType (IntegralNumType TypeInt)) <- tp
  , ArgFun (Lam LeftHandSideSingle{} (Lam LeftHandSideSingle{} (Body expr))) <- f
  , PrimApp PrimAdd{} (Pair (Evar (Var _ (SuccIdx ZeroIdx))) (Evar (Var _ ZeroIdx))) <- expr
  , TupRsingle inBound <- inBounds
  , (l, u) <- getBoundRange (boundsZero env) TypeInt $ makeTransitive env inBound
  , 0 <= l && u <= 1
  , case seed of
      Nothing -> True
      Just (_, ArgExp (Const _ 0)) -> True
      _ -> False
  , TupRpair _ (TupRsingle inSize) <- inShape
  -- Yes, this is a scan with addition, whose input consists of zeros and ones.
  -- Elements in the output are bounded by the input size
  , scanBound <- TermBound
    (lower $ boundConst (boundsZero env) 0)
    (mapPartialEnv (\(Edge d) -> Edge (d - 1)) $ upper inSize)
  , foldBound <- TermBound
    (lower $ boundConst (boundsZero env) 0)
    (upper inSize)
  =
    ( TupRsingle scanBound
    , TupRsingle foldBound
    )
-- TODO: Detect operators that only return values from the left or right argument,
-- like min and max
boundsOptimizeScanlike env _ (_ :>: ArgArray _ (ArrayR _ tp) _ _ :>: _) _ =
  ( bottoms (boundsZero env) tp
  , bottoms (boundsZero env) tp
  )
