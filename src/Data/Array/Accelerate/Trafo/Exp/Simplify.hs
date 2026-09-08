{-# LANGUAGE CPP                  #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE PatternGuards        #-}
{-# LANGUAGE RankNTypes           #-}
{-# LANGUAGE RecordWildCards      #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TupleSections        #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE ViewPatterns         #-}
{-# OPTIONS_HADDOCK hide #-}
-- |
-- Module      : Data.Array.Accelerate.Trafo.Exp.Simplify
-- Copyright   : [2012..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.Trafo.Exp.Simplify (

  simplifyFun,
  simplifyExp

) where

import Data.Array.Accelerate.AST.Exp
import Data.Array.Accelerate.AST.Environment
import Data.Array.Accelerate.AST.Idx
import Data.Array.Accelerate.AST.LeftHandSide
import Data.Array.Accelerate.AST.Var
import Data.Array.Accelerate.Analysis.Hash
import Data.Array.Accelerate.Analysis.Match
import Data.Array.Accelerate.Error
import Data.Array.Accelerate.Representation.Shape                   ( ShapeR(..), shapeToList, rank )
import Data.Array.Accelerate.Representation.Type
import Data.Array.Accelerate.Representation.Vec
import Data.Array.Accelerate.Trafo.Exp.Algebra
import Data.Array.Accelerate.Trafo.Environment
import Data.Array.Accelerate.Trafo.Shrink
import Data.Array.Accelerate.Trafo.Substitution
import Data.Array.Accelerate.Type

import qualified Data.Array.Accelerate.Debug.Internal.Stats         as Stats
import qualified Data.Array.Accelerate.Debug.Internal.Flags         as Debug
import qualified Data.Array.Accelerate.Debug.Internal.Trace         as Debug

import Control.Applicative                                          hiding ( Const )
import Control.Monad
import Data.List                                                    ( partition )
import Data.Maybe
import Data.Text                                                    ( Text )
import Data.Monoid
import Data.Text.Lazy.Builder
import Data.Primitive.Vec
import GHC.TypeNats
import Formatting
import Lens.Micro                                                   hiding ( ix )
import Prelude                                                      hiding ( exp, iterate )
import qualified Data.Map.Strict                                    as Map


-- Scalar optimisations
-- ====================

{--
-- Common subexpression elimination finds computations that are performed at
-- least twice on a given execution path and eliminates the second and later
-- occurrences, replacing them with uses of saved values. This implements a
-- simplified version of that idea, where we look for the expressions of the
-- form:
--
--   let x = e1 in e2
--
-- and replace all occurrences of e1 in e2 with x. This is not full redundancy
-- elimination, but good enough to catch some cases, and in particular those
-- likely to be introduced by scalar composition of terms in the fusion process.
--
-- While it may seem that common subexpression elimination is always worthwhile,
-- as it reduces the number of arithmetic operations performed, this is not
-- necessarily advantageous. The simplest case in which it may not be desirable
-- is if it causes a register to be occupied for a long time in order to hold
-- the shared expression's value, which hence reduces the number of registers
-- available for other uses. Even worse is if the value has to be spilled to
-- memory because there are insufficient registers available. We sidestep this
-- tricky and target-dependent issue by, for now, simply ignoring it.
--
localCSE :: (Elt a)
         => Gamma arr env env
         -> PreOpenExp arr env a
         -> PreOpenExp arr (env,a) b
         -> Maybe (PreOpenExp arr env b)
localCSE env bnd body
  | Just ix <- lookupExp env bnd = Stats.ruleFired "CSE" . Just $ inline body (Var ix)
  | otherwise                    = Nothing
--}
{--
-- Common subexpression elimination, which attempts to match the given
-- expression against something already bound in the environment. This can occur
-- due to simplification, in which case we replace the entire subterm with x.
--
-- > let x = e in .. e ..
--
globalCSE :: (Elt t)
          => Gamma arr env env
          -> PreOpenExp arr env t
          -> Maybe (PreOpenExp arr env t)
globalCSE env exp
  | Just ix <- lookupExp env exp = Stats.ruleFired "CSE" . Just $ Var ix
  | otherwise                    = Nothing
--}

{--
-- Compared to regular Haskell, the scalar expression language of Accelerate is
-- rather limited in order to meet the restrictions of what can be efficiently
-- implemented on specialised hardware, such as GPUs. For example, to avoid
-- excessive SIMD divergence, we do not support any form of recursion or
-- iteration in scalar expressions. This harmonises well with the stratified
-- design of the Accelerate language: collective array operations comprise many
-- scalar computations that are executed in parallel, so for simplicity of
-- scheduling these operations we would like some assurance that each scalar
-- computation takes approximately the same time to execute as all others.
--
-- However, some computations are naturally expressed in terms of iteration. For
-- some problems, we can instead use generative techniques to implement the
-- program by defining a single step of a recurrence relation as an Accelerate
-- collective operation and using standard Haskell to unroll the loop a _fixed_
-- number of times.
--
-- However, this is outrageously slow because the intermediate values are
-- written to memory at the end of every iteration. Luckily the fusion process
-- will eliminate this intermediate memory traffic by combining the 'n'
-- collective operations into a single operation with 'n' instances of the loop
-- body. However, doing this we uncover an embarrassing secret: C compilers do
-- not compile C code, they compile _idiomatic_ C code.
--
-- This process recovers the iteration structure that was lost in the process of
-- fusing the collective operations. This allows a backend to generate explicit
-- loops in its target language.
--
recoverLoops
    :: (Elt b)
    => Gamma arr env env
    -> PreOpenExp arr env a
    -> PreOpenExp arr (env,a) b
    -> Maybe (PreOpenExp arr env b)
recoverLoops _ bnd e3
  -- To introduce scaler loops, we look for expressions of the form:
  --
  --   let x =
  --     let y = e1 in e2
  --   in e3
  --
  -- and if e2 and e3 are congruent, replace with:
  --
  --   iterate[2] (\y -> e2) e1
  --
  | Let e1 e2           <- bnd
  , Just Refl           <- matchEnvTop e2 e3
  , Just Refl           <- match e2 e3
  = Stats.ruleFired "loop recovery/intro" . Just
  $ Iterate (constant 2) e2 e1

  -- To merge expressions into a loop body, look for the pattern:
  --
  --   let x = iterate[n] f e1
  --   in e3
  --
  -- and if e3 matches the loop body, replace the let binding with the bare
  -- iteration with the trip count increased by one.
  --
  | Iterate n f e1      <- bnd
  , Just Refl           <- match f e3
  = Stats.ruleFired "loop recovery/merge" . Just
  $ Iterate (constant 1 `plus` n) f e1

  | otherwise
  = Nothing

  where
    plus :: PreOpenExp arr env Int -> PreOpenExp arr env Int -> PreOpenExp arr env Int
    plus x y = PrimApp (PrimAdd numType) $ Tuple $ NilTup `SnocTup` x `SnocTup` y

    constant :: Int -> PreOpenExp arr env Int
    constant i = Const ((),i)

    matchEnvTop :: (Elt s, Elt t)
                => PreOpenExp arr (env,s) f
                -> PreOpenExp arr (env,t) g
                -> Maybe (s :=: t)
    matchEnvTop _ _ = gcast Refl
--}


-- Walk a scalar expression applying simplifications to terms bottom-up.
--
-- TODO: Look for particular patterns of expressions that can be replaced by
--       something equivalent and simpler. In particular, indexing operations
--       introduced by the fusion transformation. This would benefit from a
--       rewrite rule schema.
--
-- TODO: We currently pass around an environment Gamma, but we do not use it.
--       It might be helpful to do some inlining if this enables other optimizations.
--       Eg, for `let x = -y in -x`, the inlining would allow us to shorten it to `y`.
--       If we do not want to do inlining, we should remove the environment here.
--
simplifyOpenExp
    :: forall arr env e.
       IsArrayInstr arr
    => Gamma arr env env
    -> PreOpenExp arr env e
    -> (Bool, PreOpenExp arr env e)
simplifyOpenExp env = first getAny . cvtE
  where
    cvtE :: PreOpenExp arr env t -> (Any, PreOpenExp arr env t)
    cvtE exp = case exp of
      Let lhs bnd body -> (u <> v, exp')
        where
          (u, bnd') = cvtE bnd
          (v, exp') = cvtLet env lhs bnd' $ Subst weakenId body body
      Evar var                  -> cvtVar var
      Const tp c                -> pure $ Const tp c
      Undef tp                  -> pure $ Undef tp
      Nil                       -> pure Nil
      Pair e1 e2                -> hoist2 (\a b -> pure $ Pair a b) (cvtE e1) (cvtE e2)
      VecPack   vec e           -> hoist (vecPack   vec) (cvtE e)
      VecUnpack vec e           -> hoist (vecUnpack vec) (cvtE e)
      ToIndex shr sh ix         -> hoist2 (toIndex shr) (cvtE sh) (cvtE ix)
      FromIndex shr sh ix       -> hoist2 (fromIndex shr) (cvtE sh) (cvtE ix)
      Case e rhs def            -> hoist (\e' -> caseof e' (sequenceA [ (t,) <$> cvtE c | (t,c) <- rhs ]) (cvtMaybeE def)) (cvtE e)
      Cond p t e                -> hoist (\p' -> cond p' (cvtE t) (cvtE e)) (cvtE p)
      Select p t e              -> hoist (\p' -> select p' (cvtE t) (cvtE e)) (cvtE p)
      PrimApp f x               -> hoist (evalPrimApp env f) (cvtE x)
      ArrayInstr arr e          -> hoist (arrayInstr arr) (cvtE e)
      ShapeSize shr sh          -> hoist (shapeSize shr) (cvtE sh)
      Foreign tp ff f e         -> hoist (\e' -> Foreign tp ff <$> first Any (simplifyOpenFun EmptyExp f) <*> pure e') (cvtE e)
      While p f x               -> While <$> cvtF env p <*> cvtF env f <*> cvtE x
      Coerce t1 t2 e            -> hoist (pure . Coerce t1 t2) (cvtE e)
      Assert msg e1 e2          -> join (assert msg <$> cvtE e1 <*> cvtE e2)
      Assume e1 e2              -> join (assume <$> cvtE e1 <*> cvtE e2)

    cvtE' :: Gamma arr env' env' -> PreOpenExp arr env' e' -> (Any, PreOpenExp arr env' e')
    cvtE' env' = first Any . simplifyOpenExp env'

    cvtF :: Gamma arr env' env' -> PreOpenFun arr env' f -> (Any, PreOpenFun arr env' f)
    cvtF env' = first Any . simplifyOpenFun env'

    cvtMaybeE :: Maybe (PreOpenExp arr env e') -> (Any, Maybe (PreOpenExp arr env e'))
    cvtMaybeE Nothing  = pure Nothing
    cvtMaybeE (Just e) = Just <$> cvtE e

    cvtLet :: Gamma arr env' env'
           -> ELeftHandSide bnd env' env''
           -> PreOpenExp arr env' bnd -- Optimized
           -> WeakOpenExp arr env'' t -- Not optimized
           -> (Any, PreOpenExp arr env' t)
    cvtLet env' lhs (Assert msg c bnd) body = yes $ Assert msg c $ snd $ cvtLet env' lhs bnd body
    cvtLet env' lhs (Assume c bnd) body = yes $ Assume c $ snd $ cvtLet env' lhs bnd body
    -- Let rotation
    cvtLet env' lhs1 (Let lhs2 bnd expr) body
      | Exists lhs1' <- rebuildLHS lhs1 =
        yes $ snd $ cvtLet' env' lhs2 bnd $ \env'' ->
          cvtLet env'' lhs1' expr $ weakenE (sinkWithLHS lhs1 lhs1' $ weakenWithLHS lhs2) body
    cvtLet env' lhs bnd (Subst _ _ body) = cvtLet' env' lhs bnd $ \env'' -> cvtE' env'' body

    cvtLet' :: Gamma arr env' env'
            -> ELeftHandSide bnd env' env''
            -> PreOpenExp arr env' bnd
            -> (Gamma arr env'' env'' -> (Any, PreOpenExp arr env'' t))
            -> (Any, PreOpenExp arr env' t)
    -- Let rotation and hoisting of assertions are already handled in cvtLet
    cvtLet' env' lhs@(LeftHandSideSingle _) bnd          body = Let lhs bnd <$> body (incExp $ env' `pushExp` bnd) -- Single variable on the LHS, add binding to the environment
    cvtLet' env' (LeftHandSideWildcard _)   _            body = body env'                                 -- Binding not used, remove let binding
    cvtLet' env' (LeftHandSidePair l1 l2)   (Pair e1 e2) body                                             -- Split binding to multiple bindings
      = first (const $ Any True)
      $ cvtLet' env' l1 e1
      $ \env'' -> cvtLet' env'' l2 (weakenE (weakenWithLHS l1) e2) body
    cvtLet' env' lhs                        bnd          body = Let lhs bnd <$> body (lhsExpr lhs env')   -- Cannot split this binding.

    cvtVar :: ExpVar env t -> (Any, PreOpenExp arr env t)
    cvtVar var
      | shouldInline bnd
      , Nothing <- matchOpenExp bnd (Evar var)
        = yes bnd
      | otherwise
        = pure $ Evar var
      where
        bnd = prjExp (varIdx var) env

    -- Note: we also do inlining in Shrink.hs, but we can easily do it here as
    -- well since we already have an environment.
    -- TODO: We may want to consider to remove the environment (Gamma) from
    -- this function and let Shrink do the inlining. The environment was
    -- annoying for let rotation for instance.
    shouldInline :: PreOpenExp arr env t -> Bool
    shouldInline Evar{} = True
    shouldInline (ArrayInstr arr Nil) = inlineArrayInstr arr
    shouldInline Const{} = True
    shouldInline _ = False

    select :: PreOpenExp arr env PrimBool
           -> (Any, PreOpenExp arr env t)
           -> (Any, PreOpenExp arr env t)
           -> (Any, PreOpenExp arr env t)
    select p t@(_,t') e@(_,e')
      | Const _ 1 <- p                  = Stats.knownBranch "True"      (yes t')
      | Const _ 0 <- p                  = Stats.knownBranch "False"     (yes e')
      | Undef _ <- e'                   = yes t'
      | Undef _ <- t'                   = yes e'
      -- Convert select over pairs to pair of selects. This may enable further
      -- optimizations, and if we don't do this here we'll do it during code
      -- generation anyway.
      | Pair t1 t2 <- t'
      , Pair e1 e2 <- e'
      = if shouldInline p then
        -- If the condition is simple, can directly perform this transformation
          yes $ Pair (Select p t1 e1) (Select p t2 e2)
        else
          -- Otherwise we bind the condition to a variable
          yes $ Let (LeftHandSideSingle scalarTypeWord8) p
            $ Pair
              (Select (Evar (Var scalarTypeWord8 ZeroIdx)) (weakenE (weakenSucc weakenId) t1) (weakenE (weakenSucc weakenId) e1))
              (Select (Evar (Var scalarTypeWord8 ZeroIdx)) (weakenE (weakenSucc weakenId) t2) (weakenE (weakenSucc weakenId) e2))
      | Just Refl <- matchOpenExp t' e' = Stats.knownBranch "redundant" (yes e')
      | PrimApp PrimLNot c <- p         = yes $ Select c e' t'
      | otherwise                       = Select p <$> t <*> e

    -- Simplify conditional expressions, in particular by eliminating branches
    -- when the predicate is a known constant.
    --
    cond :: PreOpenExp arr env PrimBool
         -> (Any, PreOpenExp arr env t)
         -> (Any, PreOpenExp arr env t)
         -> (Any, PreOpenExp arr env t)
    cond p t@(_,t') e@(_,e')
      | Const _ 1 <- p                  = Stats.knownBranch "True"      (yes t')
      | Const _ 0 <- p                  = Stats.knownBranch "False"     (yes e')
      | Just Refl <- matchOpenExp t' e' = Stats.knownBranch "redundant" (yes e')
      | isCheap t' && isCheap e'        = yes $ snd $ select p t e
      | PrimApp PrimLNot c <- p         = yes $ Cond c e' t'
      | otherwise                       = Cond p <$> t <*> e

    -- Checks whether an expression is cheap, and may be evaluated eagerly
    -- (i.e. lifted from within a conditional, to always be evaluated)
    --
    -- If the expression performs many computations, or if the expression
    -- may diverge, this function will return false.
    --
    isCheap :: PreOpenExp arr env t -> Bool
    isCheap = maybe False (<= maxCost) . expCost
      where
        maxCost = 10

        expCost :: PreOpenExp arr env' t -> Maybe Int
        expCost = \case
          ArrayInstr a arg -> if inlineArrayInstr a
                               then Just 0 .+. expCost arg
                               else Nothing
          Evar{}           -> Just 0
          Nil              -> Just 0
          Const{}          -> Just 0
          Undef{}          -> Just 0
          PrimApp f e      -> primCost f .+. expCost e
          Let _ bnd body   -> expCost bnd .+. expCost body
          Pair e1 e2       -> expCost e1 .+. expCost e2
          VecPack _ e      -> Just 1 .+. expCost e
          VecUnpack _ e    -> Just 1 .+. expCost e
          Coerce _ _ e     -> expCost e
          Select c t f     -> Just 1 .+. expCost c .+. expCost t .+. expCost f
          ToIndex shr sh ix -> shapeCost shr .+. expCost sh .+. expCost ix
          FromIndex shr sh ix -> shapeCost shr .+. expCost sh .+. expCost ix
          ShapeSize shr sh -> shapeCost shr .+. expCost sh
          Foreign{}        -> Nothing
          Case{}           -> Nothing
          Cond{}           -> Nothing
          While{}          -> Nothing
          Assert{}         -> Nothing
          -- If we treat Assume as cheap, then it might be strictly evaluated.
          -- That may imply that the assumption gets a larger scope, and we may
          -- incorrectly act on the information of that assumption.
          -- Example: if foo then assume foo x else y
          -- If we treat Assume as cheap, this may be converted to:
          -- select foo (assume foo x) y
          -- The assumption will be lifted:
          -- assume foo (select foo x y)
          -- Bounds analysis may optimize this to:
          -- assume foo x
          -- Which is cleary not sound.
          Assume{}         -> Nothing

        shapeCost :: ShapeR sh -> Maybe Int
        shapeCost = \case
          ShapeRz -> Just 0
          ShapeRsnoc shr -> Just $ rank shr

        primCost :: PrimFun f -> Maybe Int
        primCost = \case
          PrimAdd _        -> Just 1
          PrimSub _        -> Just 1
          PrimMul _        -> Just 1
          PrimNeg _        -> Just 1
          PrimAbs _        -> Just 1
          PrimSig _        -> Just 1
          PrimBAnd _       -> Just 1
          PrimBOr _        -> Just 1
          PrimBXor _       -> Just 1
          PrimBNot _       -> Just 1
          PrimBShiftL _    -> Just 1
          PrimBShiftR _    -> Just 1
          PrimBRotateL _   -> Just 1
          PrimBRotateR _   -> Just 1
          PrimPopCount _   -> Just 1
          PrimCountLeadingZeros _ -> Just 1
          PrimCountTrailingZeros _ -> Just 1
          PrimCmp _ _      -> Just 1
          PrimMax _        -> Just 1
          PrimMin _        -> Just 1
          PrimLAnd         -> Just 1
          PrimLOr          -> Just 1
          PrimLNot         -> Just 1
          _                -> Nothing

        (.+.) :: Maybe Int -> Maybe Int -> Maybe Int
        a .+. b = (+) <$> a <*> b

    caseof :: PreOpenExp arr env TAG
           -> (Any, [(TAG, PreOpenExp arr env b)])
           -> (Any, Maybe (PreOpenExp arr env b))
           -> (Any, PreOpenExp arr env b)
    caseof tag xs@(_,xs') md@(_,md')
      | Const _ t   <- tag
      = Stats.caseElim "known" $ yes $ fromMaybe
        -- If the tag matches no alternative, then return the default (if present)
        -- or undef.
        (fromMaybe (undefs tp) md')
        $ lookup t xs'
      | Just d      <- md'
      , []          <- xs'
      = Stats.caseElim "redundant" (yes d)
      | Just d      <- md'
      , [(_,(_,u))] <- us
      , Just Refl   <- matchOpenExp d u
      = Stats.caseDefault "merge" $ yes $ Case tag (map snd vs) (Just u)
      | Nothing     <- md'
      , []          <- vs
      , [(_,(_,u))] <- us
      = Stats.caseElim "overlap" $ yes u
      | Nothing     <- md'
      , [(_,(_,u))] <- us
      = Stats.caseDefault "introduction" $ yes $ Case tag (map snd vs) (Just u)
      -- Convert case with only two alternatives to if-then-else, as we have
      -- more optimizations for conditionals
      | Nothing <- md'
      , [(tag1, alt1), (tag2, alt2)] <- xs'
      , expr <- snd $ cond (mkBinary (PrimCmp singleType CmpEq) tag $ Const scalarType tag1) (pure alt1) (pure alt2)
      = if shouldInline tag then
          -- Encode the information that 'tag' is either tag1 or tag2, in a way
          -- that bounds analysis will understand: making them the lower and
          -- upper bound of tag.
          yes $ snd $ assume
            (mkBinary PrimLAnd
              (mkBinary (PrimCmp singleType CmpGtEq) tag (Const scalarType $ min tag1 tag2))
              (mkBinary (PrimCmp singleType CmpGtEq) (Const scalarType $ max tag1 tag2) tag)
            )
            expr
        else
          yes expr
      | Just d <- md'
      , [(tag1, alt1)] <- xs'
      = yes $ snd $ cond (mkBinary (PrimCmp singleType CmpEq) tag $ Const scalarType tag1) (pure alt1) (pure d)
      | otherwise
      = Case tag <$> xs <*> md
      where
        tp
          | Just d <- md' = expType d
          | (_, x) : _ <- xs' = expType x
          | otherwise = internalError "Empty case statement should not occur"
        (us,vs) = partition (\(n,_) -> n > 1)
                $ Map.elems
                . Map.fromListWith merge
                $ [ (hashOpenExp e, (1,(t, e))) | (t,e) <- xs' ]

        merge :: (Int, (TAG, PreOpenExp arr env b)) -> (Int, (TAG, PreOpenExp arr env b)) -> (Int, (TAG, PreOpenExp arr env b))
        merge (n,(_,a)) (m,(_,b))
          = internalCheck "hashOpenExp/collision" (maybe False (const True) (matchOpenExp a b))
          $ (n+m, (0xff, a))

    arrayInstr :: arr (s -> t) -> PreOpenExp arr env s -> (Any, PreOpenExp arr env t)
    arrayInstr arr e = case arrayInstrType arr of
      -- When an array instruction returns unit, we don't have to evaluate it.
      -- This replaces the old rule which converted 'shape a' to Nil, if the array
      -- had dimension zero. As we now generalized expressions over the type of
      -- array instructions, we extend this rule to any array instructions returning
      -- unit. Though it will likely only trigger for zero dimensional arrays.
      TupRunit -> Stats.ruleFired "arrayInstr/nil" $ yes Nil
      _        -> pure $ ArrayInstr arr e

    -- Shape manipulations
    --
    shapeSize :: ShapeR sh -> PreOpenExp arr env sh -> (Any, PreOpenExp arr env Int)
    shapeSize shr sh
      | Just c <- extractConstTuple sh
      = Stats.ruleFired "shapeSize/const" $ yes (Const scalarTypeInt (product (shapeToList shr c)))
    shapeSize (ShapeRsnoc ShapeRz) (Pair _ sz)
      = Stats.ruleFired "shapeSize/I1" $ yes sz
    shapeSize shr sh
      = pure $ ShapeSize shr sh

    toIndex :: ShapeR sh
            -> PreOpenExp arr env sh
            -> PreOpenExp arr env sh
            -> (Any, PreOpenExp arr env Int)
    toIndex _ sh (FromIndex _ sh' ix)
      | Just Refl <- matchOpenExp sh sh' = Stats.ruleFired "toIndex/fromIndex" $ yes ix
    toIndex ShapeRz _ _                  = Stats.ruleFired "toIndex DIM0" $ yes $ Const scalarTypeInt 0
    toIndex (ShapeRsnoc ShapeRz) _ (Pair _ ix)
                                         = Stats.ruleFired "toIndex DIM1" $ yes ix
    toIndex (ShapeRsnoc ShapeRz) _ ix
                                         = Stats.ruleFired "toIndex DIM1" $ yes
                                         $ Let (LeftHandSidePair (LeftHandSideWildcard TupRunit) (LeftHandSideSingle scalarTypeInt))
                                           ix $ Evar $ Var scalarTypeInt ZeroIdx
    toIndex shr sh ix                    = pure $ ToIndex shr sh ix

    fromIndex :: ShapeR sh
              -> PreOpenExp arr env sh
              -> PreOpenExp arr env Int
              -> (Any, PreOpenExp arr env sh)
    fromIndex _ sh (ToIndex _ sh' ix)
      | Just Refl <- matchOpenExp sh sh' = Stats.ruleFired "fromIndex/toIndex" $ yes ix
    fromIndex ShapeRz _ _                = Stats.ruleFired "fromIndex DIM0" $ yes Nil
    fromIndex (ShapeRsnoc ShapeRz) _ ix
                                         = Stats.ruleFired "fromIndex DIM1" $ yes $ Pair Nil ix
    fromIndex shr sh ix                  = pure $ FromIndex shr sh ix

    vecPack :: KnownNat n => VecR n s tup -> PreOpenExp arr env tup -> (Any, PreOpenExp arr env (Vec n s))
    vecPack vecR (VecUnpack vecR' v)
      | Just Refl <- matchVecR vecR vecR' = yes v
    vecPack vecR e = pure $ VecPack vecR e

    vecUnpack :: KnownNat n => VecR n s tup -> PreOpenExp arr env (Vec n s) -> (Any, PreOpenExp arr env tup)
    vecUnpack vecR (VecPack vecR' v)
      | Just Refl <- matchVecR vecR vecR' = yes v
    vecUnpack vecR e = pure $ VecUnpack vecR e

    assert :: Text -> PreOpenExp arr env PrimBool -> PreOpenExp arr env t -> (Any, PreOpenExp arr env t)
    assert _ (Const _ 1) b = yes b
    assert msg c@(Const _ 0) b =
      let u = undefs $ expType b
      in (Any (isNothing $ matchOpenExp b u), Assert msg c u)
    assert msg1 (Assert msg2 c a) b = yes $ Assert msg2 c $ snd $ assert msg1 a b
    assert msg (Assume c a) b = yes $ Assume c $ snd $ assert msg a b
    assert msg c b = (Any False, Assert msg c b)

    assume :: PreOpenExp arr env PrimBool -> PreOpenExp arr env t -> (Any, PreOpenExp arr env t)
    assume (Const _ 1) b = yes b
    assume (Const _ 0) b = yes $ undefs $ expType b
    assume (Assume c a) b = yes $ Assume c $ snd $ assume a b
    assume c1 (Assume c2 b) = yes $ snd $ assume (PrimApp PrimLAnd (Pair c1 c2)) b
    assume c b = (Any False, Assume c b)

    first :: (a -> a') -> (a,b) -> (a',b)
    first f (x,y) = (f x, y)

yes :: x -> (Any, x)
yes x = (Any True, x)

hoist'
  :: (PreOpenExp arr env a -> (Any, PreOpenExp arr env t))
  -> PreOpenExp arr env a
  -> (Any, PreOpenExp arr env t)
hoist' f = \case
  Assert msg c a -> yes $ Assert msg c $ snd $ hoist' f a
  Assume c a -> yes $ Assume c $ snd $ hoist' f a
  e -> f e
  -- TODO: Should we also hoist let-bindings here?
  -- That would make the types more difficult

hoist
  :: (PreOpenExp arr env a -> (Any, PreOpenExp arr env t))
  -> (Any, PreOpenExp arr env a)
  -> (Any, PreOpenExp arr env t)
hoist f a = a >>= hoist' f

hoist2
  :: (PreOpenExp arr env a -> PreOpenExp arr env b -> (Any, PreOpenExp arr env t))
  -> (Any, PreOpenExp arr env a)
  -> (Any, PreOpenExp arr env b)
  -> (Any, PreOpenExp arr env t)
hoist2 f a b = hoist (\a' -> hoist (f a') b) a

extractConstTuple :: PreOpenExp arr env t -> Maybe t
extractConstTuple Nil          = Just ()
extractConstTuple (Pair e1 e2) = (,) <$> extractConstTuple e1 <*> extractConstTuple e2
extractConstTuple (Const _ c)  = Just c
extractConstTuple _            = Nothing

-- Simplification for open functions
--
simplifyOpenFun
    :: IsArrayInstr arr
    => Gamma arr env env
    -> PreOpenFun arr env f
    -> (Bool, PreOpenFun arr env f)
simplifyOpenFun env (Body e)    = Body    <$> simplifyOpenExp env  e
simplifyOpenFun env (Lam lhs f) = Lam lhs <$> simplifyOpenFun env' f
  where
    env' = lhsExpr lhs env

lhsExpr :: ELeftHandSide t env env' -> Gamma arr env env -> Gamma arr env' env'
lhsExpr (LeftHandSideWildcard _) env = env
lhsExpr (LeftHandSideSingle  tp) env = incExp env `pushExp` Evar (Var tp ZeroIdx)
lhsExpr (LeftHandSidePair l1 l2) env = lhsExpr l2 $ lhsExpr l1 env

-- Simplify closed expressions and functions. The process is applied
-- repeatedly until no more changes are made.
--
simplifyExp :: (HasCallStack, IsArrayInstr arr) => PreOpenExp arr () t -> PreOpenExp arr () t
simplifyExp = iterate summariseOpenExp matchOpenExp shrinkExp (simplifyOpenExp EmptyExp)

simplifyFun :: (HasCallStack, IsArrayInstr arr) => PreOpenFun arr () f -> PreOpenFun arr () f
simplifyFun = iterate summariseOpenFun matchOpenFun shrinkFun (simplifyOpenFun EmptyExp)


-- NOTE: [Simplifier iterations]
--
-- Run the simplification pass _before_ the shrinking step. There are cases
-- where it is better to run shrinking first, and then simplification would
-- complete in a single step, but the converse is also true. However, as
-- shrinking can remove some structure of the let bindings, which might be
-- useful for the transformations (e.g. loop recovery) we want to maintain this
-- information for at least the first pass.
--
-- We always apply the simplification step once. Following this, we iterate
-- shrinking and simplification until the expression no longer changes. Both
-- shrink and simplify return a boolean indicating whether any work was done; we
-- stop as soon as either returns false.
--
-- With internal checks on, we also issue a warning if the iteration limit is
-- reached, but it was still possible to make changes to the expression.
--

iterate
    :: forall f a. HasCallStack
    => (f a -> Stats)
    -> (forall s t. f s -> f t -> Maybe (s :~: t))  -- match
    -> (f a -> (Bool, f a))                         -- shrink
    -> (f a -> (Bool, f a))                         -- simplify
    -> f a
    -> f a
iterate summarise match shrink simplify = fix 1 . setup
  where
    -- The maximum number of simplifier iterations. To be conservative and avoid
    -- excessive run times, we (should) set this value very low.
    --
    -- TODO: make this tunable via debug flags.
    --
    lIMIT       = 25

    simplify'   = Stats.simplifierDone . simplify
    setup x     = Debug.trace Debug.dump_simpl_iterations (msg 0 "init" x)
                $ snd (trace 1 "simplify" (simplify' x))

    fix :: Int -> f a -> f a
    fix i x0
      | i > lIMIT       = internalWarning "iteration limit reached" (not (x0 ==^ simplify x0)) x0
      | not shrunk      = x1
      | not simplified  = x2
      | otherwise       = fix (i+1) x2
      where
        (shrunk,     x1) = trace i "shrink"   $ shrink x0
        (simplified, x2) = trace i "simplify" $ simplify' x1

    -- debugging support
    --
    u ==^ (_,v)         = isJust (match u v)

    trace i s v@(changed,x)
      | changed         = Debug.trace Debug.dump_simpl_iterations (msg i s x) v
      | otherwise       = v

    msg :: Int -> Builder -> f a -> Builder
    msg i s x = bformat ("simpl-iters/" % rpadded 9 ' ' builder % squared int % ": " % builder) s i (ppr x)

    ppr :: f a -> Builder
    ppr = stats . summarise

    stats (Stats a b c d e) =
      bformat ("terms = " % int % ", types = " % int % ", lets = " % int % ", vars = " % int % ", primops = " % int) a b c d e


-- Debugging support
-- -----------------

data Stats = Stats
  { _terms    :: {-# UNPACK #-} !Int
  , _types    :: {-# UNPACK #-} !Int
  , _binders  :: {-# UNPACK #-} !Int
  , _vars     :: {-# UNPACK #-} !Int
  , _ops      :: {-# UNPACK #-} !Int
  }

instance Semigroup Stats where
  (<>) = (+++)

instance Monoid Stats where
  mempty = Stats 0 0 0 0 0

infixl 6 +++
(+++) :: Stats -> Stats -> Stats
Stats a1 b1 c1 d1 e1 +++ Stats a2 b2 c2 d2 e2 = Stats (a1+a2) (b1+b2) (c1+c2) (d1+d2) (e1+e2)
{-# INLINE (+++) #-}

terms, types, binders, vars, ops :: Lens' Stats Int
terms   = lens _terms   (\Stats{..} v -> Stats { _terms   = v, ..})
types   = lens _types   (\Stats{..} v -> Stats { _types   = v, ..})
binders = lens _binders (\Stats{..} v -> Stats { _binders = v, ..})
vars    = lens _vars    (\Stats{..} v -> Stats { _vars    = v, ..})
ops     = lens _ops     (\Stats{..} v -> Stats { _ops     = v, ..})
{-# INLINE terms   #-}
{-# INLINE types   #-}
{-# INLINE binders #-}
{-# INLINE vars    #-}
{-# INLINE ops     #-}

summariseOpenFun :: PreOpenFun arr env f -> Stats
summariseOpenFun (Body e)  = summariseOpenExp e & terms +~ 1
summariseOpenFun (Lam _ f) = summariseOpenFun f & terms +~ 1 & binders +~ 1

summariseOpenExp :: PreOpenExp arr env t -> Stats
summariseOpenExp = (terms +~ 1) . goE
  where
    zero = Stats 0 0 0 0 0

    travE :: PreOpenExp arr env t -> Stats
    travE = summariseOpenExp

    travF :: PreOpenFun arr env t -> Stats
    travF = summariseOpenFun

    travA :: arr t -> Stats
    travA _ = zero & vars +~ 1  -- assume an array index, else we should have failed elsewhere

    travIntegralType :: IntegralType t -> Stats
    travIntegralType _ = zero & types +~ 1

    travFloatingType :: FloatingType t -> Stats
    travFloatingType _ = zero & types +~ 1

    travNumType :: NumType t -> Stats
    travNumType (IntegralNumType t) = travIntegralType t & types +~ 1
    travNumType (FloatingNumType t) = travFloatingType t & types +~ 1

    {- TODO WALL: DEAD CODE
    travBoundedType :: BoundedType t -> Stats
    travBoundedType (IntegralBoundedType t) = travIntegralType t & types +~ 1
    -}

    -- travScalarType :: ScalarType t -> Stats
    -- travScalarType (SingleScalarType t) = travSingleType t & types +~ 1
    -- travScalarType (VectorScalarType t) = travVectorType t & types +~ 1

    travSingleType :: SingleType t -> Stats
    travSingleType (NumSingleType t) = travNumType t & types +~ 1

    -- travVectorType :: VectorType t -> Stats
    -- travVectorType (Vector2Type t)  = travSingleType t & types +~ 1
    -- travVectorType (Vector3Type t)  = travSingleType t & types +~ 1
    -- travVectorType (Vector4Type t)  = travSingleType t & types +~ 1
    -- travVectorType (Vector8Type t)  = travSingleType t & types +~ 1
    -- travVectorType (Vector16Type t) = travSingleType t & types +~ 1

    -- The scrutinee has already been counted
    goE :: PreOpenExp arr env t -> Stats
    goE exp =
      case exp of
        Let _ bnd body        -> travE bnd +++ travE body & binders +~ 1
        Evar{}                -> zero & vars +~ 1
        Foreign _ _ _ x       -> travE x & terms +~ 1   -- +1 for asm, ignore fallback impls.
        Const{}               -> zero
        Undef _               -> zero
        Nil                   -> zero & terms +~ 1
        Pair e1 e2            -> travE e1 +++ travE e2 & terms +~ 1
        VecPack   _ e         -> travE e
        VecUnpack _ e         -> travE e
        ToIndex _ sh ix       -> travE sh +++ travE ix
        FromIndex _ sh ix     -> travE sh +++ travE ix
        Case e rhs def        -> travE e +++ mconcat [ travE c | (_,c) <- rhs ] +++ maybe zero travE def
        Cond p t e            -> travE p +++ travE t +++ travE e
        Select p t e          -> travE p +++ travE t +++ travE e
        While p f x           -> travF p +++ travF f +++ travE x
        ArrayInstr a e        -> travA a +++ travE e
        ShapeSize _ sh        -> travE sh
        PrimApp f x           -> travPrimFun f +++ travE x
        Coerce _ _ e          -> travE e
        Assert _ e1 e2        -> travE e1 +++ travE e2
        Assume e1 e2          -> travE e1 +++ travE e2

    travPrimFun :: PrimFun f -> Stats
    travPrimFun = (ops +~ 1) . goF
      where
        goF :: PrimFun f -> Stats
        goF fun =
          case fun of
            PrimAdd                t -> travNumType t
            PrimSub                t -> travNumType t
            PrimMul                t -> travNumType t
            PrimNeg                t -> travNumType t
            PrimAbs                t -> travNumType t
            PrimSig                t -> travNumType t
            PrimQuot               t -> travIntegralType t
            PrimRem                t -> travIntegralType t
            PrimQuotRem            t -> travIntegralType t
            PrimIDiv               t -> travIntegralType t
            PrimMod                t -> travIntegralType t
            PrimDivMod             t -> travIntegralType t
            PrimBAnd               t -> travIntegralType t
            PrimBOr                t -> travIntegralType t
            PrimBXor               t -> travIntegralType t
            PrimBNot               t -> travIntegralType t
            PrimBShiftL            t -> travIntegralType t
            PrimBShiftR            t -> travIntegralType t
            PrimBRotateL           t -> travIntegralType t
            PrimBRotateR           t -> travIntegralType t
            PrimPopCount           t -> travIntegralType t
            PrimCountLeadingZeros  t -> travIntegralType t
            PrimCountTrailingZeros t -> travIntegralType t
            PrimFDiv               t -> travFloatingType t
            PrimRecip              t -> travFloatingType t
            PrimSin                t -> travFloatingType t
            PrimCos                t -> travFloatingType t
            PrimTan                t -> travFloatingType t
            PrimAsin               t -> travFloatingType t
            PrimAcos               t -> travFloatingType t
            PrimAtan               t -> travFloatingType t
            PrimSinh               t -> travFloatingType t
            PrimCosh               t -> travFloatingType t
            PrimTanh               t -> travFloatingType t
            PrimAsinh              t -> travFloatingType t
            PrimAcosh              t -> travFloatingType t
            PrimAtanh              t -> travFloatingType t
            PrimExpFloating        t -> travFloatingType t
            PrimSqrt               t -> travFloatingType t
            PrimLog                t -> travFloatingType t
            PrimFPow               t -> travFloatingType t
            PrimLogBase            t -> travFloatingType t
            PrimTruncate         f i -> travFloatingType f +++ travIntegralType i
            PrimRound            f i -> travFloatingType f +++ travIntegralType i
            PrimFloor            f i -> travFloatingType f +++ travIntegralType i
            PrimCeiling          f i -> travFloatingType f +++ travIntegralType i
            PrimIsNaN              t -> travFloatingType t
            PrimIsInfinite         t -> travFloatingType t
            PrimAtan2              t -> travFloatingType t
            PrimCmp t _              -> travSingleType t
            PrimMax                t -> travSingleType t
            PrimMin                t -> travSingleType t
            PrimLAnd                 -> zero
            PrimLOr                  -> zero
            PrimLNot                 -> zero
            PrimFromIntegral     i n -> travIntegralType i +++ travNumType n
            PrimToFloating       n f -> travNumType n +++ travFloatingType f

