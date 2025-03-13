{-# LANGUAGE TupleSections       #-}
{-# LANGUAGE CPP                 #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE PatternGuards       #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}
{-# LANGUAGE ViewPatterns        #-}
-- |
-- Module      : Data.Array.Accelerate.Trafo.Shrink
-- Copyright   : [2012..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--
-- The shrinking substitution arises as a restriction of beta-reduction to cases
-- where the bound variable is used zero (dead-code elimination) or one (linear
-- inlining) times. By simplifying terms, the shrinking reduction can expose
-- opportunities for further optimisation.
--
-- TODO: replace with a linear shrinking algorithm; e.g.
--
--   * Andrew Appel & Trevor Jim, "Shrinking lambda expressions in linear time".
--
--   * Nick Benton, Andrew Kennedy, Sam Lindley and Claudio Russo, "Shrinking
--     Reductions in SML.NET"
--

module Data.Array.Accelerate.Trafo.Shrink (

  -- Shrinking
  ShrinkAcc,
  shrinkExp,
  shrinkFun,

  -- Occurrence counting
  UsesOfAcc, usesOfPreAcc, usesOfExp,

) where

import Data.Array.Accelerate.AST
import Data.Array.Accelerate.AST.Environment
import Data.Array.Accelerate.AST.Idx
import Data.Array.Accelerate.AST.LeftHandSide
import Data.Array.Accelerate.AST.Var
import Data.Array.Accelerate.Analysis.Match
import Data.Array.Accelerate.Trafo.Exp.Shrink

import Prelude                                                      hiding ( exp, seq )


-- The shrinking substitution for array computations. This is further limited to
-- dead-code elimination only, primarily because linear inlining may inline
-- array computations into scalar expressions, which is generally not desirable.
--
type ShrinkAcc acc = forall aenv a. acc aenv a -> acc aenv a

{--
type ReduceAcc acc = forall aenv s t. acc aenv s -> acc (aenv,s) t -> Maybe (PreOpenAcc acc aenv t)

shrinkPreAcc
    :: forall acc aenv arrs. ShrinkAcc acc -> ReduceAcc acc
    -> PreOpenAcc acc aenv arrs
    -> PreOpenAcc acc aenv arrs
shrinkPreAcc shrinkAcc reduceAcc = Stats.substitution "shrinkA" shrinkA
  where
    shrinkA :: PreOpenAcc acc aenv' a -> PreOpenAcc acc aenv' a
    shrinkA pacc = case pacc of
      Alet lhs bnd body
        | Just reduct <- reduceAcc bnd' body'   -> shrinkA reduct
        | otherwise                             -> Alet lhs bnd' body'
        where
          bnd'  = shrinkAcc bnd
          body' = shrinkAcc body
      --
      Avar ix                   -> Avar ix
      Apair a1 a2               -> Apair (shrinkAcc a1) (shrinkAcc a2)
      Anil                      -> Anil
      Apply repr f a            -> Apply repr (shrinkAF f) (shrinkAcc a)
      Aforeign ff af a          -> Aforeign ff af (shrinkAcc a)
      Acond p t e               -> Acond (shrinkE p) (shrinkAcc t) (shrinkAcc e)
      Awhile p f a              -> Awhile (shrinkAF p) (shrinkAF f) (shrinkAcc a)
      Use repr a                -> Use repr a
      Unit e                    -> Unit (shrinkE e)
      Reshape e a               -> Reshape (shrinkE e) (shrinkAcc a)
      Generate e f              -> Generate (shrinkE e) (shrinkF f)
      Transform sh ix f a       -> Transform (shrinkE sh) (shrinkF ix) (shrinkF f) (shrinkAcc a)
      Replicate sl slix a       -> Replicate sl (shrinkE slix) (shrinkAcc a)
      Slice sl a slix           -> Slice sl (shrinkAcc a) (shrinkE slix)
      Map f a                   -> Map (shrinkF f) (shrinkAcc a)
      ZipWith f a1 a2           -> ZipWith (shrinkF f) (shrinkAcc a1) (shrinkAcc a2)
      Fold f z a                -> Fold (shrinkF f) (shrinkE z) (shrinkAcc a)
      Fold1 f a                 -> Fold1 (shrinkF f) (shrinkAcc a)
      FoldSeg f z a b           -> FoldSeg (shrinkF f) (shrinkE z) (shrinkAcc a) (shrinkAcc b)
      Fold1Seg f a b            -> Fold1Seg (shrinkF f) (shrinkAcc a) (shrinkAcc b)
      Scanl f z a               -> Scanl (shrinkF f) (shrinkE z) (shrinkAcc a)
      Scanl' f z a              -> Scanl' (shrinkF f) (shrinkE z) (shrinkAcc a)
      Scanl1 f a                -> Scanl1 (shrinkF f) (shrinkAcc a)
      Scanr f z a               -> Scanr (shrinkF f) (shrinkE z) (shrinkAcc a)
      Scanr' f z a              -> Scanr' (shrinkF f) (shrinkE z) (shrinkAcc a)
      Scanr1 f a                -> Scanr1 (shrinkF f) (shrinkAcc a)
      Permute f1 a1 f2 a2       -> Permute (shrinkF f1) (shrinkAcc a1) (shrinkF f2) (shrinkAcc a2)
      Backpermute sh f a        -> Backpermute (shrinkE sh) (shrinkF f) (shrinkAcc a)
      Stencil f b a             -> Stencil (shrinkF f) b (shrinkAcc a)
      Stencil2 f b1 a1 b2 a2    -> Stencil2 (shrinkF f) b1 (shrinkAcc a1) b2 (shrinkAcc a2)
      -- Collect s                 -> Collect (shrinkS s)

{--
    shrinkS :: PreOpenSeq acc aenv' senv a -> PreOpenSeq acc aenv' senv a
    shrinkS seq =
      case seq of
        Producer p s -> Producer (shrinkP p) (shrinkS s)
        Consumer c   -> Consumer (shrinkC c)
        Reify ix     -> Reify ix

    shrinkP :: Producer acc aenv' senv a -> Producer acc aenv' senv a
    shrinkP p =
      case p of
        StreamIn arrs        -> StreamIn arrs
        ToSeq sl slix a      -> ToSeq sl slix (shrinkAcc a)
        MapSeq f x           -> MapSeq (shrinkAF f) x
        ChunkedMapSeq f x    -> ChunkedMapSeq (shrinkAF f) x
        ZipWithSeq f x y     -> ZipWithSeq (shrinkAF f) x y
        ScanSeq f e x        -> ScanSeq (shrinkF f) (shrinkE e) x

    shrinkC :: Consumer acc aenv' senv a -> Consumer acc aenv' senv a
    shrinkC c =
      case c of
        FoldSeq f e x        -> FoldSeq (shrinkF f) (shrinkE e) x
        FoldSeqFlatten f a x -> FoldSeqFlatten (shrinkAF f) (shrinkAcc a) x
        Stuple t             -> Stuple (shrinkCT t)

    shrinkCT :: Atuple (Consumer acc aenv' senv) t -> Atuple (Consumer acc aenv' senv) t
    shrinkCT NilAtup        = NilAtup
    shrinkCT (SnocAtup t c) = SnocAtup (shrinkCT t) (shrinkC c)
--}

    shrinkE :: OpenExp env aenv' t -> OpenExp env aenv' t
    shrinkE exp = case exp of
      Let bnd body              -> Let (shrinkE bnd) (shrinkE body)
      Var idx                   -> Var idx
      Const c                   -> Const c
      Undef                     -> Undef
      Tuple t                   -> Tuple (shrinkT t)
      Prj tup e                 -> Prj tup (shrinkE e)
      IndexNil                  -> IndexNil
      IndexCons sl sz           -> IndexCons (shrinkE sl) (shrinkE sz)
      IndexHead sh              -> IndexHead (shrinkE sh)
      IndexTail sh              -> IndexTail (shrinkE sh)
      IndexSlice x ix sh        -> IndexSlice x (shrinkE ix) (shrinkE sh)
      IndexFull x ix sl         -> IndexFull x (shrinkE ix) (shrinkE sl)
      IndexAny                  -> IndexAny
      ToIndex sh ix             -> ToIndex (shrinkE sh) (shrinkE ix)
      FromIndex sh i            -> FromIndex (shrinkE sh) (shrinkE i)
      Cond p t e                -> Cond (shrinkE p) (shrinkE t) (shrinkE e)
      While p f x               -> While (shrinkF p) (shrinkF f) (shrinkE x)
      PrimConst c               -> PrimConst c
      PrimApp f x               -> PrimApp f (shrinkE x)
      Index a sh                -> Index (shrinkAcc a) (shrinkE sh)
      LinearIndex a i           -> LinearIndex (shrinkAcc a) (shrinkE i)
      Shape a                   -> Shape (shrinkAcc a)
      ShapeSize sh              -> ShapeSize (shrinkE sh)
      Intersect sh sz           -> Intersect (shrinkE sh) (shrinkE sz)
      Union sh sz               -> Union (shrinkE sh) (shrinkE sz)
      Foreign ff f e            -> Foreign ff (shrinkF f) (shrinkE e)
      Coerce e                  -> Coerce (shrinkE e)

    shrinkF :: OpenFun env aenv' f -> OpenFun env aenv' f
    shrinkF (Lam f)  = Lam (shrinkF f)
    shrinkF (Body b) = Body (shrinkE b)

    shrinkT :: Tuple (OpenExp env aenv') t -> Tuple (OpenExp env aenv') t
    shrinkT NilTup        = NilTup
    shrinkT (SnocTup t e) = shrinkT t `SnocTup` shrinkE e

    shrinkAF :: PreOpenAfun acc aenv' f -> PreOpenAfun acc aenv' f
    shrinkAF (Alam lhs f) = Alam lhs (shrinkAF f)
    shrinkAF (Abody a) = Abody (shrinkAcc a)
--}

-- Occurrence Counting
-- ===================

-- Count the number of occurrences of the array term bound at the given
-- environment index. If the first argument is 'True' then it includes in the
-- total uses of the variable for 'Shape' information, otherwise not.
--
type UsesOfAcc acc = forall aenv s t. Bool -> Idx aenv s -> acc aenv t -> Int

-- XXX: Should this be converted to use the above 'Count' semigroup?
--
usesOfPreAcc
    :: forall acc aenv s t.
       Bool
    -> UsesOfAcc  acc
    -> Idx            aenv s
    -> PreOpenAcc acc aenv t
    -> Int
usesOfPreAcc withShape countAcc idx = count
  where
    countIdx :: Idx aenv a -> Int
    countIdx this
        | Just Refl <- matchIdx this idx = 1
        | otherwise                      = 0

    count :: PreOpenAcc acc aenv a -> Int
    count pacc = case pacc of
      Avar var                   -> countAvar var
      --
      Alet lhs bnd body          -> countA bnd + countAcc withShape (weakenWithLHS lhs >:> idx) body
      Apair a1 a2                -> countA a1 + countA a2
      Anil                       -> 0
      Atrace _ a1 a2             -> countA a1 + countA a2
      Apply _ f a                -> countAF f idx + countA a
      Aforeign _ _ _ a           -> countA a
      Acond p t e                -> countE p + countA t + countA e
      -- Body and condition of the while loop may be evaluated multiple times.
      -- We multiply the usage count, as a practical solution to this. As
      -- we will check whether the count is at most 1, we will thus never
      -- inline variables used in while loops.
      Awhile c f a               -> 2 * countAF c idx + 2 * countAF f idx + countA a
      Use _ _                    -> 0
      Unit _ e                   -> countE e
      Reshape _ e a              -> countE e  + countA a
      Generate _ e f             -> countE e  + countF f
      Transform _ sh ix f a      -> countE sh + countF ix + countF f  + countA a
      Replicate _ sh a           -> countE sh + countA a
      Slice _ a sl               -> countE sl + countA a
      Map _ f a                  -> countF f  + countA a
      ZipWith _ f a1 a2          -> countF f  + countA a1 + countA a2
      Fold f z a                 -> countF f  + countME z + countA a
      FoldSeg _ f z a s          -> countF f  + countME z + countA a  + countA s
      Scan  _ f z a              -> countF f  + countME z + countA a
      Scan' _ f z a              -> countF f  + countE z  + countA a
      Permute f1 a1 a2           -> maybe 0 countF f1 + countA a1 + countA a2
      Backpermute _ sh f a       -> countE sh + countF f  + countA a
      Stencil _ _ f _ a          -> countF f  + countA a
      Stencil2 _ _ _ f _ a1 _ a2 -> countF f  + countA a1 + countA a2
      -- Collect s                 -> countS s

    countE :: OpenExp env aenv e -> Int
    countE = sum . map countArrayInstr . arrayInstrsInExp

    countME :: Maybe (OpenExp env aenv e) -> Int
    countME = maybe 0 countE

    countA :: acc aenv a -> Int
    countA = countAcc withShape idx

    countAvar :: ArrayVar aenv a -> Int
    countAvar (Var _ this) = countIdx this

    countAF :: PreOpenAfun acc aenv' f
            -> Idx aenv' s
            -> Int
    countAF (Alam lhs f) v = countAF f (weakenWithLHS lhs >:> v)
    countAF (Abody a)    v = countAcc withShape v a

    countArrayInstr :: Exists (ArrayInstr aenv) -> Int
    countArrayInstr (Exists (Shape       var)) = countAvar var
    countArrayInstr (Exists (Index       var)) = countAvar var
    countArrayInstr (Exists (LinearIndex var)) = countAvar var

    countF :: OpenFun env aenv e -> Int
    countF = sum . map countArrayInstr . arrayInstrsInFun

{--
    countS :: PreOpenSeq acc aenv senv arrs -> Int
    countS seq =
      case seq of
        Producer p s -> countP p + countS s
        Consumer c   -> countC c
        Reify _      -> 0

    countP :: Producer acc aenv senv arrs -> Int
    countP p =
      case p of
        StreamIn _           -> 0
        ToSeq _ _ a          -> countA a
        MapSeq f _           -> countAF f idx
        ChunkedMapSeq f _    -> countAF f idx
        ZipWithSeq f _ _     -> countAF f idx
        ScanSeq f e _        -> countF f + countE e

    countC :: Consumer acc aenv senv arrs -> Int
    countC c =
      case c of
        FoldSeq f e _        -> countF f + countE e
        FoldSeqFlatten f a _ -> countAF f idx + countA a
        Stuple t             -> countCT t

    countCT :: Atuple (Consumer acc aenv senv) t' -> Int
    countCT NilAtup        = 0
    countCT (SnocAtup t c) = countCT t + countC c
--}

