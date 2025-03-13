{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE CPP                 #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE PatternGuards       #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}
{-# OPTIONS_HADDOCK hide #-}
-- |
-- Module      : Data.Array.Accelerate.Analysis.Exp
-- Copyright   : [2012..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.Analysis.Exp (
  isCommutative, isLeftIdentity, isRightIdentity, findLeftIdentity, findRightIdentity
) where

import Data.Array.Accelerate.AST.Exp
import Data.Array.Accelerate.AST.LeftHandSide
import Data.Array.Accelerate.AST.Environment
import Data.Array.Accelerate.Analysis.Match
import Data.Array.Accelerate.Representation.Type
import Data.Array.Accelerate.Type
import Data.Array.Accelerate.Trafo.Var
import Data.Array.Accelerate.Trafo.Exp.Simplify
import Data.Array.Accelerate.Trafo.Exp.Substitution
import Data.Array.Accelerate.Error

import Data.Maybe
import Data.List (find)
import Prelude hiding ( exp )

isCommutative :: IsArrayInstr arr => PreOpenFun arr () (a -> a -> b) -> Bool
isCommutative fun = isJust $ matchOpenFun fun' flipped
  where
    fun' = simplifyFun fun
    flipped = simplifyFun $ flipFun fun'

isLeftIdentity :: IsArrayInstr arr => PreOpenFun arr () (a -> b -> b) -> PreOpenExp arr () a -> Bool
isLeftIdentity fun arg = isJust $ isIdentity $ simplifyFun $ applyLeft fun arg

isRightIdentity :: IsArrayInstr arr => PreOpenFun arr () (a -> b -> a) -> PreOpenExp arr () b -> Bool
isRightIdentity fun arg = isJust $ isIdentity $ simplifyFun $ applyRight fun arg

findLeftIdentity :: IsArrayInstr arr => PreOpenFun arr () (a -> b -> b) -> Maybe a
findLeftIdentity fun = find (isLeftIdentity fun . mkConstant tp) (guesses tp)
  where
    tp = case fun of
      Lam lhs _ -> lhsToTupR lhs
      _ -> internalError "Expected binary function"

findRightIdentity :: IsArrayInstr arr => PreOpenFun arr () (a -> b -> a) -> Maybe b
findRightIdentity fun = find (isRightIdentity fun . mkConstant tp) (guesses tp)
  where
    tp = case fun of
      Lam _ (Lam lhs _) -> lhsToTupR lhs
      _ -> internalError "Expected binary function"

flipFun :: IsArrayInstr arr => PreOpenFun arr () (a -> b -> c) -> PreOpenFun arr () (b -> a -> c)
flipFun fun
  | DeclareVars lhsB _  valueB <- declareVars tpB
  , DeclareVars lhsA kA valueA <- declareVars tpA
  = Lam lhsB $ Lam lhsA $ Body
  $ apply fun (expVars $ valueA weakenId) (expVars $ valueB kA)
  where
    (tpA, tpB) = case fun of
      Lam lhsA (Lam lhsB _) -> (lhsToTupR lhsA, lhsToTupR lhsB)
      _ -> internalError "Expected binary function"

apply :: IsArrayInstr arr => PreOpenFun arr () (a -> b -> c) -> PreOpenExp arr env a -> PreOpenExp arr env b -> PreOpenExp arr env c
apply fun a b
  | Lam lhsA (Lam lhsB (Body body)) <- weakenE weakenEmpty fun
  = Let (LeftHandSidePair lhsA lhsB) (Pair a b) body
  | otherwise = internalError "Expected binary function"

applyLeft :: IsArrayInstr arr => PreOpenFun arr () (a -> b -> c) -> PreOpenExp arr () a -> PreOpenFun arr () (b -> c)
applyLeft fun arg = applyRight (flipFun fun) arg

applyRight :: IsArrayInstr arr => PreOpenFun arr () (a -> b -> c) -> PreOpenExp arr () b -> PreOpenFun arr () (a -> c)
applyRight (Lam lhsA (Lam lhsB (Body body))) arg
  = Lam lhsA $ Body $ Let lhsB (weakenE weakenEmpty arg) body
applyRight _ _ = internalError "Expected binary function"

data Guess = Zero | One | MinValue | MaxValue

guesses :: TypeR t -> [t]
guesses tp = mapMaybe (\g -> guess g tp) [Zero, One, MinValue, MaxValue]

guess :: Guess -> TypeR t -> Maybe t
guess _ TupRunit = Just ()
guess g (TupRsingle t) = guessScalar g t
guess g (TupRpair t1 t2) = (,) <$> guess g t1 <*> guess g t2

guessScalar :: Guess -> ScalarType t -> Maybe t
guessScalar g (SingleScalarType (NumSingleType (IntegralNumType t)))
  | IntegralDict <- integralDict t = case g of
    Zero -> Just 0
    One -> Just 1
    MinValue -> Just minBound
    MaxValue -> Just maxBound
guessScalar g (SingleScalarType (NumSingleType (FloatingNumType t)))
  | FloatingDict <- floatingDict t = case g of
    Zero -> Just 0
    One -> Just 1
    MinValue -> Just (-1/0) -- negative infinity
    MaxValue -> Just (1/0) -- infinity
guessScalar _ (VectorScalarType _) = Nothing
