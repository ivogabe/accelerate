{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE OverloadedStrings #-}

module Data.Array.Accelerate.Trafo.Partitioning.ILP.LinearConstraint (Constants (..), Number (..), Expression (..), IsNumber (..), (.+.), (.-.), (.*.), times, timesN, nCompsE, var, LinearConstraint (..), (.>=.), (.<=.), (.==.), (.>.), (.<.), allEqual, between, Bounds (..), binary, lowerUpper, lower, upper, equal, notB, impliesB, andB, allB, orB, anyB, isEqualRangeN, isEqualRange, packB, coverB, partitionB) where

import Data.Array.Accelerate.Error
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Var (Var)
import Data.Foldable

data Constants = Constants
  { -- | number of computations in the ILP
    nComps :: Int,
    -- | number of buffers in the ILP
    nBuffs :: Int
  }
  deriving (Show)

-- | given `n` (for the number of nodes in the ILP), make an Int
newtype Number = Number (Constants -> Int)

instance Show Number where
  show :: Number -> String
  show (Number f) = "Number {" ++ show (f $ Constants 1 1) ++ "}"

instance Num Number where
  (+) :: Number -> Number -> Number
  (Number f) + (Number g) = Number (\c -> f c + g c)

  (*) :: Number -> Number -> Number
  (Number f) * (Number g) = Number (\c -> f c * g c)

  negate :: Number -> Number
  negate (Number f) = Number (negate . f)

  abs :: Number -> Number
  abs (Number f) = Number (abs . f)

  signum :: Number -> Number
  signum (Number f) = Number (signum . f)

  fromInteger :: Integer -> Number
  fromInteger i = Number (\_ -> fromInteger i)

data Expression where
  Constant :: Number -> Expression
  (:+) :: Expression -> Expression -> Expression
  (:*) :: Number -> Var -> Expression
  deriving (Show)

instance Semigroup Expression where
  (<>) :: Expression -> Expression -> Expression
  (<>) a (b :+ c) = (a <> b) <> c
  (<>) a b = a :+ b

instance Monoid Expression where
  mempty :: Expression
  mempty = int 0

-- | Add two expressions.
(.+.) :: Expression -> Expression -> Expression
(.+.) = (<>)

infixl 8 .+.

-- | Subtract two expressions.
(.-.) :: Expression -> Expression -> Expression
e1 .-. e2 = e1 .+. ((-1) .*. e2)

infixl 8 .-.

-- | Multiply an expression by a constant.
(.*.) :: Number -> Expression -> Expression
i .*. (Constant j) = Constant $ i * j
i .*. (e1 :+ e2) = (:+) (i .*. e1) (i .*. e2)
i .*. (j :* v) = (:*) (i * j) v

infixl 8 .*.

-- | Multiply by one of the @Constants@.
times :: (Constants -> Int) -> Expression -> Expression
times f = (Number f .*.)

-- | Multiply by @n@ (the total number of computations + some safety margine).
--
-- This is only here because the old definitions used timesN and not all of them
-- have been replaced yet.
-- TODO: Replace all occurrences of timesN with tighter bounds.
timesN :: Expression -> Expression
timesN = times ((+ 10) . (* 2) . nComps)

-- | Total number of computations.
nCompsE :: Expression
nCompsE = Constant $ Number nComps

-- | Use a 'Var' in an 'Expression'.
var :: Var -> Expression
var = (Number (const 1) :*)

class IsNumber a where
  -- | Use an `Int` as `Expression` or `Number`.
  int :: Int -> a

instance IsNumber Number where
  int = Number . const

instance IsNumber Expression where
  int = Constant . Number . const

data LinearConstraint where
  (:>=) :: Expression -> Expression -> LinearConstraint
  (:<=) :: Expression -> Expression -> LinearConstraint
  (:==) :: Expression -> Expression -> LinearConstraint
  (:&&) :: LinearConstraint -> LinearConstraint -> LinearConstraint
  TrueConstraint :: LinearConstraint
  deriving (Show)

instance Semigroup LinearConstraint where
  (<>) :: LinearConstraint -> LinearConstraint -> LinearConstraint
  (<>) TrueConstraint b = b
  (<>) a TrueConstraint = a
  (<>) a (b :&& c) = (a <> b) <> c
  (<>) a b = a :&& b

instance Monoid LinearConstraint where
  mempty :: LinearConstraint
  mempty = TrueConstraint

-- | @x >= y@
(.>=.) :: Expression -> Expression -> LinearConstraint
(.>=.) = (:>=)

infixr 7 .>=.

-- | @x <= y@
(.<=.) :: Expression -> Expression -> LinearConstraint
(.<=.) = (:<=)

infixr 7 .<=.

-- | @x == y@
(.==.) :: Expression -> Expression -> LinearConstraint
(.==.) = (:==)

infixr 7 .==.

-- | @x[0] == x[1] == ... == x[n-1]@
allEqual :: [Expression] -> LinearConstraint
allEqual [] = TrueConstraint
allEqual (x : xs) = foldMap (x .==.) xs

-- | @x < y@
(.>.) :: Expression -> Expression -> LinearConstraint
x .>. y = x .>=. (y .+. int 1)

infixl 7 .>.

-- | @x < y@
(.<.) :: Expression -> Expression -> LinearConstraint
x .<. y = (x .+. int 1) .<=. y

infixl 7 .<.

-- | @x <= y <= z@
between :: Expression -> Expression -> Expression -> LinearConstraint
between x y z = x .<=. y <> y .<=. z

data Bounds where
  Binary :: Var -> Bounds
  LowerUpper :: Int -> Var -> Int -> Bounds
  Lower :: Int -> Var -> Bounds
  Upper :: Var -> Int -> Bounds
  (:<>) :: Bounds -> Bounds -> Bounds
  NoBounds :: Bounds
  deriving (Show)

instance Semigroup Bounds where
  (<>) :: Bounds -> Bounds -> Bounds
  (<>) NoBounds b = b
  (<>) a NoBounds = a
  (<>) (a :<> b) c = a <> b <> c
  (<>) a b = a :<> b

instance Monoid Bounds where
  mempty :: Bounds
  mempty = NoBounds

-- | 'Var' is binary.
binary :: Var -> Bounds
binary = Binary

-- | 'Var' is bounded by lower and upper bounds.
lowerUpper :: Int -> Var -> Int -> Bounds
lowerUpper = LowerUpper

-- | 'Var' is bounded by lower bound.
lower :: Int -> Var -> Bounds
lower = Lower

-- | 'Var' is bounded by upper bound.
upper :: Var -> Int -> Bounds
upper = Upper

-- | 'Var' is equal to a constant.
equal :: Int -> Var -> Bounds
equal x v = lowerUpper x v x

-- | Not 'Expression' (i.e. 1 - 'Expression').
notB :: Expression -> Expression
notB e = int 1 .-. e

-- | If a is 0, then b is 0.
impliesB :: Expression -> Expression -> LinearConstraint
impliesB = (.>=.)

-- -- | Iff a and b are 0, then r is 0.
-- andB :: Expression -> Expression -> Expression -> LinearConstraint
-- andB a b r = orB (notB a) (notB b) (notB r)

-- | Iff a and b are 0, then r is 0.
--
-- Source: "Formulating Integer Linear Programs: A Rogues' Gallery", B3
andB :: Expression -> Expression -> Expression -> LinearConstraint
andB a b r =
  r .<=. a .+. b
    <> r .>=. a
    <> r .>=. b

-- | Iff all xs are 0, then r is 0.
allB :: (Foldable f) => f Expression -> Expression -> LinearConstraint
allB xs r
  | null xs = TrueConstraint
  | otherwise =
      r .<=. fold xs
        <> foldMap (r .>=.) xs

-- -- | Iff a and b are 1, then r is 1.
-- -- not sure if this encoding is new, nor whether it is the simplest, but I think it works.
-- -- perhaps defining andB is easier than defining orB?
-- orB :: Expression -> Expression -> Expression -> LinearConstraint
-- orB a b r =
--   (2 .*. r .<=. a .+. b) -- r can only be 1 if both a and b are 1, so this line fixes 3/4 cases
--   <>
--   (r .+. int 1 .>=. a .+. b) -- and this line forces r to be 1 if a and b are both 1, while not restricting the other cases

-- | Iff a and b are 1, then r is 1.
--
-- Source: "Formulating Integer Linear Programs: A Rogues' Gallery", B2
orB :: Expression -> Expression -> Expression -> LinearConstraint
orB a b r =
  r .+. int 1 .>=. a .+. b
    <> r .<=. a
    <> r .<=. b

-- | Iff all xs are 1, then r is 1.
anyB :: (Foldable f) => f Expression -> Expression -> LinearConstraint
anyB xs r
  | null xs = TrueConstraint
  | otherwise =
      r .+. int (length xs - 1) .>=. fold xs
        <> foldMap (r .<=.) xs

isEqualRangeN :: Expression -> Expression -> Expression -> LinearConstraint
isEqualRangeN = isEqualRange timesN

-- given a function f that multiplies by the size of the domain of a and b, r can only be 0(true) when a and b are equal
-- note that r can always be 1
isEqualRange :: (Expression -> Expression) -> Expression -> Expression -> Expression -> LinearConstraint
isEqualRange f a b r = between (a .-. f r) b (a .+. f r)

-- | From a set of booleans, select at most n to be 0 (true).
packB :: (Foldable f) => Int -> f Expression -> LinearConstraint
packB n xs
  | n >= length xs = TrueConstraint
  | n >= 0 = fold xs .>=. int (length xs - n)
  | otherwise = internalError "packB: always false"

-- | From a set of booleans, select at least n to be 0 (true).
coverB :: (Foldable f) => Int -> f Expression -> LinearConstraint
coverB n xs
  | n <= 0 = TrueConstraint
  | n <= length xs = fold xs .<=. int (length xs - n)
  | otherwise = internalError "coverB: always false"

-- | From a set of booleans, select exactly n to be 0 (true).
partitionB :: (Foldable f) => Int -> f Expression -> LinearConstraint
partitionB n xs = packB n xs <> coverB n xs
