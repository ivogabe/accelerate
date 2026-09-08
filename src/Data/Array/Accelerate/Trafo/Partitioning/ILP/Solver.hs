{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
module Data.Array.Accelerate.Trafo.Partitioning.ILP.Solver where

import qualified Data.Map as M
import qualified Data.Set as S
-- Uses an hs-boot file to break an unfortunate cyclic import situation with D.A.A.T.P.ILP.Graph:
-- `ILPSolver` references `Var` in type signatures, `Var` contains `BackendVar`,
-- `BackendVar` is in the class `MakesILP`, which references `Information`,
-- `Information` contains `Constraint` and `Bounds` from `ILPSolver`.
-- I did not want to put them in the same module, so here we are.
import {-# SOURCE #-} Data.Array.Accelerate.Trafo.Partitioning.ILP.Graph ( Var, MakesILP )
import Data.Foldable
import Data.Array.Accelerate.Error


-- Currently the only instance is for MIP, which gives bindings to a couple of solvers.
-- Still, this way we minimise the surface that has to interact with MIP, can more easily
-- adapt if it changes, and we could easily add more bindings.
class (MakesILP op) => ILPSolver ilp op where
  solvePartial :: ilp -> ILP op -> IO (Maybe (Solution op))

-- MakesILP op implies Ord (Var op), but not through Graph.hs-boot
solve :: (ILPSolver ilp op, Ord (Var op)) => ilp -> ILP op -> IO (Maybe (Solution op))
solve x ilp = fmap (<> M.fromSet (const 0) (allVars ilp)) -- add zeroes to the ILP for missing variables
           <$> solvePartial x (finalize ilp)

-- adds potentially missing constraints and bounds:
-- some solvers require all variables to have a bound
-- or all variables to be in a constraint.
finalize :: Ord (Var op) => ILP op -> ILP op
finalize ilp@(ILP dir obj constr bnds n) =
  ILP dir obj (constr <> extraconstr) (bnds <> extrabnds) n
  where
    extraconstr = foldMap (\v -> int (-5) .<=. var v) (allVars ilp)
    extrabnds   = foldMap (Lower (-5))                (allVars ilp)

data OptDir = Maximise | Minimise
  deriving (Show, Eq)

data ILP op = ILP OptDir (Expression op) (Constraint op) (Bounds op) Constants
deriving instance Show (Var op) => Show (ILP op)

type Solution op = M.Map (Var op) Int

data Constants = Constants
  { nComps :: Int  -- ^ number of computations in the ILP
  , nBuffs :: Int  -- ^ number of buffers in the ILP
  } deriving Show

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

data Expression op where
  Constant :: Number -> Expression op
  (:+)     :: Expression op -> Expression op -> Expression op
  (:*)     :: Number -> Var op -> Expression op
deriving instance Show (Var op) => Show (Expression op)

instance Semigroup (Expression op) where
  (<>) :: Expression op -> Expression op -> Expression op
  (<>) a (b :+ c) = (a <> b) <> c
  (<>) a b = a :+ b

instance Monoid (Expression op) where
  mempty :: Expression op
  mempty = int 0

data Constraint op where
  (:>=) :: Expression op -> Expression op -> Constraint op
  (:<=) :: Expression op -> Expression op -> Constraint op
  (:==) :: Expression op -> Expression op -> Constraint op
  (:&&) :: Constraint op -> Constraint op -> Constraint op
  TrueConstraint :: Constraint op
deriving instance Show (Var op) => Show (Constraint op)

instance Semigroup (Constraint op) where
  (<>) :: Constraint op -> Constraint op -> Constraint op
  (<>) TrueConstraint b = b
  (<>) a TrueConstraint = a
  (<>) a (b :&& c) = (a <> b) <> c
  (<>) a b = a :&& b

instance Monoid    (Constraint op) where
  mempty :: Constraint op
  mempty = TrueConstraint


data Bounds op where
  Binary :: Var op -> Bounds op
  LowerUpper :: Int -> Var op -> Int -> Bounds op
  Lower :: Int -> Var op -> Bounds op
  Upper :: Var op -> Int -> Bounds op
  (:<>) :: Bounds op -> Bounds op -> Bounds op
  NoBounds :: Bounds op
deriving instance Show (Var op) => Show (Bounds op)

instance Semigroup (Bounds op) where
  (<>) :: Bounds op -> Bounds op -> Bounds op
  (<>) NoBounds b = b
  (<>) a NoBounds = a
  (<>) (a :<> b) c = a <> b <> c
  (<>) a b = a :<> b

instance Monoid    (Bounds op) where
  mempty :: Bounds op
  mempty = NoBounds


-- | Add two expressions.
(.+.)  :: Expression op -> Expression op -> Expression op
(.+.) = (<>)
infixl 8 .+.

-- | Subtract two expressions.
(.-.)  :: Expression op -> Expression op -> Expression op
e1 .-. e2 = e1 .+. ((-1) .*. e2)
infixl 8 .-.

-- | Multiply an expression by a constant.
(.*.)  :: Number -> Expression op -> Expression op
i .*. (Constant j) = Constant $ i * j
i .*. (e1 :+ e2)   = (:+) (i .*. e1) (i .*. e2)
i .*. (j  :* v)    = (:*) (i * j) v
infixl 8 .*.

-- | Multiply by one of the @Constants@.
times :: (Constants -> Int) -> Expression op -> Expression op
times f = (Number f .*.)

-- | Multiply by @n@ (the total number of computations + some safety margine).
--
-- This is only here because the old definitions used timesN and not all of them
-- have been replaced yet.
-- TODO: Replace all occurrences of timesN with tighter bounds.
timesN :: Expression op -> Expression op
timesN = times ((+10) . (*2) . nComps)

-- | Use a 'Var' in an 'Expression'.
var :: Var op -> Expression op
var = (Number (const 1) :*)


class IsNumber a where
  -- | Use an `Int` as `Expression` or `Number`.
  int :: Int -> a

instance IsNumber Number where
  int = Number . const

instance IsNumber (Expression op) where
  int = Constant . Number . const


-- | @x >= y@
(.>=.) :: Expression op -> Expression op -> Constraint op
(.>=.) = (:>=)
infixr 7 .>=.

-- | @x <= y@
(.<=.) :: Expression op -> Expression op -> Constraint op
(.<=.) = (:<=)
infixr 7 .<=.

-- | @x == y@
(.==.) :: Expression op -> Expression op -> Constraint op
(.==.) = (:==)
infixr 7 .==.

-- | @x[0] == x[1] == ... == x[n-1]@
allEqual :: [Expression op] -> Constraint op
allEqual []     = TrueConstraint
allEqual (x:xs) = foldMap (x .==.) xs

-- | 'Var' is binary.
binary :: Var op -> Bounds op
binary = Binary

-- | 'Var' is bounded by lower and upper bounds.
lowerUpper :: Int -> Var op -> Int -> Bounds op
lowerUpper = LowerUpper

-- | 'Var' is bounded by lower bound.
lower :: Int -> Var op -> Bounds op
lower = Lower

-- | 'Var' is bounded by upper bound.
upper :: Var op -> Int -> Bounds op
upper = Upper

-- | 'Var' is equal to a constant.
equal :: Int -> Var op -> Bounds op
equal x v = lowerUpper x v x

-- | @x < y@
(.>.) :: Expression op -> Expression op -> Constraint op
x .>. y = x .>=. (y .+. int 1)
infixl 7 .>.

-- | @x < y@
(.<.) :: Expression op -> Expression op -> Constraint op
x .<. y = (x .+. int 1) .<=. y
infixl 7 .<.

-- | @x <= y <= z@
between :: Expression op -> Expression op -> Expression op -> Constraint op
between x y z = x .<=. y <> y .<=. z

-- | Not 'Expression' (i.e. 1 - 'Expression').
notB :: Expression op -> Expression op
notB e = int 1 .-. e

-- | If a is 0, then b is 0.
impliesB :: Expression op -> Expression op -> Constraint op
impliesB = (.>=.)

-- -- | Iff a and b are 0, then r is 0.
-- andB :: Expression op -> Expression op -> Expression op -> Constraint op
-- andB a b r = orB (notB a) (notB b) (notB r)

-- | Iff a and b are 0, then r is 0.
--
-- Source: "Formulating Integer Linear Programs: A Rogues' Gallery", B3
andB :: Expression op -> Expression op -> Expression op -> Constraint op
andB a b r = r .<=. a .+. b
          <> r .>=. a
          <> r .>=. b

-- | Iff all xs are 0, then r is 0.
allB :: Foldable f => f (Expression op) -> Expression op -> Constraint op
allB xs r | null xs   = TrueConstraint
          | otherwise = r .<=. fold xs
                     <> foldMap (r .>=.) xs

-- -- | Iff a and b are 1, then r is 1.
-- -- not sure if this encoding is new, nor whether it is the simplest, but I think it works.
-- -- perhaps defining andB is easier than defining orB?
-- orB :: Expression op -> Expression op -> Expression op -> Constraint op
-- orB a b r =
--   (2 .*. r .<=. a .+. b) -- r can only be 1 if both a and b are 1, so this line fixes 3/4 cases
--   <>
--   (r .+. int 1 .>=. a .+. b) -- and this line forces r to be 1 if a and b are both 1, while not restricting the other cases

-- | Iff a and b are 1, then r is 1.
--
-- Source: "Formulating Integer Linear Programs: A Rogues' Gallery", B2
orB :: Expression op -> Expression op -> Expression op -> Constraint op
orB a b r = r .+. int 1 .>=. a .+. b
         <> r .<=. a
         <> r .<=. b

-- | Iff all xs are 1, then r is 1.
anyB :: Foldable f => f (Expression op) -> Expression op -> Constraint op
anyB xs r | null xs   = TrueConstraint
          | otherwise = r .+. int (length xs - 1) .>=. fold xs
                     <> foldMap (r .<=.) xs

isEqualRangeN :: Expression op -> Expression op -> Expression op -> Constraint op
isEqualRangeN = isEqualRange timesN

-- given a function f that multiplies by the size of the domain of a and b, r can only be 0(true) when a and b are equal
-- note that r can always be 1
isEqualRange :: (Expression op -> Expression op) -> Expression op -> Expression op -> Expression op -> Constraint op
isEqualRange f a b r = between (a .-. f r) b (a .+. f r)


-- | From a set of booleans, select at most n to be 0 (true).
packB :: Foldable f => Int -> f (Expression op) -> Constraint op
packB n xs
  | n >= length xs = TrueConstraint
  | n >= 0         = fold xs .>=. int (length xs - n)
  | otherwise      = internalError "packB: always false"

-- | From a set of booleans, select at least n to be 0 (true).
coverB :: Foldable f => Int -> f (Expression op) -> Constraint op
coverB n xs
  | n <= 0         = TrueConstraint
  | n <= length xs = fold xs .<=. int (length xs - n)
  | otherwise      = internalError "coverB: always false"

-- | From a set of booleans, select exactly n to be 0 (true).
partitionB :: Foldable f => Int -> f (Expression op) -> Constraint op
partitionB n xs = packB n xs <> coverB n xs


-- helpers for solving an ILP
allVars :: Ord (Var op) => ILP op -> S.Set (Var op)
allVars (ILP _ cost constraint bounds _) = varsExpr cost <> varsConstr constraint <> varsBounds bounds

varsExpr :: Ord (Var op) => Expression op -> S.Set (Var op)
varsExpr (Constant _) = mempty
varsExpr (a :+ b) = varsExpr a <> varsExpr b
varsExpr (_ :* v) = S.singleton v

varsConstr :: Ord (Var op) => Constraint op -> S.Set (Var op)
varsConstr TrueConstraint = mempty
varsConstr (a :&& b) = varsConstr a <> varsConstr b
varsConstr (a :>= b) = varsExpr a <> varsExpr b
varsConstr (a :== b) = varsExpr a <> varsExpr b
varsConstr (a :<= b) = varsExpr a <> varsExpr b

varsBounds :: Ord (Var op) => Bounds op -> S.Set (Var op)
varsBounds NoBounds  = mempty
varsBounds (a :<> b) = varsBounds a <> varsBounds b
varsBounds (Binary v) = S.singleton v
varsBounds (LowerUpper _ v _) = S.singleton v
varsBounds (Lower _ v) = S.singleton v
varsBounds (Upper v _) = S.singleton v
