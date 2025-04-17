{-# LANGUAGE GADTs #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeFamilyDependencies #-}
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
    extraconstr = foldMap (\v -> int (-5) .<=. c v) (allVars ilp)
    extrabnds   = foldMap (Lower (-5))              (allVars ilp)

data OptDir = Maximise | Minimise
  deriving Show

data ILP op = ILP OptDir (Expression op) (Constraint op) (Bounds op) Int
deriving instance Show (Var op) => Show (ILP op)

type Solution op = M.Map (Var op) Int

-- given `n` (for the number of nodes in the ILP), make an Int
newtype Number = Number (Int -> Int)
instance Show Number where
  show (Number f) = "Number {" ++ show (f 1) ++ "}"

data Expression op where
  Constant :: Number -> Expression op
  (:+)  :: Expression op -> Expression op -> Expression op
  (:*)  :: Number -> Var op -> Expression op
deriving instance Show (Var op) => Show (Expression op)

data Constraint op where
  (:>=) :: Expression op -> Expression op -> Constraint op
  (:<=) :: Expression op -> Expression op -> Constraint op
  (:==) :: Expression op -> Expression op -> Constraint op

  (:&&) :: Constraint op -> Constraint op -> Constraint op
  TrueConstraint :: Constraint op
deriving instance Show (Var op) => Show (Constraint op)

instance Semigroup (Constraint op) where (<>) = (:&&)
instance Monoid    (Constraint op) where mempty = TrueConstraint


data Bounds op where
  Binary :: Var op -> Bounds op
  LowerUpper :: Int -> Var op -> Int -> Bounds op
  Lower :: Int -> Var op -> Bounds op
  Upper :: Var op -> Int -> Bounds op
  (:<>) :: Bounds op -> Bounds op -> Bounds op
  NoBounds :: Bounds op
deriving instance Show (Var op) => Show (Bounds op)

instance Semigroup (Bounds op) where (<>) = (:<>)
instance Monoid    (Bounds op) where mempty = NoBounds


-- Synonyms for the constructors above: ease of defining ILP
infixl 8 .+.
infixl 8 .-.
infixl 8 .*.
(.+.)  :: Expression op -> Expression op -> Expression op
(.+.) = (:+)
(.-.)  :: Expression op -> Expression op -> Expression op
e1 .-. e2 = e1 .+. ((-1) .*. e2)
(.*.)  :: Int           -> Expression op -> Expression op
i .*. (Constant (Number f)) = Constant $ Number $ (*i) . f
i .*. (e1 :+ e2) = (:+) (i .*. e1) (i .*. e2)
i .*. (Number f :* v) = (:*) (Number ((*i) . f)) v
timesN :: Expression op -> Expression op
timesN (Constant (Number f)) = Constant (Number (\n -> n * f n))
timesN ((:+) e1 e2) = (:+) (timesN e1) (timesN e2)
timesN ((:*) (Number f) v) = (:*) (Number (\n -> n * f n)) v
-- | Convert 'Var' to 'Expression' (multiplies with 1).
c :: Var op -> Expression op
c = (Number (const 1) :*)
int :: Int -> Expression op
int = Constant . Number . const

infixr 7 .>=.
infixr 7 .<=.
infixr 7 .==.
(.>=.) :: Expression op -> Expression op -> Constraint op
(.>=.) = (:>=)
(.<=.) :: Expression op -> Expression op -> Constraint op
(.<=.) = (:<=)
(.==.) :: Expression op -> Expression op -> Constraint op
(.==.) = (:==)
binary :: Var op -> Bounds op
binary = Binary
lowerUpper :: Int -> Var op -> Int -> Bounds op
lowerUpper = LowerUpper
lower :: Int -> Var op -> Bounds op
lower = Lower
upper :: Var op -> Int -> Bounds op
upper = Upper
equal :: Int -> Var op -> Bounds op
equal x v = lowerUpper x v x

-- Convenience
(.>.)  :: Expression op -> Expression op -> Constraint op
x .>. y = x .>=. (y .+. int 1)
(.<.)  :: Expression op -> Expression op -> Constraint op
x .<. y = (x .+. int 1) .<=. y
between :: Expression op -> Expression op -> Expression op -> Constraint op
between x y z = x .<=. y <> y .<=. z


notB :: Expression op -> Expression op
notB e = int 1 .-. e

-- | If a is 0, then b must be 0
impliesB :: Expression op -> Expression op -> Constraint op
impliesB a b = a .>=. b

-- | Iff a and b are 0, the result is 0
andB  :: Expression op -> Expression op -> Expression op -> Constraint op
andB a b r = orB (notB a) (notB b) (notB r)

-- | Iff a and b are 1, r is 1
-- not sure if this encoding is new, nor whether it is the simplest, but I think it works.
-- perhaps defining andB is easier than defining orB?
orB :: Expression op -> Expression op -> Expression op -> Constraint op
orB a b r =
  (2 .*. r .<=. a .+. b) -- r can only be 1 if both a and b are 1, so this line fixes 3/4 cases
  <>
  (r .+. int 1 .>=. a .+. b) -- and this line forces r to be 1 if a and b are both 1, while not restricting the other cases

isEqualRangeN :: Expression op -> Expression op -> Expression op -> Constraint op
isEqualRangeN = isEqualRange timesN

-- given a function f that multiplies by the size of the domain of a and b, r can only be 0(true) when a and b are equal
-- note that r can always be 1
isEqualRange :: (Expression op -> Expression op) -> Expression op -> Expression op -> Expression op -> Constraint op
isEqualRange f a b r = a .-. f r .<=. b <> b .<=. a .+. f r


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
