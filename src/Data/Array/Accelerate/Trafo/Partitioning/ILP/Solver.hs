{-# LANGUAGE GADTs #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE OverloadedStrings #-}
module Data.Array.Accelerate.Trafo.Partitioning.ILP.Solver where

import qualified Data.Map as M
import qualified Data.Set as S
-- Uses an hs-boot file to break an unfortunate cyclic import situation with D.A.A.T.P.ILP.Graph:
-- `ILPSolver` references `Var` in type signatures, `Var` contains `BackendVar`,
-- `BackendVar` is in the class `MakesILP`, which references `Information`,
-- `Information` contains `LinearConstraint` and `Bounds` from `ILPSolver`.
-- I did not want to put them in the same module, so here we are.
import {-# SOURCE #-} Data.Array.Accelerate.Trafo.Partitioning.ILP.Graph ( Var, MakesILP )
import Data.Array.Accelerate.Trafo.Partitioning.ILP.LinearConstraint
import Data.Array.Accelerate.Error
import Formatting                                       ( (%), shown )


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

evalExpr :: (Ord (Var op), Show (Var op)) => Constants -> Solution op -> Expression op -> Int
evalExpr consts sol = go
  where
    go (Constant (Number f)) = f consts
    go (a :+ b)              = go a + go b
    go (Number f :* v)       = f consts * value v

    value v = case M.lookup v sol of
      Just x  -> x
      Nothing -> internalError ("evalExpr: variable not in solution: " % shown) v

data OptDir = Maximise | Minimise
  deriving (Show, Eq)

data ILP op = ILP OptDir (Expression op) (LinearConstraint op) (Bounds op) Constants
deriving instance Show (Var op) => Show (ILP op)

type Solution op = M.Map (Var op) Int

-- helpers for solving an ILP
allVars :: Ord (Var op) => ILP op -> S.Set (Var op)
allVars (ILP _ cost constraint bounds _) = varsExpr cost <> varsConstr constraint <> varsBounds bounds

varsExpr :: Ord (Var op) => Expression op -> S.Set (Var op)
varsExpr (Constant _) = mempty
varsExpr (a :+ b) = varsExpr a <> varsExpr b
varsExpr (_ :* v) = S.singleton v

varsConstr :: Ord (Var op) => LinearConstraint op -> S.Set (Var op)
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
