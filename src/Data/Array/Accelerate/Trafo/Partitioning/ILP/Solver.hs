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
module Data.Array.Accelerate.Trafo.Partitioning.ILP.Solver where

import qualified Data.Map as M
import qualified Data.Set as S
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Var (Var)
import Data.Array.Accelerate.Trafo.Partitioning.ILP.LinearConstraint


-- Currently the only instance is for MIP, which gives bindings to a couple of solvers.
-- Still, this way we minimise the surface that has to interact with MIP, can more easily
-- adapt if it changes, and we could easily add more bindings.
class ILPSolver ilp where
  solvePartial :: ilp -> ILP -> IO (Maybe Solution)


solve :: ILPSolver ilp => ilp -> ILP -> IO (Maybe Solution)
solve x ilp = fmap (<> M.fromSet (const 0) (allVars ilp)) -- add zeroes to the ILP for missing variables
           <$> solvePartial x (finalize ilp)

-- adds potentially missing constraints and bounds:
-- some solvers require all variables to have a bound
-- or all variables to be in a constraint.
finalize :: ILP -> ILP
finalize ilp@(ILP dir obj constr bnds n) =
  ILP dir obj (constr <> extraconstr) (bnds <> extrabnds) n
  where
    extraconstr = foldMap (\v -> int (-5) .<=. var v) (allVars ilp)
    extrabnds   = foldMap (Lower (-5))                (allVars ilp)

data OptDir = Maximise | Minimise
  deriving (Show, Eq)

data ILP = ILP OptDir Expression LinearConstraint Bounds Constants
  deriving (Show)

type Solution = M.Map Var Int

-- helpers for solving an ILP
allVars :: ILP -> S.Set Var
allVars (ILP _ cost constraint bounds _) = varsExpr cost <> varsConstr constraint <> varsBounds bounds

varsExpr :: Expression -> S.Set Var
varsExpr (Constant _) = mempty
varsExpr (a :+ b) = varsExpr a <> varsExpr b
varsExpr (_ :* v) = S.singleton v

varsConstr :: LinearConstraint -> S.Set Var
varsConstr TrueConstraint = mempty
varsConstr (a :&& b) = varsConstr a <> varsConstr b
varsConstr (a :>= b) = varsExpr a <> varsExpr b
varsConstr (a :== b) = varsExpr a <> varsExpr b
varsConstr (a :<= b) = varsExpr a <> varsExpr b

varsBounds :: Bounds -> S.Set Var
varsBounds NoBounds  = mempty
varsBounds (a :<> b) = varsBounds a <> varsBounds b
varsBounds (Binary v) = S.singleton v
varsBounds (LowerUpper _ v _) = S.singleton v
varsBounds (Lower _ v) = S.singleton v
varsBounds (Upper v _) = S.singleton v
