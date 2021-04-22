{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeFamilyDependencies #-}
module Data.Array.Accelerate.Trafo.Partitioning.ILP.Solver where

import qualified Data.Map as M
-- Uses an hs-boot file to break an unfortunate cyclic import situation with D.A.A.T.P.ILP.Graph:
-- `ILPSolver` references `Var` in type signatures, `Var` contains `BackendVar`,
-- `BackendVar` is in the class `MakesILP`, which references `Information`,
-- `Information` contains `Constraint` and `Bounds` from `ILPSolver`.
-- I did not want to put them in the same module, so here we are.
import {-# SOURCE #-} Data.Array.Accelerate.Trafo.Partitioning.ILP.Graph ( Var, MakesILP )


-- (data)types that are needed for/used in the class, but need to be defined outside of it.
data OptDir = Maximise | Minimise
data ILP ilp op = ILP OptDir (Expression ilp op) (Constraint ilp op) (Bounds ilp op)
type Solution op = M.Map (Var op) Int


-- Has an instance for LIMP, could add more. The MIP library binds to many solvers,
-- and I enjoyed using that with Gurobi for a different project. Sadly, Gurobi is
-- proprietary (though they provide free licenses to academics).
-- TODO once stuff works, benchmark some large accelerate programs to find a fast
-- solver that we can integrate with Accelerate easily.
-- -David

-- Conceptually, this should be "class ILPSolver ilp where _". It's just more difficult
-- to add a "forall op. MakesILP op => (Monoid (Bounds ilp op), Monoid (Constraint ilp op))"
-- clause, and this way seems to "just work" with very little effort and good type inference/errors.
-- "Law": All instances should be polymorphic over `op` (instance (MakesILP op) => ILPSolver x op where _)
class ( MakesILP op
      , Monoid (Bounds     ilp op)
      , Monoid (Constraint ilp op)
   ) => ILPSolver ilp op where

  -- The functional dependencies aid type inference
  type Bounds     ilp op = a | a -> ilp op
  type Constraint ilp op = a | a -> ilp op
  type Expression ilp op = a | a -> ilp op

  (.+.)  :: Expression ilp op -> Expression ilp op -> Expression ilp op
  (.-.)  :: Expression ilp op -> Expression ilp op -> Expression ilp op
  (.*.)  :: Int               -> Var            op -> Expression ilp op 
  -- ^ Note: Asymmetric!
  
  (.>=.) :: Expression ilp op -> Expression ilp op -> Constraint ilp op
  (.<=.) :: Expression ilp op -> Expression ilp op -> Constraint ilp op
  (.==.) :: Expression ilp op -> Expression ilp op -> Constraint ilp op
  (.>.)  :: Expression ilp op -> Expression ilp op -> Constraint ilp op
  (.<.)  :: Expression ilp op -> Expression ilp op -> Constraint ilp op
  -- Has a default implementation, but Limp has a (perhaps faster?) specialisation (or it's just convenience...)
  between :: Expression ilp op -> Expression ilp op -> Expression ilp op -> Constraint ilp op
  between x y z = x .<=. y <> y .<=. z

  int :: Int -> Expression ilp op
  
  binary :: Var op -> Bounds ilp op
  lowerUpper :: Int -> Var op -> Int -> Bounds ilp op

  solve :: ILP ilp op -> IO (Maybe (Solution op))


