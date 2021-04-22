{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RoleAnnotations #-}
-- This file exists to break the cyclic import of Graph.hs and Solver.hs
module Data.Array.Accelerate.Trafo.Partitioning.ILP.Graph where
import Data.Kind (Type)

type role Var nominal -- Needed, because it defaults to 'representational' here
data Var (op :: Type -> Type)

class MakesILP (op :: Type -> Type)
