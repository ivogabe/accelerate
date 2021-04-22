{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
module Data.Array.Accelerate.Trafo.Partitioning.ILP.Limp where

import Data.Array.Accelerate.Trafo.Partitioning.ILP.Graph (MakesILP, Var)
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Solver ( ILPSolver(..) )
import qualified Data.Map as M

-- Limp is a Linear Integer Mixed Programming library.
-- We only use the Integer part (not the Mixed part, 
-- which allows you to add non-integer variables and
-- constraints). It has a backend that binds to CBC, 
-- which is apparently a good one? Does not seem to be
-- actively maintained though.
import qualified Numeric.Limp.Program as LIMP
import qualified Numeric.Limp.Rep     as LIMP

data LIMP

-- | We have Int variables represented by @Variable op@, and no real variables.
-- These type synonyms instantiate the @z@, @r@ and @c@ type variables in Limp.
type Limp  datatyp op               = datatyp (Var op) () LIMP.IntDouble
type Limp' datatyp op (a :: LIMP.K) = datatyp (Var op) () LIMP.IntDouble a


-- Because we only use the integer part of this library, there's some integer<->real conversions
-- happening in this instance. Note also that we convert Int into Z IntDouble often.
instance MakesILP op => ILPSolver LIMP op where
  type Bounds     LIMP op = [Limp  LIMP.Bounds     op]
  type Constraint LIMP op =  Limp  LIMP.Constraint op
  type Expression LIMP op =  Limp' LIMP.Linear     op 'LIMP.KZ


  (.*.) = flip LIMP.z . LIMP.Z
  (.+.)  = (LIMP..+.)
  (.-.)  = (LIMP..-.)
  (.>=.) = (LIMP.:>=)
  (.<=.) = (LIMP.:<=)
  (.==.) = (LIMP.:==)
  (.>.)  = (LIMP.:>)
  (.<.)  = (LIMP.:<)
  
  int = LIMP.conZ . LIMP.Z
  between = LIMP.Between

  binary = pure . LIMP.binary
  lowerUpper l v u = pure $ LIMP.lowerUpperZ (LIMP.Z l) v (LIMP.Z u)

  -- TODO actually couple this to a backend, like limp-cbc
  solve problem = ((\(LIMP.Assignment m _) -> M.map (\(LIMP.Z x) -> x) m) <$>) <$> (_ problem :: IO (Maybe (Limp LIMP.Assignment op)))
