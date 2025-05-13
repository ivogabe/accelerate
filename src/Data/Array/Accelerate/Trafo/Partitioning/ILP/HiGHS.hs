{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ViewPatterns #-}
module Data.Array.Accelerate.Trafo.Partitioning.ILP.HiGHS where
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Solver
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Graph (MakesILP)

import qualified Numeric.HiGHS.LP as LP
import Numeric.LinearProgramming.Common
import GHC.Float (int2Double)
import qualified Data.Map as M
import Data.Array.Comfort.Storable
import qualified Debug.Trace

-- DON'T USE
-- Even though HiGHS is also capable of MIP problems,
-- the highs-lp package only supports LP.
-- This is useless for us; we need ILP/MIP support.
-- Keeping this here in case we get around to forking highs-lp with ILP support.


data HiGHS = Highs

instance MakesILP op => ILPSolver HiGHS op where
  solvePartial Highs ilp@(ILP dir cost constraint bounds n) = pure . getSolution $
    LP.solve LP.choose bounds' constraint' (dir', cost')
    where
      vs = allVars ilp
      bounds' = highbounds bounds []
      constraint' = highconstraints n constraint []
      dir' = case dir of
        Maximise -> LP.Maximize
        Minimise -> LP.Minimize
      cost' = case highexpr n cost of (term,_constant) -> fromMap . M.unionWith (+) (M.fromSet (const 0) vs) $ term2Map term

getSolution (s, Nothing)      = Nothing
getSolution (s, Just (c,arr)) = Just (round <$> toMap arr)

term2Map [] = mempty
term2Map ((Term d v):ts) = M.unionWith (+) (M.singleton v d) (term2Map ts)

highbounds NoBounds = id
highbounds (a :<> b) = highbounds a . highbounds b
highbounds (Binary v)         = (:) $ Inequality v $ Between 0 1
highbounds (LowerUpper l v u) = (:) $ Inequality v $ Between (int2Double l) (int2Double u)
highbounds (Lower l v)        = (:) $ Inequality v $ GreaterEqual (int2Double l)
highbounds (Upper v u)        = (:) $ Inequality v $ LessEqual (int2Double u)

highconstraints n TrueConstraint = id
highconstraints n (a :&& b) = highconstraints n a . highconstraints n b
highconstraints n ((a :>= b)) = (:) $ case highexpr n (a.-.b) of (terms,((-1)*)-> c) -> Inequality terms $ GreaterEqual (int2Double c)
highconstraints n ((a :== b)) = (:) $ case highexpr n (a.-.b) of (terms,((-1)*)-> c) -> Inequality terms $ Equal (int2Double c)
highconstraints n ((a :<= b)) = (:) $ case highexpr n (a.-.b) of (terms,((-1)*)-> c) -> Inequality terms $ LessEqual (int2Double c)

highexpr n (Constant (Number m)) = ([],m n)
highexpr n ((Number m) :* v) = ([int2Double (m n) .* v],0)
highexpr n (a :+ b) = case (highexpr n a, highexpr n b) of
  ((t1,c),(t2,d)) -> (t1 `merge` t2,c+d)
  where
    merge [] xs = xs
    merge xs [] = xs
    merge (Term a x:xs) (Term b y:ys)
      | x == y = Term (a+b) x : merge xs ys
      | x < y = Term a x : merge xs (Term b y:ys)
      | y < x = Term b y : merge (Term a x:xs) ys
      | otherwise = error "simple math"
