{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -fno-warn-orphans #-} -- Shame on me!
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE LambdaCase #-}

module Data.Array.Accelerate.Trafo.Partitioning.ILP.MIP (
  -- Exports default paths to 6 solvers, as well as an instance to ILPSolver for all of them
  cbc, cplex, glpsol, gurobiCl, lpSolve, scip,
  MIP(..)
  ) where

import Data.Array.Accelerate.Trafo.Partitioning.ILP.Graph (MakesILP)
import qualified Data.Array.Accelerate.Trafo.Partitioning.ILP.Graph as Graph (Var)
import Data.Array.Accelerate.Trafo.Partitioning.ILP.NameGeneration

import Data.Array.Accelerate.Trafo.Partitioning.ILP.Solver hiding (var)
import qualified Data.Map as M

import Numeric.Optimization.MIP hiding (Bounds, Constraint, Var, Solution, name)
import qualified Numeric.Optimization.MIP as MIP
import qualified Numeric.Optimization.MIP.Solver.Base as MIP
import Data.Scientific ( Scientific )
import Data.Bifunctor (bimap)

import Numeric.Optimization.MIP.Solver
    ( cbc, cplex, glpsol, gurobiCl, lpSolve, scip )
import Data.Maybe (mapMaybe)
import Control.Monad.State ( runState )
import Control.Monad.Reader ( Reader, asks, runReader )

newtype MIP s = MIP s

instance (MakesILP op, MIP.IsSolver s IO) => ILPSolver (MIP s) op where
  solvePartial :: MIP s -> ILP op -> IO (Maybe (Solution op))
  solvePartial (MIP s) ilp@(ILP dir obj constr bnds n) = makeSolution names <$> MIP.solve s options problem
    where
      options = def { MIP.solveTimeLimit   = Nothing --Just 60
                                -- , MIP.solveLogger      = putStrLn . ("AccILPSolver: "      ++)
                                , MIP.solveErrorLogger = putStrLn . ("AccILPSolverError: " ++)
      } --, MIP.solveCondensedSolution = False }
      vs = allVars ilp
      ((),(names, _)) = runState (mapM_ var' vs) ((mempty, mempty),"")

      readerProblem = Problem (Just "AccelerateILP")
        <$> (mkFun dir <$> expr n obj)
        <*> cons n constr
        <*> pure []
        <*> pure []
        <*> vartypes -- If any variables are not given a type, they won't get fixed by `solveCondensedSoluton` (and I'm also not sure whether Integer is the default).
        <*> bounds bnds
      problem = runReader readerProblem names

      -- varsOf :: [MIP.Constraint Scientific] -> [MIP.Var]
      -- varsOf = concatMap $ concatMap (\(Term _ vs)->vs) . (\(Expr ts)->ts) . MIP.constrExpr

      mkFun Maximise = ObjectiveFunction (Just "AccelerateObjective") OptMax
      mkFun Minimise = ObjectiveFunction (Just "AccelerateObjective") OptMin

      vartypes = allIntegers -- assuming that all variables have bounds


      -- addZeroes :: MIP.Problem Scientific -> MIP.Solution Scientific -> MIP.Solution Scientific
      -- addZeroes problem (MIP.Solution stat obj solmap) =
      --   -- Map.union is left-biased: only values not present in the solution are added.
      --   MIP.Solution stat obj $ M.union solmap (M.fromSet (const 0) (vars problem))

var :: Ord (Graph.Var op) => Graph.Var op -> Reader (Names op) MIP.Var
var y = asks (toVar . (M.! y) . snd)

-- MIP has a Num instance for expressions, but it's scary (because
-- you can't guarantee linearity with arbitrary multiplications).
-- We use that instance here, knowing that our own Expression can only be linear.
expr :: MakesILP op => Int -> Expression op -> Reader (Names op) (MIP.Expr Scientific)
expr n (Constant (Number f)) = pure $ fromIntegral (f n)
expr n (x :+ y) = (+) <$> expr n x <*> expr n y
expr n ((Number f) :* y) = (fromIntegral (f n) *) . varExpr <$> var y

cons :: MakesILP op => Int -> Constraint op -> Reader (Names op) [MIP.Constraint Scientific]
cons n (x :>= y) = (\a b -> [a MIP..>=. b]) <$> expr n x <*> expr n y
cons n (x :<= y) = (\a b -> [a MIP..<=. b]) <$> expr n x <*> expr n y
cons n (x :== y) = (\a b -> [a MIP..==. b]) <$> expr n x <*> expr n y

cons n (x :&& y) = (<>) <$> cons n x <*> cons n y
cons _ TrueConstraint = pure mempty

bounds :: MakesILP op => Bounds op -> Reader (Names op) (M.Map MIP.Var (Extended Scientific, Extended Scientific))
bounds (Binary v) = (`M.singleton` (Finite 0, Finite 1)) <$> var v
bounds (Lower      l v  ) = (`M.singleton` (Finite (fromIntegral l), PosInf                 )) <$> var v
bounds (     Upper   v u) = (`M.singleton` (NegInf                 , Finite (fromIntegral u))) <$> var v
bounds (LowerUpper l v u) = (`M.singleton` (Finite (fromIntegral l), Finite (fromIntegral u))) <$> var v
bounds (x :<> y) = M.unionWith (\(l1, u1) (l2, u2) -> (max l1 l2, min u1 u2)) <$> bounds x <*> bounds y
bounds NoBounds = pure mempty

-- -- For all variables not yet in bounds, we add infinite bounds. This is apparently required.
-- -- Potentially, it's more efficient to simply make a bounds map giving (NegInf, PosInf) to all variables (like in `allIntegers`), and then use `unionWith const`?
-- finishBounds :: M.Map MIP.Var (Extended Scientific, Extended Scientific) -> Reader (Names op) (M.Map MIP.Var (Extended Scientific, Extended Scientific))
-- finishBounds x = do
--   vars' <- asks $ map toVar . M.keys . fst
--   let y = M.keys x
--   return $ x <> (M.fromList . map (,(NegInf,PosInf)) . filter (not . (`elem` y)) $ vars')

-- -- we currently have no variables that ever get less then -2
-- extraConstraints :: Reader (Names op) [MIP.Constraint Scientific]
-- extraConstraints = do
--   vs <- asks $ map toVar . M.keys . fst
--   return [MIP.constExpr (-5) MIP..<=. MIP.varExpr x | x <- vs]

allIntegers :: Reader (Names op) (M.Map MIP.Var VarType)
allIntegers = asks $ M.fromList . map ((,IntegerVariable) . toVar) . M.keys . fst



makeSolution :: MakesILP op => Names op -> MIP.Solution Scientific -> Maybe (Solution op)
--                                   ------- Matching on solutions with a value: If this is Nothing, the model was infeasable or unbounded.
--                                   |    -- Instead matching on `MIP.Solution StatusOptimal _ m` often works too, but that doesn't work for
--                                   v    -- e.g. the identity program (which has an empty ILP).
makeSolution names (MIP.Solution _ (Just _) m) = Just . M.fromList . mapMaybe (sequence' . bimap (\v -> runReader (unvar' $ fromVar v) names) round) $ M.toList m
makeSolution _ _ = Nothing

-- tuple's traversable instance works on the second argument, we need it on the first
sequence' :: (Maybe a, b) -> Maybe (a, b)
sequence' (Nothing, _) = Nothing
sequence' (Just x, y) = Just (x, y)
