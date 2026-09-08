{-# LANGUAGE MonoLocalBinds #-}
{-# OPTIONS_HADDOCK hide #-}
-- |
-- Module      : Data.Array.Accelerate.AST.CountEnv
-- Copyright   : [2008..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.AST.CountEnv (
  CountEnv, fromIdxSet, maxCount, findWithCount, findMostFrequent
  ) where

import Data.Array.Accelerate.AST.IdxSet (IdxSet)
import qualified Data.Array.Accelerate.AST.IdxSet as IdxSet
import Data.Array.Accelerate.AST.Environment hiding ( push )
import Data.List (foldl')

newtype CountEnv env = CountEnv (PartialEnv Count env)

newtype Count a = Count Int

fromIdxSet :: IdxSet env -> CountEnv env
fromIdxSet = CountEnv . mapPartialEnv (const $ Count 1) . IdxSet.unIdxSet

instance Semigroup (Count a) where
  Count x <> Count y = Count $ x + y

instance Monoid (Count a) where
  mempty = Count 0

instance Semigroup (CountEnv env) where
  CountEnv a <> CountEnv b = CountEnv $ unionPartialEnv (<>) a b

instance Monoid (CountEnv env) where
  mempty = CountEnv PEnd

maxCount :: CountEnv env -> Int
maxCount (CountEnv env) = foldl' (\x (EnvBinding _ (Count y)) -> max x y) 0 $ partialEnvToList env

findWithCount :: CountEnv env -> Int -> IdxSet env
findWithCount (CountEnv env) count = case env of
  PEnd           -> IdxSet.empty
  PPush env' (Count c)
    | count == c -> IdxSet.push $ findWithCount (CountEnv env') count
    | otherwise  -> IdxSet.skip $ findWithCount (CountEnv env') count
  PNone env'     -> IdxSet.skip $ findWithCount (CountEnv env') count

findMostFrequent :: CountEnv env -> (Int, IdxSet env)
findMostFrequent env = (count, findWithCount env count)
  where
    count = maxCount env
