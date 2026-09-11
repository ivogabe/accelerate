module Data.Array.Accelerate.Trafo.Partitioning.ILP.NameGeneration where

import Control.Monad.State ( State, gets, modify )
import Data.Char ( ord )
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Var (Var)
import qualified Data.Map as M
import Lens.Micro.Mtl (zoom)
import Lens.Micro (_2)
import Control.Monad.Reader
import Data.Bifunctor


-- Apparently, solvers don't appreciate variable names longer than 255 characters!
-- Instead, we generate small placeholders here and store their meaning
type Names = (M.Map String Var, M.Map Var String)
type STN = State (Names, String)
-- to avoid generating keywords, we simply prepend every name with an 'x'. This still leaves 26^254 options, more than enough!
freshName' :: STN String
freshName' = zoom _2 $ freshName "x" 

-- Iterates in the following order:
-- ["", "a", .., "z", "aa", .., "za", "ab", .., "zz", "aaa", "baa", ...]
-- The prefix disembiguates from other uses of freshName, and avoids generating keywords.
freshName :: String -> State String String
freshName prefix = do
  modify increment
  gets ((prefix <> "_") <>)
  where
    increment (char:cs)
      | ord char < ord 'z' = toEnum (ord char + 1) : cs
      | otherwise = 'a' : increment cs
    increment "" = "a"

var' :: Var -> STN String
var' v = do
  maybeName <- gets $ (M.!? v) . snd . fst
  case maybeName of
    Just name -> return name
    Nothing -> do
      name <- freshName'
      modify $ first $ bimap (M.insert name v) (M.insert v name)
      return name

unvar' :: String -> Reader Names (Maybe Var)
unvar' name = asks $ (M.!? name) . fst

