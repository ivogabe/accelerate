{-# LANGUAGE MonoLocalBinds      #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_HADDOCK hide #-}
-- |
-- Module      : Data.Array.Accelerate.AST.IdxSet
-- Copyright   : [2008..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.AST.IdxSet (
  IdxSet(..),
  member, varMember, overlaps, isSubsetOf, intersect, union, unions, (\\), (>>=),
  insert, insertVar, insertVars, skip, skip',
  push, push', empty, isEmpty, drop, drop', remove, partialEnvRemoveSet, partialEnvFilterSet,
  fromList, fromList', fromVarList, fromVars, map,
  singleton, singletonVar, first, null,
  toList, rnfIdxSet
) where

import Prelude hiding (drop, (>>=), map, null)

import Data.Array.Accelerate.AST.Idx
import Data.Array.Accelerate.AST.Var
import Data.Array.Accelerate.AST.Environment hiding ( push, push' )
import Data.Array.Accelerate.AST.LeftHandSide
import Data.Array.Accelerate.Representation.Type
import Data.Maybe

newtype IdxSet env = IdxSet { unIdxSet :: PartialEnv Present env }

data Present a = Present

member :: Idx env t -> IdxSet env -> Bool
member idx (IdxSet set) = isJust $ prjPartial idx set

varMember :: Var s env t -> IdxSet env -> Bool
varMember (Var _ idx) = member idx

instance Eq (IdxSet env) where
  IdxSet PEnd == b = isEmpty b
  a == IdxSet PEnd = isEmpty a
  IdxSet (PPush a _) == IdxSet (PPush b _) = IdxSet a == IdxSet b
  IdxSet (PNone a) == IdxSet (PNone b) = IdxSet a == IdxSet b
  _ == _ = False

instance Semigroup (IdxSet env) where
  (<>) = union

instance Monoid (IdxSet env) where
  mempty = empty

overlaps :: IdxSet env -> IdxSet env -> Bool
overlaps (IdxSet (PPush _ _)) (IdxSet (PPush _ _)) = True
overlaps (IdxSet (PPush a _)) (IdxSet (PNone b  )) = overlaps (IdxSet a) (IdxSet b)
overlaps (IdxSet (PNone a  )) (IdxSet (PPush b _)) = overlaps (IdxSet a) (IdxSet b)
overlaps (IdxSet (PNone a  )) (IdxSet (PNone b  )) = overlaps (IdxSet a) (IdxSet b)
overlaps _ _ = False

isSubsetOf :: IdxSet env -> IdxSet env -> Bool
isSubsetOf (IdxSet (PPush a _)) (IdxSet (PPush b _)) = isSubsetOf (IdxSet a) (IdxSet b)
isSubsetOf (IdxSet (PNone a  )) (IdxSet (PPush b _)) = isSubsetOf (IdxSet a) (IdxSet b)
isSubsetOf (IdxSet (PPush _ _)) (IdxSet (PNone _  )) = False
isSubsetOf (IdxSet (PNone a  )) (IdxSet (PNone b  )) = isSubsetOf (IdxSet a) (IdxSet b)
isSubsetOf (IdxSet PEnd) _ = True
isSubsetOf a (IdxSet PEnd) = null a

intersect :: IdxSet env -> IdxSet env -> IdxSet env
intersect (IdxSet a) (IdxSet b) = IdxSet $ intersectPartialEnv (\_ _ -> Present) a b

union :: IdxSet env -> IdxSet env -> IdxSet env
union (IdxSet a) (IdxSet b) = IdxSet $ unionPartialEnv (\_ _ -> Present) a b

unions :: [IdxSet env] -> IdxSet env
unions []     = empty
unions [a]    = a
unions (a:as) = union a $ unions as

(\\) :: IdxSet env -> IdxSet env -> IdxSet env
IdxSet a \\ IdxSet b = IdxSet $ diffPartialEnv a b

(>>=) :: IdxSet env -> (forall t. Idx env t -> IdxSet env') -> IdxSet env'
set >>= f = unions $ fmap (\(Exists idx) -> f idx) $ toList set

insert :: Idx env t -> IdxSet env -> IdxSet env
insert idx (IdxSet a) = IdxSet $ partialUpdate Present idx a

insertVar :: Var s env t -> IdxSet env -> IdxSet env
insertVar (Var _ idx) = insert idx

insertVars :: Vars s env t -> IdxSet env -> IdxSet env
insertVars (TupRsingle (Var _ idx)) = insert idx
insertVars (TupRpair v1 v2) = insertVars v1 . insertVars v2
insertVars TupRunit = id

remove :: Idx env t -> IdxSet env -> IdxSet env
remove idx (IdxSet a) = IdxSet $ partialRemove idx a

partialEnvRemoveSet :: IdxSet env -> PartialEnv f env -> PartialEnv f env
partialEnvRemoveSet (IdxSet set) env = diffPartialEnv env set

partialEnvFilterSet :: IdxSet env -> PartialEnv f env -> PartialEnv f env
partialEnvFilterSet (IdxSet set) env = intersectPartialEnv (\_ f -> f) set env

skip :: IdxSet env -> IdxSet (env, t)
skip = IdxSet . PNone . unIdxSet

skip' :: LeftHandSide s t env env' -> IdxSet env -> IdxSet env'
skip' (LeftHandSideSingle _)   = skip
skip' (LeftHandSideWildcard _) = id
skip' (LeftHandSidePair l1 l2) = skip' l2 . skip' l1

push :: IdxSet env -> IdxSet (env, t)
push = IdxSet . flip PPush Present . unIdxSet

push' :: LeftHandSide s t env env' -> IdxSet env -> IdxSet env'
push' (LeftHandSideSingle _)   = push
push' (LeftHandSideWildcard _) = id
push' (LeftHandSidePair l1 l2) = push' l2 . push' l1

empty :: IdxSet env
empty = IdxSet PEnd

isEmpty :: IdxSet env -> Bool
isEmpty (IdxSet PEnd)        = True
isEmpty (IdxSet (PNone set)) = isEmpty $ IdxSet set
isEmpty _                    = False

drop :: IdxSet (env, t) -> IdxSet env
drop = IdxSet . partialEnvTail . unIdxSet

drop' :: LeftHandSide s t env env' -> IdxSet env' -> IdxSet env
drop' (LeftHandSidePair lhs1 lhs2) = drop' lhs1 . drop' lhs2
drop' (LeftHandSideWildcard _)     = id
drop' (LeftHandSideSingle _)       = drop

toList :: IdxSet env -> [Exists (Idx env)]
toList = fmap (\(EnvBinding idx _) -> Exists idx) . partialEnvToList . unIdxSet

fromList :: [Exists (Idx env)] -> IdxSet env
fromList = IdxSet . partialEnvFromList (\_ _ -> Present) . fmap (\(Exists idx) -> EnvBinding idx Present)

fromList' :: [Idx env t] -> IdxSet env
fromList' = IdxSet . partialEnvFromList (\_ _ -> Present) . fmap (\idx -> EnvBinding idx Present)

map :: (forall t. Idx env t -> Idx env' t) -> IdxSet env -> IdxSet env'
map f = fromList . fmap (\(Exists idx) -> Exists $ f idx) . toList

fromVarList :: [Exists (Var s env)] -> IdxSet env
fromVarList = fromList . fmap (\(Exists (Var _ idx)) -> Exists idx)

fromVars :: Vars s env t -> IdxSet env
fromVars = fromVarList . flattenTupR

singleton :: Idx env t -> IdxSet env
singleton idx = IdxSet $ partialEnvSingleton idx Present

singletonVar :: Var s env t -> IdxSet env
singletonVar (Var _ idx) = singleton idx

first :: IdxSet env -> Maybe (Exists (Idx env))
first (IdxSet (PPush _ _))                  = Just $ Exists ZeroIdx
first (IdxSet (PNone env))
  | Just (Exists idx) <- first (IdxSet env) = Just $ Exists $ SuccIdx idx
first _                                     = Nothing

null :: IdxSet env -> Bool
null (IdxSet (PPush _ _)) = False
null (IdxSet (PNone env)) = null (IdxSet env)
null _ = True

rnfIdxSet :: IdxSet env -> ()
rnfIdxSet = foldr (\(Exists ix) () -> rnfIdx ix) () . toList

instance Show (IdxSet env) where
  showsPrec p = showsPrec p . fmap (\(Exists idx) -> idxToInt idx) . toList
