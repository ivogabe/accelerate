{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE PatternSynonyms       #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE StandaloneDeriving    #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeOperators         #-}
{-# OPTIONS_HADDOCK hide #-}
-- |
-- Module      : Data.Array.Accelerate.AST.LeftHandSide
-- Copyright   : [2008..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.AST.LeftHandSide
  (
    Exists(..),
    LeftHandSide(.., LeftHandSideUnit), leftHandSidePair,
    lhsToTupR, lhsSize, leftHandSideIsVoid,
    rnfLeftHandSide, liftLeftHandSide, mapLeftHandSide, flattenTupR)
  where

import Data.Array.Accelerate.Representation.Type

import Language.Haskell.TH.Extra
import Data.Typeable


data Exists f where
  Exists :: !(f a) -> Exists f

data LeftHandSide s v env env' where
  LeftHandSideSingle
    :: s v
    -> LeftHandSide s v env (env, v)

  LeftHandSideWildcard
    :: TupR s v
    -> LeftHandSide s v env env

  LeftHandSidePair
    :: LeftHandSide s v1       env  env'
    -> LeftHandSide s v2       env' env''
    -> LeftHandSide s (v1, v2) env  env''

deriving instance (forall a. Show (s a)) => Show (LeftHandSide s v env env')

pattern LeftHandSideUnit
    :: ()                   -- required
    => (env' ~ env, v ~ ()) -- provided
    => LeftHandSide s v env env'
pattern LeftHandSideUnit = LeftHandSideWildcard TupRunit

lhsToTupR :: LeftHandSide s v env env' -> TupR s v
lhsToTupR (LeftHandSideSingle s)   = TupRsingle s
lhsToTupR (LeftHandSideWildcard r) = r
lhsToTupR (LeftHandSidePair as bs) = TupRpair (lhsToTupR as) (lhsToTupR bs)

lhsSize :: LeftHandSide s v env env' -> Int
lhsSize (LeftHandSideWildcard _) = 0
lhsSize (LeftHandSidePair l1 l2) = lhsSize l1 + lhsSize l2
lhsSize (LeftHandSideSingle _)   = 1

rnfLeftHandSide :: (forall b. s b -> ()) -> LeftHandSide s v env env' -> ()
rnfLeftHandSide f (LeftHandSideWildcard r) = rnfTupR f r
rnfLeftHandSide f (LeftHandSideSingle s)   = f s
rnfLeftHandSide f (LeftHandSidePair as bs) = rnfLeftHandSide f as `seq` rnfLeftHandSide f bs

liftLeftHandSide :: (forall u. s u -> CodeQ (s u)) -> LeftHandSide s v env env' -> CodeQ (LeftHandSide s v env env')
liftLeftHandSide f (LeftHandSideSingle s)   = [|| LeftHandSideSingle $$(f s) ||]
liftLeftHandSide f (LeftHandSideWildcard r) = [|| LeftHandSideWildcard $$(liftTupR f r) ||]
liftLeftHandSide f (LeftHandSidePair as bs) = [|| LeftHandSidePair $$(liftLeftHandSide f as) $$(liftLeftHandSide f bs) ||]

mapLeftHandSide :: (forall v. s v -> u v) -> LeftHandSide s t env env' -> LeftHandSide u t env env'
mapLeftHandSide f (LeftHandSideSingle s)   = LeftHandSideSingle $ f s
mapLeftHandSide f (LeftHandSideWildcard r) = LeftHandSideWildcard $ mapTupR f r
mapLeftHandSide f (LeftHandSidePair as bs) = LeftHandSidePair (mapLeftHandSide f as) (mapLeftHandSide f bs)

leftHandSidePair :: LeftHandSide s t1 env env' -> LeftHandSide s t2 env' env'' -> LeftHandSide s (t1, t2) env env''
leftHandSidePair (LeftHandSideWildcard t1) (LeftHandSideWildcard t2) = LeftHandSideWildcard $ TupRpair t1 t2
leftHandSidePair l1 l2 = LeftHandSidePair l1 l2

flattenTupR :: TupR s t -> [Exists s]
flattenTupR = (`go` [])
  where
    go :: TupR s t -> [Exists s] -> [Exists s]
    go (TupRsingle s)   accum = Exists s : accum
    go (TupRpair t1 t2) accum = go t1 $ go t2 accum
    go TupRunit         accum = accum

leftHandSideIsVoid :: LeftHandSide s t env env' -> Maybe (env :~: env')
leftHandSideIsVoid (LeftHandSideWildcard _) = Just Refl
leftHandSideIsVoid (LeftHandSidePair l1 l2)
  | Just Refl <- leftHandSideIsVoid l1
  , Just Refl <- leftHandSideIsVoid l2 = Just Refl
leftHandSideIsVoid _ = Nothing
