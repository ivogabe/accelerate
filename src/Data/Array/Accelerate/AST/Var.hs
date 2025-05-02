{-# LANGUAGE GADTs           #-}
{-# LANGUAGE RankNTypes      #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeOperators   #-}
{-# OPTIONS_HADDOCK hide #-}
-- |
-- Module      : Data.Array.Accelerate.AST.Var
-- Copyright   : [2008..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.AST.Var
  where

import Data.Array.Accelerate.Representation.Type
    ( TupR(..), mapTupR, liftTupR, rnfTupR )
import Data.Array.Accelerate.AST.Idx

import Language.Haskell.TH.Extra
import Data.Typeable                                                ( (:~:)(..) )


data Var  s env t = Var { varType :: s t, varIdx :: Idx env t }
type Vars s env   = TupR (Var s env)

varsType :: Vars s env t -> TupR s t
varsType TupRunit               = TupRunit
varsType (TupRsingle (Var t _)) = TupRsingle t
varsType (TupRpair a b)         = TupRpair (varsType a) (varsType b)


rnfVar :: (forall b. s b -> ()) -> Var s env t -> ()
rnfVar f (Var t idx) = f t `seq` rnfIdx idx

rnfVars :: (forall b. s b -> ()) -> Vars s env t -> ()
rnfVars f = rnfTupR (rnfVar f)

liftVar :: (forall b. s b -> CodeQ (s b)) -> Var s env t -> CodeQ (Var s env t)
liftVar f (Var s idx) = [|| Var $$(f s) $$(liftIdx idx) ||]

liftVars :: (forall b. s b -> CodeQ (s b)) -> Vars s env t -> CodeQ (Vars s env t)
liftVars f = liftTupR (liftVar f)

{-# INLINEABLE matchVar #-}
matchVar :: Var s env t1 -> Var s env t2 -> Maybe (t1 :~: t2)
matchVar (Var _ v1) (Var _ v2) = matchIdx v1 v2

{-# INLINEABLE matchVars #-}
matchVars :: Vars s env t1 -> Vars s env t2 -> Maybe (t1 :~: t2)
matchVars TupRunit         TupRunit = Just Refl
matchVars (TupRsingle v1) (TupRsingle v2)
  | Just Refl <- matchVar v1 v2 = Just Refl
matchVars (TupRpair v w) (TupRpair x y)
  | Just Refl <- matchVars v x
  , Just Refl <- matchVars w y  = Just Refl
matchVars _ _ = Nothing

mapVar :: (forall u. s u -> s' u) -> Var s env t -> Var s' env t
mapVar f (Var t ix) = Var (f t) ix

mapVars :: (forall u. s u -> s' u) -> Vars s env t -> Vars s' env t
mapVars f = mapTupR (mapVar f)

instance Show (Var s env t) where
  show (Var _ idx) = "Var " ++ show (idxToInt idx)
