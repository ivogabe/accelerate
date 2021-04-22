{-# LANGUAGE ConstraintKinds     #-}
{-# LANGUAGE EmptyCase           #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE PatternGuards       #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TupleSections       #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE TypeOperators       #-}
{-# LANGUAGE ViewPatterns        #-}
{-# OPTIONS_HADDOCK hide #-}
-- |
-- Module      : Data.Array.Accelerate.Trafo.Exp.Substitution
-- Copyright   : [2012..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.Trafo.Exp.Substitution (

  -- ** Renaming & Substitution
  inline, inlineVars, compose,
  subTop, apply1, apply2,

  -- ** Weakening
  (:>), SinkExp(..), weakenVars,

  -- ** Strengthening
  (:?>), strengthenE,

  -- ** Rebuilding terms
  RebuildableExp(..), rebuildLHS,
  lhsFullVars,

  RebuildArrayInstr, rebuildArrayInstrMap,
  rebuildNoArrayInstr,

  -- ** Checks
  isIdentity, extractExpVars,
  bindingIsTrivial,

) where

import Data.Array.Accelerate.AST.Exp
import Data.Array.Accelerate.AST.LeftHandSide
import Data.Array.Accelerate.AST.Var
import Data.Array.Accelerate.AST.Idx
import Data.Array.Accelerate.AST.Environment
import Data.Array.Accelerate.Analysis.Match
import Data.Array.Accelerate.Error
import Data.Array.Accelerate.Representation.Type
import qualified Data.Array.Accelerate.Debug.Internal.Stats      as Stats

import Data.Kind
import Control.Applicative                              hiding ( Const )
import Control.Monad
import Prelude                                          hiding ( exp, seq )

infixr `compose`


lhsFullVars :: forall s a env1 env2. LeftHandSide s a env1 env2 -> Maybe (Vars s env2 a)
lhsFullVars = fmap snd . go weakenId
  where
    go :: forall env env' b. (env' :> env2) -> LeftHandSide s b env env' -> Maybe (env :> env2, Vars s env2 b)
    go k (LeftHandSideWildcard TupRunit) = Just (k, TupRunit)
    go k (LeftHandSideSingle s) = Just $ (weakenSucc $ k, TupRsingle $ Var s $ k >:> ZeroIdx)
    go k (LeftHandSidePair l1 l2)
      | Just (k',  v2) <- go k  l2
      , Just (k'', v1) <- go k' l1 = Just (k'', TupRpair v1 v2)
    go _ _ = Nothing

bindingIsTrivial :: LeftHandSide s a env1 env2 -> Vars s env2 b -> Maybe (a :~: b)
bindingIsTrivial lhs vars
  | Just lhsVars <- lhsFullVars lhs
  , Just Refl    <- matchVars vars lhsVars
  = Just Refl
bindingIsTrivial _ _ = Nothing

isIdentity :: PreOpenFun arr env (a -> b) -> Maybe (a :~: b)
isIdentity (Lam lhs (Body (extractExpVars -> Just vars))) = bindingIsTrivial lhs vars
isIdentity _ = Nothing

-- | Replace the first variable with the given expression. The environment
-- shrinks.
--
inline :: PreOpenExp arr (env, s) t
       -> PreOpenExp arr env      s
       -> PreOpenExp arr env      t
inline f g = Stats.substitution "inline" $ rebuildE (subTop g) f

inlineVars :: forall arr env env' t1 t2.
              ELeftHandSide t1 env env'
           ->        PreOpenExp arr env' t2
           ->        PreOpenExp arr env  t1
           -> Maybe (PreOpenExp arr env  t2)
inlineVars lhsBound expr bound
  | Just vars <- lhsFullVars lhsBound = substitute (strengthenWithLHS lhsBound) weakenId vars expr
  where
    substitute
        :: forall env1 env2 t.
           env1 :?> env2
        -> env :> env2
        -> ExpVars env1 t1
        -> PreOpenExp arr env1 t
        -> Maybe (PreOpenExp arr env2 t)
    substitute _ k2 vars (extractExpVars -> Just vars')
      | Just Refl <- matchVars vars vars' = Just $ weakenE k2 bound
    substitute k1 k2 vars topExp = case topExp of
      Let lhs e1 e2
        | Exists lhs' <- rebuildLHS lhs
                          -> Let lhs' <$> travE e1 <*> substitute (strengthenAfter lhs lhs' k1) (weakenWithLHS lhs' .> k2) (weakenWithLHS lhs `weakenVars` vars) e2
      Evar (Var t ix)     -> Evar . Var t <$> k1 ix
      Foreign tp asm f e1 -> Foreign tp asm f <$> travE e1
      Pair e1 e2          -> Pair <$> travE e1 <*> travE e2
      Nil                 -> Just Nil
      VecPack   vec e1    -> VecPack   vec <$> travE e1
      VecUnpack vec e1    -> VecUnpack vec <$> travE e1
      IndexSlice si e1 e2 -> IndexSlice si <$> travE e1 <*> travE e2
      IndexFull  si e1 e2 -> IndexFull  si <$> travE e1 <*> travE e2
      ToIndex   shr e1 e2 -> ToIndex   shr <$> travE e1 <*> travE e2
      FromIndex shr e1 e2 -> FromIndex shr <$> travE e1 <*> travE e2
      Case e1 rhs def     -> Case <$> travE e1 <*> mapM (\(t,c) -> (t,) <$> travE c) rhs <*> travMaybeE def
      Cond e1 e2 e3       -> Cond <$> travE e1 <*> travE e2 <*> travE e3
      While f1 f2 e1      -> While <$> travF f1 <*> travF f2 <*> travE e1
      Const t c           -> Just $ Const t c
      PrimConst c         -> Just $ PrimConst c
      PrimApp p e1        -> PrimApp p <$> travE e1
      ArrayInstr arr e1   -> ArrayInstr arr <$> travE e1
      ShapeSize shr e1    -> ShapeSize shr <$> travE e1
      Undef t             -> Just $ Undef t
      Coerce t1 t2 e1     -> Coerce t1 t2 <$> travE e1

      where
        travE :: PreOpenExp arr env1 s -> Maybe (PreOpenExp arr env2 s)
        travE = substitute k1 k2 vars

        travF :: PreOpenFun arr env1 s -> Maybe (PreOpenFun arr env2 s)
        travF = substituteF k1 k2 vars

        travMaybeE :: Maybe (PreOpenExp arr env1 s) -> Maybe (Maybe (PreOpenExp arr env2 s))
        travMaybeE Nothing  = pure Nothing
        travMaybeE (Just x) = Just <$> travE x

    substituteF :: forall env1 env2 t.
               env1 :?> env2
            -> env :> env2
            -> ExpVars env1 t1
            -> PreOpenFun arr env1 t
            -> Maybe (PreOpenFun arr env2 t)
    substituteF k1 k2 vars (Body e) = Body <$> substitute k1 k2 vars e
    substituteF k1 k2 vars (Lam lhs f)
      | Exists lhs' <- rebuildLHS lhs = Lam lhs' <$> substituteF (strengthenAfter lhs lhs' k1) (weakenWithLHS lhs' .> k2) (weakenWithLHS lhs `weakenVars` vars) f

inlineVars _ _ _ = Nothing


-- | Composition of unary functions.
--
compose :: HasCallStack
        => PreOpenFun arr env (b -> c)
        -> PreOpenFun arr env (a -> b)
        -> PreOpenFun arr env (a -> c)
compose f@(Lam lhsB (Body c)) g@(Lam lhsA (Body b))
  | Stats.substitution "compose" False = undefined
  | Just Refl <- isIdentity f = g -- don't rebind an identity function
  | Just Refl <- isIdentity g = f

  | Exists lhsB' <- rebuildLHS lhsB
  = Lam lhsA
  $ Body
  $ Let lhsB' b
  $ weakenE (sinkWithLHS lhsB lhsB' $ weakenWithLHS lhsA) c
  -- = Stats.substitution "compose" . Lam lhs2 . Body $ substitute' f g
compose _
  _ = internalError "compose: impossible evaluation"

subTop :: PreOpenExp arr env s -> ExpVar (env, s) t -> PreOpenExp arr env t
subTop s (Var _  ZeroIdx     ) = s
subTop _ (Var tp (SuccIdx ix)) = Evar $ Var tp ix

-- Applies an argument to a unary function
--
apply1 :: IsArrayInstr arr => TypeR t -> PreOpenFun arr () (s -> t) -> PreOpenExp arr env s -> PreOpenExp arr env t
apply1 tp fun arg = case weakenE (weakenEmpty) fun of
  Body e            -> functionImpossible $ expType e
  Lam lhs (Body b)  -> Let lhs arg b
  Lam _ (Lam _ _)   -> functionImpossible tp

-- Applies arguments to a binary function
--
apply2 :: IsArrayInstr arr => TypeR t -> PreOpenFun arr () (s -> u -> t) -> PreOpenExp arr env s -> PreOpenExp arr env u -> PreOpenExp arr env t
apply2 tp fun a1 a2 = case weakenE (weakenEmpty) fun of
  Body e                   -> functionImpossible $ expType e
  Lam _ (Body e)           -> functionImpossible $ expType e
  Lam l1 (Lam l2 (Body b)) -> Let (LeftHandSidePair l1 l2) (Pair a1 a2) b
  Lam _  (Lam _ (Lam _ _)) -> functionImpossible tp

-- A class for rebuilding scalar terms.
--
class RebuildableExp f where
  {-# MINIMAL rebuildPartialE, rebuildArrayInstrPartial #-}
  rebuildPartialE :: (Applicative f', SyntacticExp fe)
                  => (forall e'. ExpVar env e' -> f' (fe arr env' e'))
                  -> f arr env e
                  -> f' (f arr env' e)

  {-# INLINEABLE rebuildE #-}
  rebuildE :: SyntacticExp fe
           => (forall e'. ExpVar env e' -> fe arr env' e')
           -> f arr env  e
           -> f arr env' e
  rebuildE v = runIdentity . rebuildPartialE (Identity . v)

  rebuildArrayInstrPartial :: Applicative f'
                           => RebuildArrayInstr f' arr arr'
                           -> f arr env e
                           -> f' (f arr' env e)

  {-# INLINEABLE rebuildArrayInstr #-}
  rebuildArrayInstr :: (forall s t env'. arr (s -> t) -> PreOpenExp arr' env' s -> PreOpenExp arr' env' t)
                    -> f arr env e
                    -> f arr' env e
  rebuildArrayInstr v = runIdentity . rebuildArrayInstrPartial (Identity . v)

instance RebuildableExp PreOpenExp where
  {-# INLINEABLE rebuildPartialE #-}
  rebuildPartialE v x = Stats.substitution "rebuild" $ rebuildOpenExp v x

  {-# INLINEABLE rebuildArrayInstrPartial #-}
  rebuildArrayInstrPartial v x = Stats.substitution "rebuildArrayInstr" $ rebuildArrayInstrOpenExp v x

instance RebuildableExp PreOpenFun where
  {-# INLINEABLE rebuildPartialE #-}
  rebuildPartialE v x = Stats.substitution "rebuild" $ rebuildFun v x

  {-# INLINEABLE rebuildArrayInstrPartial #-}
  rebuildArrayInstrPartial v x = Stats.substitution "rebuildArrayInstr" $ rebuildArrayInstrFun v x

rebuildNoArrayInstr :: RebuildableExp f => f NoArrayInstr env e -> f arr env e
rebuildNoArrayInstr = rebuildArrayInstr k
  where
    k :: NoArrayInstr t -> a
    k a = case a of {}

-- NOTE: [Weakening]
--
-- Weakening is something we usually take for granted: every time you learn a
-- new word, old sentences still make sense. If a conclusion is justified by a
-- hypothesis, it is still justified if you add more hypotheses. Similarly, a
-- term remains in scope if you bind more (fresh) variables. Weakening is the
-- operation of shifting things from one scope to a larger scope in which new
-- things have become meaningful, but no old things have vanished.
--
-- When we use a named representation (or HOAS) we get weakening for free. But
-- in the de Bruijn representation weakening takes work: you have to shift all
-- variable references to make room for the new bindings.
--

-- TODO: Should we merge this type class with Sink? 'weaken' and 'weakenE' now have the same
-- type, because of various refactorings.
--
class SinkExp (f :: Type -> Type -> Type) where
  weakenE :: env :> env' -> f env t -> f env' t

  -- TLM: We can't use this default instance because it doesn't lead to
  --      specialised code. Perhaps the INLINEABLE pragma is ignored: GHC bug?
  --
  -- {-# INLINEABLE weakenE #-}
  -- default weakenE :: RebuildableExp f => env :> env' -> f arr env t -> f arr env' t
  -- weakenE v = Stats.substitution "weakenE" . rebuildE (IE . v)

instance SinkExp Idx where
  {-# INLINEABLE weakenE #-}
  weakenE = (>:>)

instance SinkExp (Var s) where
  {-# INLINEABLE weakenE #-}
  weakenE k (Var s ix) = Var s (k >:> ix)

instance SinkExp (PreOpenExp arr) where
  {-# INLINEABLE weakenE #-}
  weakenE v = Stats.substitution "weakenE" . rebuildE (rebuildWeakenEvar v)

instance SinkExp (PreOpenFun arr) where
  {-# INLINEABLE weakenE #-}
  weakenE v = Stats.substitution "weakenE" . rebuildE (rebuildWeakenEvar v)

-- This rewrite rule is disabled because 'weaken' is now part of a type class.
-- As such, we cannot attach a NOINLINE pragma because it has many definitions.
-- {-# RULES
-- "weakenE/weakenE" forall a (v1 :: env' :> env'') (v2 :: env :> env').
--    weakenE v1 (weakenE v2 a) = weakenE (v1 . v2) a
--  #-}

weakenVars :: env :> env' -> Vars s env t -> Vars s env' t
weakenVars _  TupRunit      = TupRunit
weakenVars k (TupRsingle v) = TupRsingle $ weakenE k v
weakenVars k (TupRpair v w) = TupRpair (weakenVars k v) (weakenVars k w)

rebuildWeakenEvar :: env :> env' -> ExpVar env t -> PreOpenExp arr env' t
rebuildWeakenEvar k (Var s idx) = Evar $ Var s $ k >:> idx

-- NOTE: [Strengthening]
--
-- Strengthening is the dual of weakening. Shifting terms from one scope to a
-- smaller scope. Of course this is not always possible. If the term contains
-- any variables not in the new environment, then it cannot be strengthened.
-- This partial behaviour is captured with 'Maybe'.
--

-- The type of partially shifting terms from one context into another.
type env :?> env' = forall t'. Idx env t' -> Maybe (Idx env' t')

{-# INLINEABLE strengthenE #-}
strengthenE :: forall f arr env env' t. RebuildableExp f => env :?> env' -> f arr env t -> Maybe (f arr env' t)
strengthenE k x = Stats.substitution "strengthenE" $ rebuildPartialE @f @Maybe @IdxE (\(Var tp ix) -> fmap (IE . Var tp) $ k ix) x

strengthenWithLHS :: LeftHandSide s t env1 env2 -> env2 :?> env1
strengthenWithLHS (LeftHandSideWildcard _) = Just
strengthenWithLHS (LeftHandSideSingle _)   = \ix -> case ix of
  ZeroIdx   -> Nothing
  SuccIdx i -> Just i
strengthenWithLHS (LeftHandSidePair l1 l2) = strengthenWithLHS l2 >=> strengthenWithLHS l1

strengthenAfter :: LeftHandSide s t env1 env2 -> LeftHandSide s t env1' env2' -> env1 :?> env1' -> env2 :?> env2'
strengthenAfter (LeftHandSideWildcard _) (LeftHandSideWildcard _) k = k
strengthenAfter (LeftHandSideSingle _)   (LeftHandSideSingle _)   k = \ix -> case ix of
  ZeroIdx   -> Just ZeroIdx
  SuccIdx i -> SuccIdx <$> k i
strengthenAfter (LeftHandSidePair l1 l2) (LeftHandSidePair l1' l2') k =
  strengthenAfter l2 l2' $ strengthenAfter l1 l1' k
strengthenAfter _ _ _ = error "Substitution.strengthenAfter: left hand sides do not match"


-- Simultaneous Substitution ===================================================
--

-- The scalar environment
-- ------------------

-- SEE: [Renaming and Substitution]
-- SEE: [Weakening]
--
class SyntacticExp f where
  varIn         :: ExpVar env t -> f arr env t
  expOut        :: f arr env t -> PreOpenExp arr env t
  weakenExp     :: f arr env t -> f arr (env, s) t

newtype IdxE (arr :: Type -> Type) env t = IE { unIE :: ExpVar env t }

instance SyntacticExp IdxE where
  varIn          = IE
  expOut         = Evar . unIE
  weakenExp (IE (Var tp ix)) = IE $ Var tp $ SuccIdx ix

instance SyntacticExp PreOpenExp where
  varIn          = Evar
  expOut         = id
  weakenExp      = runIdentity . rebuildOpenExp (Identity . weakenExp . IE)

{-# INLINEABLE shiftE #-}
shiftE
    :: (Applicative f, SyntacticExp fe)
    => RebuildEvar f fe arr env      env'
    -> RebuildEvar f fe arr (env, s) (env', s)
shiftE _ (Var tp ZeroIdx)      = pure $ varIn (Var tp ZeroIdx)
shiftE v (Var tp (SuccIdx ix)) = weakenExp <$> v (Var tp ix)

{-# INLINEABLE shiftE' #-}
shiftE'
    :: (Applicative f, SyntacticExp fe)
    => ELeftHandSide t env1 env1'
    -> ELeftHandSide t env2 env2'
    -> RebuildEvar f fe arr env1  env2
    -> RebuildEvar f fe arr env1' env2'
shiftE' (LeftHandSideWildcard _) (LeftHandSideWildcard _) v = v
shiftE' (LeftHandSideSingle _)   (LeftHandSideSingle _)   v = shiftE v
shiftE' (LeftHandSidePair a1 b1) (LeftHandSidePair a2 b2) v = shiftE' b1 b2 $ shiftE' a1 a2 v
shiftE' _ _ _ = error "Substitution: left hand sides do not match"

type RebuildEvar f fe (arr :: Type -> Type) env env' =
  forall t'. ExpVar env t' -> f (fe arr env' t')

{-# INLINEABLE rebuildMaybeExp #-}
rebuildMaybeExp
    :: (HasCallStack, Applicative f, SyntacticExp fe)
    => RebuildEvar f fe arr env env'
    -> Maybe (PreOpenExp arr env  t)
    -> f (Maybe (PreOpenExp arr env' t))
rebuildMaybeExp _ Nothing  = pure Nothing
rebuildMaybeExp v (Just x) = Just <$> rebuildOpenExp v x

{-# INLINEABLE rebuildOpenExp #-}
rebuildOpenExp
    :: (HasCallStack, Applicative f, SyntacticExp fe)
    => RebuildEvar f fe arr env env'
    -> PreOpenExp arr env  t
    -> f (PreOpenExp arr env' t)
rebuildOpenExp v exp =
  case exp of
    Const t c           -> pure $ Const t c
    PrimConst c         -> pure $ PrimConst c
    Undef t             -> pure $ Undef t
    Evar var            -> expOut          <$> v var
    Let lhs a b
      | Exists lhs' <- rebuildLHS lhs
                        -> Let lhs'        <$> rebuildOpenExp v a  <*> rebuildOpenExp (shiftE' lhs lhs' v) b
    Pair e1 e2          -> Pair            <$> rebuildOpenExp v e1 <*> rebuildOpenExp v e2
    Nil                 -> pure Nil
    VecPack   vec e     -> VecPack   vec   <$> rebuildOpenExp v e
    VecUnpack vec e     -> VecUnpack vec   <$> rebuildOpenExp v e
    IndexSlice x ix sh  -> IndexSlice x    <$> rebuildOpenExp v ix <*> rebuildOpenExp v sh
    IndexFull x ix sl   -> IndexFull x     <$> rebuildOpenExp v ix <*> rebuildOpenExp v sl
    ToIndex shr sh ix   -> ToIndex shr     <$> rebuildOpenExp v sh <*> rebuildOpenExp v ix
    FromIndex shr sh ix -> FromIndex shr   <$> rebuildOpenExp v sh <*> rebuildOpenExp v ix
    Case e rhs def      -> Case            <$> rebuildOpenExp v e  <*> sequenceA [ (t,) <$> rebuildOpenExp v c | (t,c) <- rhs ] <*> rebuildMaybeExp v def
    Cond p t e          -> Cond            <$> rebuildOpenExp v p  <*> rebuildOpenExp v t  <*> rebuildOpenExp v e
    While p f x         -> While           <$> rebuildFun v p      <*> rebuildFun v f      <*> rebuildOpenExp v x
    PrimApp f x         -> PrimApp f       <$> rebuildOpenExp v x
    ArrayInstr arr e    -> ArrayInstr arr  <$> rebuildOpenExp v e
    ShapeSize shr sh    -> ShapeSize shr   <$> rebuildOpenExp v sh
    Foreign tp ff f e   -> Foreign tp ff f <$> rebuildOpenExp v e
    Coerce t1 t2 e      -> Coerce t1 t2    <$> rebuildOpenExp v e

{-# INLINEABLE rebuildFun #-}
rebuildFun
    :: (HasCallStack, Applicative f, SyntacticExp fe)
    => RebuildEvar f fe arr env env'
    -> PreOpenFun arr env   t
    -> f (PreOpenFun arr env' t)
rebuildFun v fun =
  case fun of
    Body e -> Body <$> rebuildOpenExp v e
    Lam lhs f
      | Exists lhs' <- rebuildLHS lhs
        -> Lam lhs' <$> rebuildFun (shiftE' lhs lhs' v) f

{-# INLINEABLE rebuildLHS #-}
rebuildLHS :: LeftHandSide s t aenv1 aenv1' -> Exists (LeftHandSide s t aenv2)
rebuildLHS (LeftHandSideWildcard r) = Exists $ LeftHandSideWildcard r
rebuildLHS (LeftHandSideSingle s)   = Exists $ LeftHandSideSingle s
rebuildLHS (LeftHandSidePair as bs)
  | Exists as' <- rebuildLHS as
  , Exists bs' <- rebuildLHS bs
  = Exists $ LeftHandSidePair as' bs'

type RebuildArrayInstr f arr arr' = forall s t env. arr (s -> t) -> f (PreOpenExp arr' env s -> PreOpenExp arr' env t)

-- RebuildArrayInstr corresponds to the bind of a monad, meaning that a single array instruction can
-- be transformed to an expressions, possibly containing multiple array instructions. For many cases
-- it may be sufficient to only have the functor (map) interface. This function converts a map-like
-- function to the bind-like function.
--
rebuildArrayInstrMap
    :: Applicative f
    => (forall s t. arr (s -> t) -> f (arr' (s -> t)))
    -> RebuildArrayInstr f arr arr'
rebuildArrayInstrMap f arr = ArrayInstr <$> f arr

rebuildArrayInstrOpenExp
    :: forall f arr arr' env t.
       (HasCallStack, Applicative f)
    => RebuildArrayInstr f arr arr'
    -> PreOpenExp arr  env t
    -> f (PreOpenExp arr' env t)
rebuildArrayInstrOpenExp v = \case
    Let lhs e1 e2            -> Let lhs <$> travE e1 <*> travE e2
    Evar var                 -> pure $ Evar var
    Foreign t asm f x        -> Foreign t asm f <$> travE x
    Pair e1 e2               -> Pair <$> travE e1 <*> travE e2
    Nil                      -> pure Nil
    VecPack   vecr e         -> VecPack   vecr <$> travE e
    VecUnpack vecr e         -> VecUnpack vecr <$> travE e
    IndexSlice slice slix sh -> IndexSlice slice <$> travE slix <*> travE sh
    IndexFull  slice slix sl -> IndexFull  slice <$> travE slix <*> travE sl
    ToIndex   shr sh ix      -> ToIndex   shr <$> travE sh <*> travE ix
    FromIndex shr sh ix      -> FromIndex shr <$> travE sh <*> travE ix
    Case e rhs def           -> Case <$> travE e <*> sequenceA [ (t,) <$> travE c | (t,c) <- rhs ] <*> travME def
    Cond e1 e2 e3            -> Cond <$> travE e1 <*> travE e2 <*> travE e3
    While c f x              -> While <$> travF c <*> travF f <*> travE x
    Const tp c               -> pure $ Const tp c
    PrimConst prim           -> pure $ PrimConst prim
    PrimApp f x              -> PrimApp f <$> travE x
    ArrayInstr arr x         -> v arr <*> travE x
    ShapeSize shr sh         -> ShapeSize shr <$> travE sh
    Undef tp                 -> pure $ Undef tp
    Coerce t1 t2 e           -> Coerce t1 t2 <$> travE e
  where
    travE :: PreOpenExp arr env' t' -> f (PreOpenExp arr' env' t')
    travE = rebuildArrayInstrOpenExp v

    travF :: PreOpenFun arr env' t' -> f (PreOpenFun arr' env' t')
    travF = rebuildArrayInstrFun v

    travME :: Maybe (PreOpenExp arr env' t') -> f (Maybe (PreOpenExp arr' env' t'))
    travME Nothing = pure Nothing
    travME (Just e) = Just <$> travE e

rebuildArrayInstrFun
    :: (HasCallStack, Applicative f)
    => RebuildArrayInstr f arr arr'
    -> PreOpenFun arr  env t
    -> f (PreOpenFun arr' env t)
rebuildArrayInstrFun v (Body e)    = Body <$> rebuildArrayInstrOpenExp v e
rebuildArrayInstrFun v (Lam lhs f) = Lam lhs <$> rebuildArrayInstrFun v f


extractExpVars :: PreOpenExp arr env a -> Maybe (ExpVars env a)
extractExpVars Nil          = Just TupRunit
extractExpVars (Pair e1 e2) = TupRpair <$> extractExpVars e1 <*> extractExpVars e2
extractExpVars (Evar v)     = Just $ TupRsingle v
extractExpVars _            = Nothing
