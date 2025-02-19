{-# LANGUAGE ConstraintKinds     #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE KindSignatures      #-}
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
-- Module      : Data.Array.Accelerate.Trafo.Substitution
-- Copyright   : [2012..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.Trafo.Substitution (

  -- ** Renaming & Substitution
  inline, inlineVars, compose,
  subTop, subAtop, apply1,

  -- ** Weakening
  (:>), Sink(..), Sink'(..), SinkExp(..), weakenVars, weakenArrayInstr,

  -- ** Strengthening
  (:?>), strengthen, strengthenE,

  -- ** Rebuilding terms
  RebuildAcc, Rebuildable(..), RebuildableAcc,
  RebuildableExp(..), rebuildWeakenVar, rebuildLHS,
  OpenAccFun(..), OpenAccExp(..),

  -- ** Checks
  isIdentity, isIdentityIndexing, extractExpVars,
  bindingIsTrivial,

) where

import Data.Array.Accelerate.AST
import Data.Array.Accelerate.AST.LeftHandSide
import Data.Array.Accelerate.AST.Var
import Data.Array.Accelerate.AST.Idx
import Data.Array.Accelerate.AST.Environment
import Data.Array.Accelerate.Analysis.Match
import Data.Array.Accelerate.Error
import Data.Array.Accelerate.Representation.Array
import Data.Array.Accelerate.Trafo.Exp.Substitution
import qualified Data.Array.Accelerate.Debug.Internal.Stats         as Stats

import Data.Kind
import Control.Applicative                                          hiding ( Const )
import Control.Monad
import Prelude                                                      hiding ( exp, seq )
import Data.Functor.Identity


-- NOTE: [Renaming and Substitution]
--
-- To do things like renaming and substitution, we need some operation on
-- variables that we push structurally through terms, applying to each variable.
-- We have a type preserving but environment changing operation:
--
--   v :: forall t. Idx env t -> f env' aenv t
--
-- The crafty bit is that 'f' might represent variables (for renaming) or terms
-- (for substitutions). The demonic forall, --- which is to say that the
-- quantifier is in a position which gives us obligation, not opportunity ---
-- forces us to respect type: when pattern matching detects the variable we care
-- about, happily we discover that it has the type we must respect. The demon is
-- not so free to mess with us as one might fear at first.
--
-- We then lift this to an operation which traverses terms and rebuild them
-- after applying 'v' to the variables:
--
--   rebuildPartial v :: OpenExp env aenv t -> OpenExp env' aenv t
--
-- The Syntactic class tells us what we need to know about 'f' if we want to be
-- able to rebuildPartial terms. In essence, the crucial functionality is to propagate
-- a class of operations on variables that is closed under shifting.
--

-- Detects whether the function is of the form \ix -> a ! ix
isIdentityIndexing :: OpenFun env aenv (a -> b) -> Maybe (ArrayVar aenv (Array a b))
isIdentityIndexing (Lam lhs (Body body))
  | ArrayInstr (Index avar) ix <- body
  , Just vars     <- extractExpVars ix
  , Just Refl     <- bindingIsTrivial lhs vars
  = Just avar
isIdentityIndexing _ = Nothing

subAtop :: PreOpenAcc acc aenv t -> ArrayVar (aenv, t) (Array sh2 e2) -> PreOpenAcc acc aenv (Array sh2 e2)
subAtop t (Var _    ZeroIdx      ) = t
subAtop _ (Var repr (SuccIdx idx)) = Avar $ Var repr idx

-- A class for rebuilding terms.
--
class Rebuildable f where
  {-# MINIMAL rebuildPartial #-}
  type AccClo f :: Type -> Type -> Type

  rebuildPartial :: (Applicative f', SyntacticAcc fa)
                 => (forall sh e. ArrayVar aenv (Array sh e) -> f' (fa (AccClo f) aenv' (Array sh e)))
                 -> f aenv  a
                 -> f' (f aenv' a)

  {-# INLINEABLE rebuildA #-}
  rebuildA :: (SyntacticAcc fa)
           => (forall sh e. ArrayVar aenv (Array sh e) -> fa (AccClo f) aenv' (Array sh e))
           -> f aenv  a
           -> f aenv' a
  rebuildA av = runIdentity . rebuildPartial (Identity . av)

-- Terms that are rebuildable and also recursive closures
--
type RebuildableAcc acc = (Rebuildable acc, AccClo acc ~ acc)

-- Wrappers which add the 'acc' type argument
--
data OpenAccExp (acc :: Type -> Type -> Type) env aenv a where
  OpenAccExp :: { unOpenAccExp :: OpenExp env aenv a } -> OpenAccExp acc env aenv a

data OpenAccFun (acc :: Type -> Type -> Type) env aenv a where
  OpenAccFun :: { unOpenAccFun :: OpenFun env aenv a } -> OpenAccFun acc env aenv a

-- We can use the same plumbing to rebuildPartial all the things we want to rebuild.
--
instance Rebuildable (OpenAccExp acc env) where
  type AccClo (OpenAccExp acc env) = acc
  {-# INLINEABLE rebuildPartial #-}
  rebuildPartial v (OpenAccExp e) = OpenAccExp <$> Stats.substitution "rebuild" (rebuildArrayInstrPartial (reindexArrayInstr v) e)

instance Rebuildable (OpenAccFun acc env) where
  type AccClo (OpenAccFun acc env) = acc
  {-# INLINEABLE rebuildPartial #-}
  rebuildPartial v (OpenAccFun f) = OpenAccFun <$> Stats.substitution "rebuild" (rebuildArrayInstrPartial (reindexArrayInstr v) f)

instance RebuildableAcc acc => Rebuildable (PreOpenAcc acc) where
  type AccClo (PreOpenAcc acc) = acc
  {-# INLINEABLE rebuildPartial #-}
  rebuildPartial x = Stats.substitution "rebuild" $ rebuildPreOpenAcc rebuildPartial x

instance RebuildableAcc acc => Rebuildable (PreOpenAfun acc) where
  type AccClo (PreOpenAfun acc) = acc
  {-# INLINEABLE rebuildPartial #-}
  rebuildPartial x = Stats.substitution "rebuild" $ rebuildAfun rebuildPartial x

instance Rebuildable OpenAcc where
  type AccClo OpenAcc = OpenAcc
  {-# INLINEABLE rebuildPartial #-}
  rebuildPartial x = Stats.substitution "rebuild" $ rebuildOpenAcc x

-- | Weakening
-- SEE: [Weakening]

class Sink f where
  weaken :: env :> env' -> forall t. f env t -> f env' t

  -- TLM: We can't use this default instance because it doesn't lead to
  --      specialised code. Perhaps the INLINEABLE pragma is ignored: GHC bug?
  --
  -- {-# INLINEABLE weaken #-}
  -- default weaken :: Rebuildable f => env :> env' -> f env t -> f env' t
  -- weaken k = Stats.substitution "weaken" . rebuildA rebuildWeakenVar

class Sink' f where
  weaken' :: env :> env' -> f env -> f env'

--instance Rebuildable f => Sink f where -- undecidable, incoherent
--  weaken k = Stats.substitution "weaken" . rebuildA rebuildWeakenVar

instance Sink Idx where
  {-# INLINEABLE weaken #-}
  weaken = (>:>)

instance Sink (Var s) where
  {-# INLINEABLE weaken #-}
  weaken k (Var s ix) = Var s (k >:> ix)

rebuildWeakenVar :: env :> env' -> ArrayVar env (Array sh e) -> PreOpenAcc acc env' (Array sh e)
rebuildWeakenVar k (Var s idx) = Avar $ Var s $ k >:> idx

instance RebuildableAcc acc => Sink (PreOpenAcc acc) where
  {-# INLINEABLE weaken #-}
  weaken k = Stats.substitution "weaken" . rebuildA (rebuildWeakenVar k)

instance RebuildableAcc acc => Sink (PreOpenAfun acc) where
  {-# INLINEABLE weaken #-}
  weaken k = Stats.substitution "weaken" . rebuildA (rebuildWeakenVar k)

-- We cannot use 'weaken' to weaken the array environment of an 'OpenExp',
-- as OpenExp is a type synonym for 'PreOpenExp (ArrayInstr aenv) env',
-- and 'weaken' would thus affect the expression environment. Hence we
-- have a separate function for OpenExp and OpenFun.
--
weakenArrayInstr :: RebuildableExp f => aenv :> aenv' -> f (ArrayInstr aenv) env t -> f (ArrayInstr aenv') env t
weakenArrayInstr k = Stats.substitution "weaken" . rebuildArrayInstr (ArrayInstr . weaken k)

{- 
instance Sink (OpenExp env) where
  {-# INLINEABLE weaken #-}
  weaken k = Stats.substitution "weaken" . runIdentity . rebuildOpenExp (Identity . Evar) (ReindexAvar (Identity . weaken k))

instance Sink (OpenFun env) where
  {-# INLINEABLE weaken #-}
  weaken k = Stats.substitution "weaken" . runIdentity . rebuildFun (Identity . Evar) (ReindexAvar (Identity . weaken k))
-}

instance Sink ArrayInstr where
  weaken k (Index       var) = Index       $ weaken k var
  weaken k (LinearIndex var) = LinearIndex $ weaken k var
  weaken k (Shape       var) = Shape       $ weaken k var

instance Sink Boundary where
  {-# INLINEABLE weaken #-}
  weaken k bndy =
    case bndy of
      Clamp      -> Clamp
      Mirror     -> Mirror
      Wrap       -> Wrap
      Constant c -> Constant c
      Function f -> Function (weakenArrayInstr k f)

instance Sink OpenAcc where
  {-# INLINEABLE weaken #-}
  weaken k = Stats.substitution "weaken" . rebuildA (rebuildWeakenVar k)

-- This rewrite rule is disabled because 'weaken' is now part of a type class.
-- As such, we cannot attach a NOINLINE pragma because it has many definitions.
-- {-# RULES
-- "weaken/weaken" forall a (v1 :: env' :> env'') (v2 :: env :> env').
--     weaken v1 (weaken v2 a) = weaken (v1 . v2) a
--  #-}


-- SEE: [Strengthening]
--

{-# INLINEABLE strengthen #-}
strengthen :: forall f env env' t. Rebuildable f => env :?> env' -> f env t -> Maybe (f env' t)
strengthen k x = Stats.substitution "strengthen" $ rebuildPartial @f @Maybe @IdxA (\(Var s ix) -> fmap (IA . Var s) $ k ix) x

-- Substitutions in array environment
-- ----------------------------------

type RebuildAcc acc =
  forall aenv aenv' f fa a. (HasCallStack, Applicative f, SyntacticAcc fa)
    => RebuildAvar f fa acc aenv aenv'
    -> acc aenv a
    -> f (acc aenv' a)

newtype IdxA (acc :: Type -> Type -> Type) aenv t = IA { unIA :: ArrayVar aenv t }

class SyntacticAcc f where
  avarIn        :: ArrayVar aenv (Array sh e) -> f acc aenv (Array sh e)
  accOut        :: f acc aenv (Array sh e) -> PreOpenAcc acc aenv (Array sh e)
  weakenAcc     :: RebuildAcc acc -> f acc aenv (Array sh e) -> f acc (aenv, s) (Array sh e)

instance SyntacticAcc IdxA where
  avarIn                       = IA
  accOut                       = Avar . unIA
  weakenAcc _ (IA (Var s idx)) = IA $ Var s $ SuccIdx idx

instance SyntacticAcc PreOpenAcc where
  avarIn        = Avar
  accOut        = id
  weakenAcc k   = runIdentity . rebuildPreOpenAcc k (Identity . weakenAcc k . IA)

type RebuildAvar f (fa :: (Type -> Type -> Type) -> Type -> Type -> Type) acc aenv aenv'
    = forall sh e. ArrayVar aenv (Array sh e) -> f (fa acc aenv' (Array sh e))


{-# INLINEABLE shiftA #-}
shiftA
    :: (HasCallStack, Applicative f, SyntacticAcc fa)
    => RebuildAcc acc
    -> RebuildAvar f fa acc aenv aenv'
    -> ArrayVar  (aenv,  s) (Array sh e)
    -> f (fa acc (aenv', s) (Array sh e))
shiftA _ _ (Var s ZeroIdx)      = pure $ avarIn $ Var s ZeroIdx
shiftA k v (Var s (SuccIdx ix)) = weakenAcc k <$> v (Var s ix)

shiftA'
    :: (HasCallStack, Applicative f, SyntacticAcc fa)
    => ALeftHandSide t aenv1 aenv1'
    -> ALeftHandSide t aenv2 aenv2'
    -> RebuildAcc acc
    -> RebuildAvar f fa acc aenv1  aenv2
    -> RebuildAvar f fa acc aenv1' aenv2'
shiftA' (LeftHandSideWildcard _) (LeftHandSideWildcard _) _ v = v
shiftA' (LeftHandSideSingle _)   (LeftHandSideSingle _)   k v = shiftA k v
shiftA' (LeftHandSidePair a1 b1) (LeftHandSidePair a2 b2) k v = shiftA' b1 b2 k $ shiftA' a1 a2 k v
shiftA' _ _ _ _ = internalError "left hand sides do not match"

{-# INLINEABLE rebuildOpenAcc #-}
rebuildOpenAcc
    :: (HasCallStack, Applicative f, SyntacticAcc fa)
    => (forall sh e. ArrayVar aenv (Array sh e) -> f (fa OpenAcc aenv' (Array sh e)))
    -> OpenAcc aenv  t
    -> f (OpenAcc aenv' t)
rebuildOpenAcc av (OpenAcc acc) = OpenAcc <$> rebuildPreOpenAcc rebuildOpenAcc av acc

{-# INLINEABLE rebuildPreOpenAcc #-}
rebuildPreOpenAcc
    :: forall f fa acc aenv aenv' t.
       (HasCallStack, Applicative f, SyntacticAcc fa)
    => RebuildAcc acc
    -> RebuildAvar f fa acc aenv aenv'
    -> PreOpenAcc acc aenv  t
    -> f (PreOpenAcc acc aenv' t)
rebuildPreOpenAcc k av acc =
  case acc of
    Use repr a                -> pure $ Use repr a
    Alet lhs a b              -> rebuildAlet k av lhs a b
    Avar ix                   -> accOut          <$> av ix
    Apair as bs               -> Apair           <$> k av as <*> k av bs
    Anil                      -> pure Anil
    Atrace msg as bs          -> Atrace msg      <$> k av as <*> k av bs
    Apply repr f a            -> Apply repr      <$> rebuildAfun k av f <*> k av a
    Acond p t e               -> Acond           <$> travE p <*> k av t <*> k av e
    Awhile p f a              -> Awhile          <$> rebuildAfun k av p <*> rebuildAfun k av f <*> k av a
    Unit tp e                 -> Unit tp         <$> travE e
    Reshape shr e a           -> Reshape shr     <$> travE e <*> k av a
    Generate repr e f         -> Generate repr   <$> travE e <*> travF f
    Transform repr sh ix f a  -> Transform repr  <$> travE sh <*> travF ix <*> travF f <*> k av a
    Replicate sl slix a       -> Replicate sl    <$> travE slix <*> k av a
    Slice sl a slix           -> Slice sl        <$> k av a <*> travE slix
    Map tp f a                -> Map tp          <$> travF f <*> k av a
    ZipWith tp f a1 a2        -> ZipWith tp      <$> travF f <*> k av a1 <*> k av a2
    Fold f z a                -> Fold            <$> travF f <*> travME z <*> k av a
    FoldSeg itp f z a s       -> FoldSeg itp     <$> travF f <*> travME z <*> k av a <*> k av s
    Scan  d f z a             -> Scan  d         <$> travF f <*> travME z <*> k av a
    Scan' d f z a             -> Scan' d         <$> travF f <*> travE z <*> k av a
    Permute f1 a1 a2          -> Permute         <$> travMF f1 <*> k av a1 <*> k av a2
    Backpermute shr sh f a    -> Backpermute shr <$> travE sh <*> travF f <*> k av a
    Stencil sr tp f b a       -> Stencil sr tp   <$> travF f <*> rebuildBoundary av b  <*> k av a
    Stencil2 s1 s2 tp f b1 a1 b2 a2
                              -> Stencil2 s1 s2 tp <$> travF f <*> rebuildBoundary av b1 <*> k av a1 <*> rebuildBoundary av b2 <*> k av a2
    Aforeign repr ff afun as  -> Aforeign repr ff afun <$> k av as
    -- Collect seq             -> Collect      <$> rebuildSeq k av seq
  where
    travE :: Exp aenv e -> f (Exp aenv' e)
    travE = rebuildArrayInstrPartial (reindexArrayInstr av)

    travME :: Maybe (Exp aenv e) -> f (Maybe (Exp aenv' e))
    travME Nothing  = pure Nothing
    travME (Just e) = Just <$> travE e

    travF :: Fun aenv e -> f (Fun aenv' e)
    travF = rebuildArrayInstrPartial (reindexArrayInstr av)

    travMF :: Maybe (Fun aenv e) -> f (Maybe (Fun aenv' e))
    travMF Nothing = pure Nothing
    travMF (Just x) = Just <$> travF x

{-# INLINEABLE rebuildAfun #-}
rebuildAfun
    :: (HasCallStack, Applicative f, SyntacticAcc fa)
    => RebuildAcc acc
    -> RebuildAvar f fa acc aenv aenv'
    -> PreOpenAfun acc aenv  t
    -> f (PreOpenAfun acc aenv' t)
rebuildAfun k av (Abody b) = Abody <$> k av b
rebuildAfun k av (Alam lhs1 f)
  | Exists lhs2 <- rebuildLHS lhs1
  = Alam lhs2 <$> rebuildAfun k (shiftA' lhs1 lhs2 k av) f

rebuildAlet
    :: forall f fa acc aenv1 aenv1' aenv2 bndArrs arrs. (HasCallStack, Applicative f, SyntacticAcc fa)
    => RebuildAcc acc
    -> RebuildAvar f fa acc aenv1 aenv2
    -> ALeftHandSide bndArrs aenv1 aenv1'
    -> acc aenv1  bndArrs
    -> acc aenv1' arrs
    -> f (PreOpenAcc acc aenv2 arrs)
rebuildAlet k av lhs1 bind1 body1
  | Exists lhs2 <- rebuildLHS lhs1
  = Alet lhs2 <$> k av bind1 <*> k (shiftA' lhs1 lhs2 k av) body1

{-# INLINEABLE rebuildBoundary #-}
rebuildBoundary
    :: (HasCallStack, Applicative f, SyntacticAcc fa)
    => RebuildAvar f fa acc aenv aenv'
    -> Boundary aenv t
    -> f (Boundary aenv' t)
rebuildBoundary av bndy =
  case bndy of
    Clamp       -> pure Clamp
    Mirror      -> pure Mirror
    Wrap        -> pure Wrap
    Constant v  -> pure (Constant v)
    Function f  -> Function <$> rebuildArrayInstrPartial (reindexArrayInstr av) f

reindexArrayInstr
    :: forall f fa acc aenv aenv'.
       (HasCallStack, Applicative f, SyntacticAcc fa)
    => RebuildAvar f fa acc aenv aenv'
    -> RebuildArrayInstr f (ArrayInstr aenv) (ArrayInstr aenv')
reindexArrayInstr av arr = case arr of
  Shape var       -> ArrayInstr . Shape       <$> reindex var
  Index var       -> ArrayInstr . Index       <$> reindex var
  LinearIndex var -> ArrayInstr . LinearIndex <$> reindex var
  where
    reindex :: forall sh e. ArrayVar aenv (Array sh e) -> f (ArrayVar aenv' (Array sh e))
    reindex var = g <$> av var

    g :: fa acc aenv' (Array sh e) -> ArrayVar aenv' (Array sh e)
    g fa = case accOut fa of
      Avar var' -> var'
      _ -> internalError "An Avar which was used in an Exp was mapped to an array term other than Avar. This mapping is invalid as an Exp can only contain array variables."

{--
{-# INLINEABLE rebuildSeq #-}
rebuildSeq
    :: (SyntacticAcc fa, Applicative f)
    => RebuildAcc acc
    -> RebuildAvar f fa acc aenv aenv'
    -> PreOpenSeq acc aenv senv t
    -> f (PreOpenSeq acc aenv' senv t)
rebuildSeq k v seq =
  case seq of
    Producer p s -> Producer <$> (rebuildP k v p) <*> (rebuildSeq k v s)
    Consumer c   -> Consumer <$> (rebuildC k v c)
    Reify ix     -> pure $ Reify ix

{-# INLINEABLE rebuildP #-}
rebuildP :: (SyntacticAcc fa, Applicative f)
         => RebuildAcc acc
         -> RebuildAvar f fa acc aenv aenv'
         -> Producer acc aenv senv a
         -> f (Producer acc aenv' senv a)
rebuildP k v p =
  case p of
    StreamIn arrs        -> pure (StreamIn arrs)
    ToSeq sl slix acc    -> ToSeq sl slix <$> k v acc
    MapSeq f x           -> MapSeq <$> rebuildAfun k v f <*> pure x
    ChunkedMapSeq f x    -> ChunkedMapSeq <$> rebuildAfun k v f <*> pure x
    ZipWithSeq f x y     -> ZipWithSeq <$> rebuildAfun k v f <*> pure x <*> pure y
    ScanSeq f e x        -> ScanSeq <$> rebuildFun (pure . IE) v f <*> rebuildOpenExp (pure . IE) v e <*> pure x

{-# INLINEABLE rebuildC #-}
rebuildC :: forall acc fa f aenv aenv' senv a. (SyntacticAcc fa, Applicative f)
         => RebuildAcc acc
         -> RebuildAvar f fa acc aenv aenv'
         -> Consumer acc aenv senv a
         -> f (Consumer acc aenv' senv a)
rebuildC k v c =
  case c of
    FoldSeq f e x          -> FoldSeq <$> rebuildFun (pure . IE) v f <*> rebuildOpenExp (pure . IE) v e <*> pure x
    FoldSeqFlatten f acc x -> FoldSeqFlatten <$> rebuildAfun k v f <*> k v acc <*> pure x
    Stuple t               -> Stuple <$> rebuildT t
  where
    rebuildT :: Atuple (Consumer acc aenv senv) t -> f (Atuple (Consumer acc aenv' senv) t)
    rebuildT NilAtup        = pure NilAtup
    rebuildT (SnocAtup t s) = SnocAtup <$> (rebuildT t) <*> (rebuildC k v s)
--}
