{-# LANGUAGE ConstraintKinds     #-}
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
{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# OPTIONS_HADDOCK hide #-}
-- |
-- Module      : Data.Array.Accelerate.Trafo.Operation.Substitution
-- Copyright   : [2012..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.Trafo.Operation.Substitution (
  Sink(..), Sink'(..),
  reindexPartial,
  reindexPartialAfun,
  pair, pair', pairUnique, alet, aletUnique, alet',
  weakenArrayInstr,
  strengthenArrayInstr,
  extractParams,

  reindexVar, reindexVars,
  mkLHS, LHS(..),
  ) where

import Data.Array.Accelerate.AST.Idx
import Data.Array.Accelerate.AST.Var
import Data.Array.Accelerate.AST.LeftHandSide
import Data.Array.Accelerate.AST.Operation
import Data.Array.Accelerate.AST.Environment
import Data.Array.Accelerate.Representation.Type
import Data.Array.Accelerate.Trafo.Var
import Data.Array.Accelerate.Trafo.Substitution       (Sink(..), Sink'(..))
import Data.Array.Accelerate.Trafo.Exp.Substitution
import Data.Functor.Identity

data SunkReindexPartial f env env' where
  Sink     :: SunkReindexPartial f env env' -> SunkReindexPartial f (env, s) (env', s)
  ReindexF :: ReindexPartial f env env' -> SunkReindexPartial f env env'

reindexPartial :: (Applicative f) => ReindexPartial f env env' -> PreOpenAcc op env t -> f (PreOpenAcc op env' t)
reindexPartial k = reindexA' (ReindexF k)

reindexPartialAfun :: (Applicative f) => ReindexPartial f env env' -> PreOpenAfun op env t -> f (PreOpenAfun op env' t)
reindexPartialAfun k = reindexAfun' (ReindexF k)

instance Sink (PreOpenAcc op) where
  weaken k = runIdentity . reindexPartial (Identity . (k >:>))

instance Sink (PreOpenAfun op) where
  weaken k = runIdentity . reindexPartialAfun (Identity . (k >:>))

instance Sink Arg where
  weaken k = runIdentity . reindexArg (weakenReindex k)

instance Sink ArrayInstr where
  weaken k (Index     v) = Index     $ weaken k v
  weaken k (Parameter v) = Parameter $ weaken k v

sinkReindexWithLHS :: LeftHandSide s t env1 env1' -> LeftHandSide s t env2 env2' -> SunkReindexPartial f env1 env2 -> SunkReindexPartial f env1' env2'
sinkReindexWithLHS (LeftHandSideWildcard _) (LeftHandSideWildcard _) k = k
sinkReindexWithLHS (LeftHandSideSingle _)   (LeftHandSideSingle _)   k = Sink k
sinkReindexWithLHS (LeftHandSidePair a1 b1) (LeftHandSidePair a2 b2) k = sinkReindexWithLHS b1 b2 $ sinkReindexWithLHS a1 a2 k
sinkReindexWithLHS _ _ _ = error "sinkReindexWithLHS: left hand sides don't match"

-- All functions ending in a prime work with SunkReindexPartial instead of ReindexPartial.
reindex' :: Applicative f => SunkReindexPartial f env env' -> ReindexPartial f env env'
reindex' (ReindexF f) = f
reindex' (Sink k) = \case
  ZeroIdx    -> pure ZeroIdx
  SuccIdx ix -> SuccIdx <$> reindex' k ix

reindexVar' :: Applicative f => SunkReindexPartial f env env' -> Var s env t -> f (Var s env' t)
reindexVar' k (Var repr ix) = Var repr <$> reindex' k ix

reindexVars' :: Applicative f => SunkReindexPartial f env env' -> Vars s env t -> f (Vars s env' t)
reindexVars' _ TupRunit = pure $ TupRunit
reindexVars' k (TupRsingle var) = TupRsingle <$> reindexVar' k var
reindexVars' k (TupRpair v1 v2) = TupRpair <$> reindexVars' k v1 <*> reindexVars' k v2

reindexArrayInstr' :: Applicative f => SunkReindexPartial f env env' -> ArrayInstr env (s -> t) -> f (ArrayInstr env' (s -> t))
reindexArrayInstr' k (Index     v) = Index     <$> reindexVar' k v
reindexArrayInstr' k (Parameter v) = Parameter <$> reindexVar' k v

reindexExp' :: (Applicative f, RebuildableExp e) => SunkReindexPartial f benv benv' -> e (ArrayInstr benv) env t -> f (e (ArrayInstr benv') env t)
reindexExp' k = rebuildArrayInstrPartial (rebuildArrayInstrMap $ reindexArrayInstr' k)

reindexA' :: forall op f env env' t. (Applicative f) => SunkReindexPartial f env env' -> PreOpenAcc op env t -> f (PreOpenAcc op env' t)
reindexA' k = \case
    Exec op args -> Exec op <$> reindexArgs (reindex' k) args
    Return vars -> Return <$> reindexVars' k vars
    Compute e -> Compute <$> reindexExp' k e
    Alet lhs uniqueness bnd body
      | Exists lhs' <- rebuildLHS lhs -> Alet lhs' uniqueness <$> travA bnd <*> reindexA' (sinkReindexWithLHS lhs lhs' k) body
    Alloc shr tp sh -> Alloc shr tp <$> reindexVars' k sh
    Use tp n buffer -> pure $ Use tp n buffer
    Unit var -> Unit <$> reindexVar' k var
    Acond c t f -> Acond <$> reindexVar' k c <*> travA t <*> travA f
    Awhile uniqueness c f i -> Awhile uniqueness <$> reindexAfun' k c <*> reindexAfun' k f <*> reindexVars' k i
  where
    travA :: PreOpenAcc op env s -> f (PreOpenAcc op env' s)
    travA = reindexA' k

reindexAfun' :: (Applicative f) => SunkReindexPartial f env env' -> PreOpenAfun op env t -> f (PreOpenAfun op env' t)
reindexAfun' k (Alam lhs f)
  | Exists lhs' <- rebuildLHS lhs = Alam lhs' <$> reindexAfun' (sinkReindexWithLHS lhs lhs' k) f
reindexAfun' k (Abody a) = Abody <$> reindexA' k a

pair :: forall op env a b. PreOpenAcc op env a -> PreOpenAcc op env b -> PreOpenAcc op env (a, b)
pair = pair' False

pairUnique :: forall op env a b. PreOpenAcc op env a -> PreOpenAcc op env b -> PreOpenAcc op env (a, b)
pairUnique = pair' True

pair' :: forall op env a b. Bool -> PreOpenAcc op env a -> PreOpenAcc op env b -> PreOpenAcc op env (a, b)
pair' u a b = goA weakenId a
  where
    -- Traverse 'a' and look for a return. We can jump over let bindings
    -- If we don't find a 'return', we must first bind the value in a let,
    -- and then use the newly defined variables instead.
    --
    goA :: env :> env' -> PreOpenAcc op env' a -> PreOpenAcc op env' (a, b)
    goA k (Alet lhs uniqueness bnd x) 
                           = Alet lhs uniqueness bnd $ goA (weakenWithLHS lhs .> k) x
    goA k (Return vars)    = goB vars $ weaken k b
    goA k acc
      | DeclareVars lhs k' value <- declareVars $ groundsR acc
                           = Alet lhs ((if u then unique else shared) $ groundsR acc) acc $ goB (value weakenId) $ weaken (k' .> k) b

    goB :: GroundVars env' a -> PreOpenAcc op env' b -> PreOpenAcc op env' (a, b)
    goB varsA (Alet lhs uniqueness bnd x)
                               = Alet lhs uniqueness bnd $ goB (weakenVars (weakenWithLHS lhs) varsA) x
    goB varsA (Return varsB)   = Return (TupRpair varsA varsB)
    goB varsA acc
      | DeclareVars lhs k value <- declareVars $ groundsR b
                               = Alet lhs ((if u then unique else shared) $ groundsR b) acc $ Return (TupRpair (weakenVars k varsA) (value weakenId))

alet :: GLeftHandSide t env env' -> PreOpenAcc op env t -> PreOpenAcc op env' s -> PreOpenAcc op env s
alet lhs = alet' lhs $ shared $ lhsToTupR lhs

aletUnique :: GLeftHandSide t env env' -> PreOpenAcc op env t -> PreOpenAcc op env' s -> PreOpenAcc op env s
aletUnique lhs = alet' lhs $ unique $ lhsToTupR lhs

alet' :: GLeftHandSide t env env' -> Uniquenesses t -> PreOpenAcc op env t -> PreOpenAcc op env' s -> PreOpenAcc op env s
alet' lhs1 us (Alet lhs2 uniqueness a1 a2) a3
  | Exists lhs1' <- rebuildLHS lhs1 = Alet lhs2 uniqueness a1 $ alet' lhs1' us a2 $ weaken (sinkWithLHS lhs1 lhs1' $ weakenWithLHS lhs2) a3
alet' lhs@(LeftHandSideWildcard TupRunit) _ bnd a = case bnd of
  Compute _ -> a
  Return _  -> a
  Alloc{}   -> a
  Use{}     -> a
  Unit _    -> a
  _ -> Alet lhs TupRunit bnd a -- 'bnd' may have side effects
alet' lhs@(LeftHandSideWildcard TupRunit) _ bnd a = Alet lhs TupRunit bnd a
alet' lhs _ (Return vars)      a = weaken (substituteLHS lhs vars) a
alet' lhs us (Compute e)       a
  | Just vars <- extractParams e = weaken (substituteLHS lhs vars) a
  | LeftHandSidePair l1 l2 <- lhs
  , TupRpair u1 u2 <- us
  , Pair e1 e2 <- e = alet' l1 u1 (Compute e1) $ alet' l2 u2 (weaken (weakenWithLHS l1) $ Compute e2) a
alet' lhs us bnd               a = Alet lhs us bnd a

extractParams :: OpenExp env benv t -> Maybe (ExpVars benv t)
extractParams Nil                          = Just TupRunit
extractParams (Pair e1 e2)                 = TupRpair <$> extractParams e1 <*> extractParams e2
extractParams (ArrayInstr (Parameter v) _) = Just $ TupRsingle v
extractParams _                            = Nothing

-- We cannot use 'weaken' to weaken the array environment of an 'OpenExp',
-- as OpenExp is a type synonym for 'PreOpenExp (ArrayInstr aenv) env',
-- and 'weaken' would thus affect the expression environment. Hence we
-- have a separate function for OpenExp and OpenFun.
--
weakenArrayInstr :: RebuildableExp f => aenv :> aenv' -> f (ArrayInstr aenv) env t -> f (ArrayInstr aenv') env t
weakenArrayInstr k = rebuildArrayInstr (ArrayInstr . weaken k)

strengthenArrayInstr :: forall f benv benv' env t. RebuildableExp f => benv :?> benv' -> f (ArrayInstr benv) env t -> Maybe (f (ArrayInstr benv') env t)
strengthenArrayInstr k = rebuildArrayInstrPartial f
  where
    f :: ArrayInstr benv (u -> s) -> Maybe (OpenExp env' benv' u -> OpenExp env' benv' s)
    f (Parameter (Var tp ix)) = ArrayInstr . Parameter . Var tp <$> k ix
    f (Index     (Var tp ix)) = ArrayInstr . Index     . Var tp <$> k ix


data LHS s v env where
  LHS :: LeftHandSide s v env env'
      -> Vars s env' v
      -> LHS s v env

mkLHS :: TupR s v -> LHS s v env
mkLHS TupRunit = LHS LeftHandSideUnit TupRunit
mkLHS (TupRsingle x) = LHS (LeftHandSideSingle x) (TupRsingle $ Var x ZeroIdx)
mkLHS (TupRpair x y) = case mkLHS x of
  LHS lhsL varsL -> case mkLHS y of
    LHS lhsR varsR -> LHS (LeftHandSidePair lhsL lhsR) (TupRpair (weakenVars (weakenWithLHS lhsR) varsL) varsR)
