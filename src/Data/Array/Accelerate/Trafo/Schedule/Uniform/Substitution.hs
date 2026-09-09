{-# LANGUAGE GADTs               #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# OPTIONS_HADDOCK hide #-}
-- |
-- Module      : Data.Array.Accelerate.Trafo.Schedule.Uniform
-- Copyright   : [2012..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.Trafo.Schedule.Uniform.Substitution (
  NewIdx(..), ReindexPartialN, SunkReindexPartialN(..),
  reindexArgs, reindexSchedule
) where

import Data.Array.Accelerate.AST.Environment
import Data.Array.Accelerate.AST.Idx
import Data.Array.Accelerate.AST.LeftHandSide
import Data.Array.Accelerate.AST.Schedule.Uniform
import Data.Array.Accelerate.Error
import Data.Array.Accelerate.Representation.Type
import Data.Array.Accelerate.Trafo.Exp.Substitution
import Data.Array.Accelerate.Trafo.Substitution
import Data.Maybe
import Prelude hiding (id, (.), read)
import Control.Category
import Data.Functor.Identity


instance Sink' (UniformSchedule kernel) where
  weaken' _ Return                        = Return
  weaken' k (Alet lhs b s)                
    | Exists lhs' <- rebuildLHS lhs   = Alet lhs' (weaken k b) (weaken' (sinkWithLHS lhs lhs' k) s)
  weaken' k (Effect effect s)         = Effect (weaken' k effect) (weaken' k s)
  weaken' k (Acond cond true false s) = Acond (weaken k cond) (weaken' k true) (weaken' k false) (weaken' k s)
  weaken' k (Awhile io f input s)     = Awhile io (weaken k f) (mapTupR (weaken k) input) (weaken' k s)
  weaken' k (AwhileSeq io f input s)  = AwhileSeq io (weaken k f) (mapTupR (weaken k) input) (weaken' k s)
  weaken' k (Spawn s1 s2)             = Spawn (weaken' k s1) (weaken' k s2)

instance Sink (UniformScheduleFun kernel) where
  weaken k (Slam lhs f)
    | Exists lhs' <- rebuildLHS lhs = Slam lhs' $ weaken (sinkWithLHS lhs lhs' k) f
  weaken k (Sbody s)    = Sbody $ weaken' k s

instance Sink Binding where
  weaken k (Compute e)       = Compute $ mapArrayInstr (weaken k) e
  weaken _ (NewSignal name)  = NewSignal name
  weaken _ (NewRef r)        = NewRef r
  weaken k (Alloc shr tp sz) = Alloc shr tp $ mapTupR (weaken k) sz
  weaken _ (Use tp n buffer) = Use tp n buffer
  weaken k (Unit var)        = Unit $ weaken k var
  weaken k (RefRead ref)     = RefRead $ weaken k ref

instance Sink' (Effect kernel) where
  weaken' k (Exec md kernel args) = Exec md kernel $ runIdentity $ reindexSArgs' (ReindexF $ \ix -> NewIdxJust <$> weakenReindex k ix) args
  weaken' k (SignalAwait vars) = SignalAwait $ map (weaken k) vars
  weaken' k (SignalResolve vars) = SignalResolve $ map (weaken k) vars
  weaken' k (RefWrite ref value) = RefWrite (weaken k ref) (weaken k value)
  weaken' k (Aassert msg cond) = Aassert msg $ mapArrayInstr (weaken k) cond
  weaken' k (Atrace msg t) = Atrace msg $ weakenArrayDescriptors k t

instance Sink SArg where
  weaken k = runIdentity . reindexSArg' (ReindexF $ \ix -> NewIdxJust <$> weakenReindex k ix)

type ReindexPartialN f env env' = forall a. Idx env a -> f (NewIdx env' a)

data NewIdx env t where
  NewIdxNoResolver :: NewIdx env SignalResolver
  NewIdxJust :: Idx env t -> NewIdx env t

data SunkReindexPartialN f env env' where
  Sink     :: SunkReindexPartialN f env env' -> SunkReindexPartialN f (env, s) (env', s)
  ReindexF :: ReindexPartialN f env env' -> SunkReindexPartialN f env env'


reindexSchedule :: (Applicative f) => ReindexPartialN f env env' -> UniformSchedule kernel env -> f (UniformSchedule kernel env')
reindexSchedule k = reindexSchedule' $ ReindexF k

sinkReindexWithLHS :: LeftHandSide s t env1 env1' -> LeftHandSide s t env2 env2' -> SunkReindexPartialN f env1 env2 -> SunkReindexPartialN f env1' env2'
sinkReindexWithLHS (LeftHandSideWildcard _) (LeftHandSideWildcard _) k = k
sinkReindexWithLHS (LeftHandSideSingle _)   (LeftHandSideSingle _)   k = Sink k
sinkReindexWithLHS (LeftHandSidePair a1 b1) (LeftHandSidePair a2 b2) k = sinkReindexWithLHS b1 b2 $ sinkReindexWithLHS a1 a2 k
sinkReindexWithLHS _ _ _ = internalError "sinkReindexWithLHS: left hand sides don't match"

reindex' :: Applicative f => SunkReindexPartialN f env env' -> ReindexPartialN f env env'
reindex' (ReindexF f) = f
reindex' (Sink k) = \case
  ZeroIdx    -> pure $ NewIdxJust ZeroIdx
  SuccIdx ix ->
    let
      f NewIdxNoResolver = NewIdxNoResolver
      f (NewIdxJust ix') = NewIdxJust $ SuccIdx ix'
    in
      f <$> reindex' k ix

reindexSchedule' :: (Applicative f) => SunkReindexPartialN f env env' -> UniformSchedule kernel env -> f (UniformSchedule kernel env')
reindexSchedule' k = \case
  Return -> pure Return
  Alet lhs bnd s
    | Exists lhs' <- rebuildLHS lhs -> Alet lhs' <$> reindexBinding' k bnd <*> reindexSchedule' (sinkReindexWithLHS lhs lhs' k) s
  Effect effect s -> Effect <$> reindexEffect' k effect <*> reindexSchedule' k s
  Acond cond t f continue -> Acond <$> reindexVarUnsafe k cond <*> reindexSchedule' k t <*> reindexSchedule' k f <*> reindexSchedule' k continue
  Awhile io f initial continue -> Awhile io <$> reindexScheduleFun' k f <*> traverseTupR (reindexVarUnsafe k) initial <*> reindexSchedule' k continue
  AwhileSeq io f initial continue -> AwhileSeq io <$> reindexScheduleFun' k f <*> traverseTupR (reindexVarUnsafe k) initial <*> reindexSchedule' k continue
  Spawn s1 s2 -> Spawn <$> reindexSchedule' k s1 <*> reindexSchedule' k s2

reindexVarUnsafe :: Applicative f => SunkReindexPartialN f env env' -> Var s env t -> f (Var s env' t)
reindexVarUnsafe k (Var tp idx) = Var tp . fromNewIdxUnsafe <$> reindex' k idx

reindexScheduleFun' :: (Applicative f) => SunkReindexPartialN f env env' -> UniformScheduleFun kernel env t -> f (UniformScheduleFun kernel env' t)
reindexScheduleFun' k = \case
  Sbody s -> Sbody <$> reindexSchedule' k s
  Slam lhs f
    | Exists lhs' <- rebuildLHS lhs -> Slam lhs' <$> reindexScheduleFun' (sinkReindexWithLHS lhs lhs' k) f

reindexEffect' :: forall kernel f env env'. (Applicative f) => SunkReindexPartialN f env env' -> Effect kernel env -> f (Effect kernel env')
reindexEffect' k = \case
  Exec md kernel args -> Exec md kernel <$> reindexSArgs' k args
  SignalAwait signals -> SignalAwait <$> traverse (fromNewIdxSignal <.> reindex' k) signals
  SignalResolve resolvers -> SignalResolve . mapMaybe toMaybe <$> traverse (reindex' k) resolvers
  RefWrite ref value -> RefWrite <$> reindexVar (fromNewIdxOutputRef <.> reindex' k) ref <*> reindexVar (fromNewIdxUnsafe <.> reindex' k) value
  Aassert msg cond -> Aassert msg <$> reindexExp (fromNewIdxUnsafe <.> reindex' k) cond
  Atrace msg t -> Atrace msg <$> reindexArrayDescriptors (fromNewIdxUnsafe <.> reindex' k) t
  where
    toMaybe :: NewIdx env' a -> Maybe (Idx env' a)
    toMaybe (NewIdxJust idx) = Just idx
    toMaybe _ = Nothing

reindexSArgs' :: Applicative f => SunkReindexPartialN f env env' -> SArgs env t -> f (SArgs env' t)
reindexSArgs' k = \case
  a :>: as -> (:>:) <$> reindexSArg' k a <*> reindexSArgs' k as
  ArgsNil  -> pure ArgsNil

reindexSArg' :: Applicative f => SunkReindexPartialN f env env' -> SArg env t -> f (SArg env' t)
reindexSArg' k = \case
  SArgScalar   var -> SArgScalar   <$> reindexVarUnsafe k var
  SArgBuffer m var -> SArgBuffer m <$> reindexVarUnsafe k var

-- For Exec we cannot have a safe function from the conversion,
-- as we cannot enforce in the type system that no SignalResolvers
-- occur in an Exec or Compute.
fromNewIdxUnsafe :: NewIdx env' a -> Idx env' a
fromNewIdxUnsafe (NewIdxJust idx) = idx
fromNewIdxUnsafe _ = error "Expected NewIdxJust"

-- Different versions, which have different ways of getting evidence
-- that NewIdxNoResolver is impossible
fromNewIdxSignal :: NewIdx env' Signal -> Idx env' Signal
fromNewIdxSignal (NewIdxJust idx) = idx

fromNewIdxOutputRef :: NewIdx env' (OutputRef t) -> Idx env' (OutputRef t)
fromNewIdxOutputRef (NewIdxJust idx) = idx

fromNewIdxGround :: GroundR a -> NewIdx env' a -> Idx env' a
fromNewIdxGround _  (NewIdxJust idx) = idx
fromNewIdxGround tp NewIdxNoResolver = signalResolverImpossible (TupRsingle tp)

reindexBinding' :: Applicative f => SunkReindexPartialN f env env' -> Binding env t -> f (Binding env' t)
reindexBinding' k = \case
  Compute e -> Compute <$> reindexExp (fromNewIdxUnsafe <.> reindex' k) e
  NewSignal name -> pure $ NewSignal name
  NewRef tp -> pure $ NewRef tp
  Alloc shr tp sh -> Alloc shr tp <$> reindexVars (fromNewIdxUnsafe <.> reindex' k) sh
  Use tp n buffer -> pure $ Use tp n buffer
  Unit (Var tp idx) -> Unit . Var tp <$> (fromNewIdxGround (GroundRscalar tp) <.> reindex' k) idx
  RefRead ref -> RefRead <$> reindexVar (fromNewIdxUnsafe <.> reindex' k) ref

(<.>) :: Applicative f => (b -> c) -> (a -> f b) -> a -> f c
(<.>) g h a = g <$> h a
