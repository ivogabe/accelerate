{-# LANGUAGE BangPatterns          #-}
{-# LANGUAGE CPP                   #-}
{-# LANGUAGE EmptyCase             #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE PatternSynonyms       #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TemplateHaskellQuotes #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE ViewPatterns          #-}
{-# OPTIONS_HADDOCK hide #-}
-- |
-- Module      : Data.Array.Accelerate.AST.Idx
-- Copyright   : [2008..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--
-- Typed de Bruijn indices
--

module Data.Array.Accelerate.AST.Idx (
  Idx(ZeroIdx, SuccIdx, VoidIdx),
  idxToInt,
  rnfIdx, liftIdx, matchIdx,

  PairIdx(..),

  Skip(SkipNone, SkipSucc, SkipSucc'), skipIdx, unskipIdx, chainSkip,

  Keep(KeepNone, KeepSucc), keepIdx, unkeepIdx, chainKeep,
) where

import Control.DeepSeq
import Language.Haskell.TH.Extra                                    hiding ( Type )
import Data.Type.Equality                                           ( (:~:)(Refl) )

#ifndef ACCELERATE_INTERNAL_CHECKS
import Data.Kind
import Unsafe.Coerce                                                ( unsafeCoerce )
#endif


#ifdef ACCELERATE_INTERNAL_CHECKS

-- | De Bruijn variable index projecting a specific type from a type
-- environment.  Type environments are nested pairs (..((), t1), t2, ..., tn).
--
data Idx env t where
  ZeroIdx ::              Idx (env, t) t
  SuccIdx :: Idx env t -> Idx (env, s) t

instance Eq (Idx env t) where
  ZeroIdx == ZeroIdx = True
  SuccIdx a == SuccIdx b = a == b
  _ == _ = False

instance Ord (Idx env t) where
  compare a b = compare (idxToInt a) (idxToInt b)

idxToInt :: Idx env t -> Int
idxToInt ZeroIdx       = 0
idxToInt (SuccIdx idx) = 1 + idxToInt idx

rnfIdx :: Idx env t -> ()
rnfIdx ZeroIdx      = ()
rnfIdx (SuccIdx ix) = rnfIdx ix

liftIdx :: Idx env t -> CodeQ (Idx env t)
liftIdx ZeroIdx      = [|| ZeroIdx ||]
liftIdx (SuccIdx ix) = [|| SuccIdx $$(liftIdx ix) ||]

{-# INLINEABLE matchIdx #-}
matchIdx :: Idx env s -> Idx env t -> Maybe (s :~: t)
matchIdx ZeroIdx     ZeroIdx     = Just Refl
matchIdx (SuccIdx u) (SuccIdx v) = matchIdx u v
matchIdx _           _           = Nothing

#else

-- | De Bruijn variable index projecting a specific type from a type
-- environment.  Type environments are nested pairs (..((), t1), t2, ..., tn).
--
-- Outside of this file, pretend that this is an ordinary GADT:
-- data Idx env t where
--   ZeroIdx ::              Idx (env, t) t
--   SuccIdx :: Idx env t -> Idx (env, s) t
--
-- For performance, it uses an Int under the hood.
--
newtype Idx :: Type -> Type -> Type where
  UnsafeIdxConstructor :: { unsafeRunIdx :: Int } -> Idx env t
  deriving (Eq, Ord)
{-# COMPLETE ZeroIdx, SuccIdx #-}

pattern ZeroIdx :: forall envt t. () => forall env. (envt ~ (env, t)) => Idx envt t
pattern ZeroIdx <- (\x -> (idxToInt x, unsafeCoerce Refl) -> (0, Refl :: envt :~: (env, t)))
  where
    ZeroIdx = UnsafeIdxConstructor 0

pattern SuccIdx :: forall envs t. () => forall s env. (envs ~ (env, s)) => Idx env t -> Idx envs t
pattern SuccIdx idx <- (unSucc -> Just (idx, Refl))
  where
    SuccIdx (UnsafeIdxConstructor i) = UnsafeIdxConstructor (i+1)

-- Note: env and s should actually not be universally quantified (forall),
-- so this function on its own is unsound. The integration in SuccIdx makes it
-- sound however.
unSucc :: Idx envs t -> Maybe (Idx env t, envs :~: (env, s))
unSucc (UnsafeIdxConstructor i)
  | i < 1     = Nothing
  | otherwise = Just (UnsafeIdxConstructor (i-1), unsafeCoerce Refl)

-- Note: this is a separate function instead of a field of Idx, since this function is exported.
-- If we would export a field of Idx, then it could unsafely be updated via
-- idx{ idxToInt = 2 }, breaking the "safe" abstraction of this module.
idxToInt :: Idx env t -> Int
idxToInt = unsafeRunIdx

rnfIdx :: Idx env t -> ()
rnfIdx !_ = ()

liftIdx :: Idx env t -> CodeQ (Idx env t)
liftIdx (UnsafeIdxConstructor i) = [|| UnsafeIdxConstructor i ||]

{-# INLINEABLE matchIdx #-}
matchIdx :: Idx env s -> Idx env t -> Maybe (s :~: t)
matchIdx (UnsafeIdxConstructor i) (UnsafeIdxConstructor j)
  | i == j = Just $ unsafeCoerce Refl
  | otherwise = Nothing
#endif

instance NFData (Idx env t) where
  rnf = rnfIdx

-- | Despite the 'complete' pragma above, GHC can't infer that there is no
-- pattern possible if the environment is empty. This can be used instead.
--
{-# COMPLETE VoidIdx #-}
pattern VoidIdx :: forall env t a. (env ~ ()) => () => a -> Idx env t
pattern VoidIdx a <- (\case{} -> a)

{-# COMPLETE VoidIdx #-}

data PairIdx p a where
  PairIdxLeft  :: PairIdx (a, b) a
  PairIdxRight :: PairIdx (a, b) b

-- Skip: a GADT to describe that we skip over a number of bindings in an
-- environment.
#ifdef ACCELERATE_INTERNAL_CHECKS

-- Drops some bindings of env' to result in env.
data Skip env env' where
  SkipSucc :: Skip env (env', t) -> Skip env env'
  SkipNone :: Skip env env

-- Historical context: we used to have two data types, Skip and Skip'.
-- Skip was constructed via:
-- SkipSucc :: Skip env (env', t) -> Skip env env'
-- and Skip' via:
-- SkipSucc' :: Skip env env' -> Skip (env, t) env'
-- Both data types have the same functionality, but different performance,
-- similar to the difference between cons- and snoc-lists.
-- Each analysis or transformation in the compiler would need to choose between
-- these two data types. 
-- To simplify this, we now only have Skip, and SkipSucc' is implemented as a
-- pattern synonym over Skip.

skipIdx :: Skip env env' -> Idx env t -> Maybe (Idx env' t)
skipIdx SkipNone     idx = Just idx
skipIdx (SkipSucc s) idx = case skipIdx s idx of
  Just (SuccIdx idx') -> Just idx'
  _                   -> Nothing

unskipIdx :: Skip env env' -> Idx env' t -> Idx env t
unskipIdx SkipNone     idx = idx
unskipIdx (SkipSucc s) idx = unskipIdx s $ SuccIdx idx

chainSkip :: Skip env1 env2 -> Skip env2 env3 -> Skip env1 env3
chainSkip skipL (SkipSucc skipR) = SkipSucc $ chainSkip skipL skipR
chainSkip skipL SkipNone         = skipL

skipSucc' :: Skip env env' -> Skip (env, t) env'
skipSucc' SkipNone = SkipSucc SkipNone
skipSucc' (SkipSucc s) = SkipSucc $ skipSucc' s

data UnSkipSucc' envt env' where
  UnSkipSucc' :: Skip env env' -> UnSkipSucc' (env, t) env'

unSkipSucc' :: Skip env env' -> Either (env :~: env') (UnSkipSucc' env env')
unSkipSucc' SkipNone = Left Refl
unSkipSucc' (SkipSucc s) = Right $ case unSkipSucc' s of
  Left Refl -> UnSkipSucc' SkipNone
  Right (UnSkipSucc' s') -> UnSkipSucc' $ SkipSucc s'

pattern SkipSucc' :: forall envt env'. () => forall t env. (envt ~ (env, t)) => Skip env env' -> Skip envt env'
pattern SkipSucc' s <- (unSkipSucc' -> Right (UnSkipSucc' s))
  where
    SkipSucc' s = skipSucc' s
{-# COMPLETE SkipNone, SkipSucc' #-}

#else

newtype Skip :: Type -> Type -> Type where
  UnsafeSkipConstructor :: { skipToInt :: Int } -> Skip env env'
{-# COMPLETE SkipNone, SkipSucc #-}
{-# COMPLETE SkipNone, SkipSucc' #-}

pattern SkipNone :: forall env env'. () => (env ~ env') => Skip env env'
pattern SkipNone <- (\x -> (skipToInt x, unsafeCoerce Refl) -> (0, Refl :: env :~: env'))
  where
    SkipNone = UnsafeSkipConstructor 0

skipIdx :: Skip env env' -> Idx env t -> Maybe (Idx env' t)
skipIdx skip idx
  | i >= 0 = Just $ UnsafeIdxConstructor i
  | otherwise = Nothing
  where
    i = idxToInt idx - skipToInt skip

unskipIdx :: Skip env env' -> Idx env' t -> Idx env t
unskipIdx skip idx = UnsafeIdxConstructor $ skipToInt skip + idxToInt idx

chainSkip :: Skip env1 env2 -> Skip env2 env3 -> Skip env1 env3
chainSkip skip1 skip2 = UnsafeSkipConstructor $ skipToInt skip1 + skipToInt skip2

data UnSkipSucc env env' where
  UnSkipSucc :: Skip env (env', t) -> UnSkipSucc env env'

unSkipSucc :: Skip env env' -> Maybe (UnSkipSucc env env')
unSkipSucc (UnsafeSkipConstructor 0) = Nothing
unSkipSucc (UnsafeSkipConstructor i)
  = unsafeCoerce $ Just $ UnSkipSucc $ UnsafeSkipConstructor $ i - 1

pattern SkipSucc :: forall env env'. () => forall t envt'. (envt' ~ (env', t)) => Skip env envt' -> Skip env env'
pattern SkipSucc s <- (unSkipSucc -> Just (UnSkipSucc s))
  where
    SkipSucc s = UnsafeSkipConstructor $ skipToInt s + 1

data UnSkipSucc' envt env' where
  UnSkipSucc' :: Skip env env' -> UnSkipSucc' (env, t) env'

unSkipSucc' :: Skip env env' -> Maybe (UnSkipSucc' env env')
unSkipSucc' (UnsafeSkipConstructor 0) = Nothing
unSkipSucc' (UnsafeSkipConstructor i)
  = unsafeCoerce $ Just $ UnSkipSucc' $ UnsafeSkipConstructor $ i - 1

pattern SkipSucc' :: forall envt env'. () => forall t env. (envt ~ (env, t)) => Skip env env' -> Skip envt env'
pattern SkipSucc' s <- (unSkipSucc' -> Just (UnSkipSucc' s))
  where
    SkipSucc' s = UnsafeSkipConstructor $ skipToInt s + 1

#endif

-- Keep: a GADT to describe that we preserve a number of bindings in an
-- environment.
-- The right-most n bindings of env1' and env2' are equal.
-- After dropping those bindings we get env1 and env2 respectively.
#ifdef ACCELERATE_INTERNAL_CHECKS

data Keep env1 env2 env1' env2' where
  KeepNone :: Keep env1 env2 env1 env2
  KeepSucc
    :: Keep env1 env2 env1' env2'
    -> Keep env1 env2 (env1', t) (env2', t)

keepIdx :: Keep env1 env2 env1' env2' -> Idx env1' t -> Either (Idx env1 t) (Idx env2' t)
keepIdx KeepNone idx = Left idx
keepIdx (KeepSucc _) ZeroIdx = Right ZeroIdx
keepIdx (KeepSucc k) (SuccIdx idx) = SuccIdx <$> keepIdx k idx

unkeepIdx :: Keep env1 env2 env1' env2' -> Idx env2 t -> Idx env2' t
unkeepIdx KeepNone idx = idx
unkeepIdx (KeepSucc k) idx = SuccIdx $ unkeepIdx k idx

chainKeep :: Keep env1 env2 env1' env2' -> Keep env1' env2' env1'' env2'' -> Keep env1 env2 env1'' env2''
chainKeep keepL KeepNone = keepL
chainKeep keepL (KeepSucc keepR) = KeepSucc $ chainKeep keepL keepR

#else

newtype Keep :: Type -> Type -> Type -> Type -> Type where
  UnsafeKeepConstructor :: { keepToInt :: Int } -> Keep env1 env2 env1' env2'
{-# COMPLETE KeepNone, KeepSucc #-}

pattern KeepNone :: forall env1 env2 env1' env2'. () => (env1 ~ env1', env2 ~ env2') => Keep env1 env2 env1' env2'
pattern KeepNone <- (\x -> (keepToInt x, unsafeCoerce Refl) -> (0, Refl :: (env1, env2) :~: (env1', env2')))
  where
    KeepNone = UnsafeKeepConstructor 0

data UnKeepSucc env1 env2 env1t' env2t' where
  UnKeepSucc :: Keep env1 env2 env1' env2' -> UnKeepSucc env1 env2 (env1', t) (env2', t)

unKeepSucc :: Keep env1 env2 env1t' env2t' -> Maybe (UnKeepSucc env1 env2 env1t' env2t')
unKeepSucc (UnsafeKeepConstructor 0) = Nothing
unKeepSucc (UnsafeKeepConstructor i)
  = unsafeCoerce $ Just $ UnKeepSucc $ UnsafeKeepConstructor $ i - 1

pattern KeepSucc :: forall env1 env2 env1t' env2t'. () => forall env1' env2' t. (env1t' ~ (env1', t), env2t' ~ (env2', t)) => Keep env1 env2 env1' env2' -> Keep env1 env2 env1t' env2t'
pattern KeepSucc k <- (unKeepSucc -> Just (UnKeepSucc k))
  where
    KeepSucc k = UnsafeKeepConstructor $ keepToInt k + 1

keepIdx :: Keep env1 env2 env1' env2' -> Idx env1' t -> Either (Idx env1 t) (Idx env2' t)
keepIdx k idx
  | i >= 0 = Left $ UnsafeIdxConstructor i
  | otherwise = Right $ UnsafeIdxConstructor $ idxToInt idx
  where
    i = idxToInt idx - keepToInt k

unkeepIdx :: Keep env1 env2 env1' env2' -> Idx env2 t -> Idx env2' t
unkeepIdx k idx = UnsafeIdxConstructor $ idxToInt idx + keepToInt k

chainKeep :: Keep env1 env2 env1' env2' -> Keep env1' env2' env1'' env2'' -> Keep env1 env2 env1'' env2''
chainKeep keep1 keep2 = UnsafeKeepConstructor $ keepToInt keep1 + keepToInt keep2

#endif
