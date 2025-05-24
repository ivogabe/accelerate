{-# LANGUAGE GADTs               #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}
{-# OPTIONS_HADDOCK hide #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TupleSections #-}
-- |
-- Module      : Data.Array.Accelerate.AST.Environment
-- Copyright   : [2008..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.AST.Environment (
  Env(.., Push'), PartialEnv(..), Val, IdentityF(..),
  push, push', prj, prj', prjVars, prjPartial,
  unionPartialEnv, EnvBinding(..), partialEnvFromList, mapPartialEnv,
  mapMaybePartialEnv, partialEnvValues, diffPartialEnv, diffPartialEnvWith,
  intersectPartialEnv, partialEnvTail, partialEnvLast, partialEnvSkip,
  partialUpdate, partialRemove, partialEnvToList, partialEnvSingleton, partialEnvPush,
  partialEnvPushLHS, partialEnvSameKeys, partialEnvSub, partialEnvSkipLHS,
  envToPartial, envFromPartialLazy,

  Skip(..), skipIdx, chainSkip, skipWeakenIdx, lhsSkip,

  prjUpdate', prjReplace', update', updates', mapEnv,
  (:>)(..), weakenId, weakenSucc, weakenSucc', weakenEmpty, weakenReplace,
  sink, (.>), sinkWithLHS, weakenWithLHS, substituteLHS,
  varsGet, varsGetVal, stripWithLhs,weakenKeep) where

import Data.Array.Accelerate.AST.Idx
import Data.Array.Accelerate.AST.Var
import Data.Array.Accelerate.AST.LeftHandSide
import Data.Array.Accelerate.Error
import Data.Array.Accelerate.Representation.Type
import Data.Typeable                                ((:~:)(..))
import Data.Either
import Data.List ( sortOn )
import Data.Functor.Identity
import Data.Kind (Type)
import Data.String ( fromString )

-- Valuation for an environment
--
data Env f env where
  Empty :: Env f ()
  Push  :: Env f env -> f t -> Env f (env, t)

data PartialEnv f env where
  PEnd  :: PartialEnv f env
  PPush :: PartialEnv f env -> f t -> PartialEnv f (env, t)
  PNone :: PartialEnv f env ->        PartialEnv f (env, t)

type Val = Env Identity

pattern Push' :: () => (env' ~ (env, t)) => Val env -> t -> Val env'
pattern Push' env t = Push env (Identity t)
{-# COMPLETE Empty, Push' #-}

-- Push a set of variables into an environment
--
push :: Val env -> (LeftHandSide s t env env', t) -> Val env'
push env (LeftHandSideWildcard _, _     ) = env
push env (LeftHandSideSingle _  , a     ) = env `Push` Identity a
push env (LeftHandSidePair l1 l2, (a, b)) = push env (l1, a) `push` (l2, b)

push' :: forall f s t env env'. Distributes s => Env f env -> (LeftHandSide s t env env', Distribute f t) -> Env f env'
push' env (LeftHandSideWildcard _, _     ) = env
push' env (LeftHandSidePair l1 l2, (a, b)) = push' env (l1, a) `push'` (l2, b)
push' env (LeftHandSideSingle s  , a     )
  | Refl <- reprIsSingle @s @t @f s        = env `Push` a

-- Projection of a value from a valuation using a de Bruijn index
--
prj :: Idx env t -> Val env -> t
prj ix v = runIdentity $ prj' ix v

prj' :: Idx env t -> Env f env -> f t
prj' ZeroIdx       (Push _   v) = v
prj' (SuccIdx idx) (Push env _) = prj' idx env

prjVars :: forall f s t env. Distributes s => Vars s env t -> Env f env -> Distribute f t
prjVars (TupRpair v1 v2) env = (prjVars v1 env, prjVars v2 env)
prjVars TupRunit         _   = ()
prjVars (TupRsingle var) env
  | Refl <- reprIsSingle @s @t @f (varType var) = prj' (varIdx var) env

prjPartial :: Idx env t -> PartialEnv f env -> Maybe (f t)
prjPartial ZeroIdx       (PPush _   v) = Just v
prjPartial (SuccIdx idx) (PPush env _) = prjPartial idx env
prjPartial (SuccIdx idx) (PNone env)   = prjPartial idx env
prjPartial _             _             = Nothing

unionPartialEnv :: (forall t. f t -> f t -> f t) -> PartialEnv f env -> PartialEnv f env -> PartialEnv f env
unionPartialEnv _ PEnd         env          = env
unionPartialEnv _ env          PEnd         = env
unionPartialEnv g (PNone e1  ) (PNone e2  ) = PNone (unionPartialEnv g e1 e2)
unionPartialEnv g (PPush e1 a) (PNone e2  ) = PPush (unionPartialEnv g e1 e2) a
unionPartialEnv g (PNone e1  ) (PPush e2 b) = PPush (unionPartialEnv g e1 e2) b
unionPartialEnv g (PPush e1 a) (PPush e2 b) = PPush (unionPartialEnv g e1 e2) (g a b)

intersectPartialEnv :: (forall t. f t -> g t -> h t) -> PartialEnv f env -> PartialEnv g env -> PartialEnv h env
intersectPartialEnv _ PEnd _ = PEnd
intersectPartialEnv _ _ PEnd = PEnd
intersectPartialEnv g (PNone e1  ) (PNone e2  ) = PNone (intersectPartialEnv g e1 e2)
intersectPartialEnv g (PPush e1 _) (PNone e2  ) = PNone (intersectPartialEnv g e1 e2)
intersectPartialEnv g (PNone e1  ) (PPush e2 _) = PNone (intersectPartialEnv g e1 e2)
intersectPartialEnv g (PPush e1 a) (PPush e2 b) = PPush (intersectPartialEnv g e1 e2) (g a b)

-- Creates a partial environment containing only the identifiers which where
-- present in the first env but not in the second env.
diffPartialEnv :: PartialEnv f env -> PartialEnv g env -> PartialEnv f env
diffPartialEnv = diffPartialEnvWith (const $ const Nothing)

diffPartialEnvWith :: (forall t. f t -> g t -> Maybe (f t)) -> PartialEnv f env -> PartialEnv g env -> PartialEnv f env
diffPartialEnvWith _ PEnd         _            = PEnd
diffPartialEnvWith _ env          PEnd         = env
diffPartialEnvWith g (PNone e1  ) (PNone e2  ) = PNone (diffPartialEnvWith g e1 e2)
diffPartialEnvWith g (PNone e1  ) (PPush e2 _) = PNone (diffPartialEnvWith g e1 e2)
diffPartialEnvWith g (PPush e1 a) (PNone e2  ) = PPush (diffPartialEnvWith g e1 e2) a
diffPartialEnvWith g (PPush e1 a) (PPush e2 b) = case g a b of
  Nothing -> PNone (diffPartialEnvWith g e1 e2)
  Just x  -> PPush (diffPartialEnvWith g e1 e2) x

partialEnvTail :: PartialEnv f (env, t) -> PartialEnv f env
partialEnvTail (PPush e _) = e
partialEnvTail (PNone e  ) = e
partialEnvTail PEnd        = PEnd

partialEnvLast :: PartialEnv f (env, t) -> Maybe (f t)
partialEnvLast (PPush _ a) = Just a
partialEnvLast _           = Nothing

partialEnvSkip :: PartialEnv f env -> PartialEnv f (env, t)
partialEnvSkip PEnd = PEnd
partialEnvSkip e = PNone e

partialEnvSkipLHS :: LeftHandSide s t env env' -> PartialEnv f env -> PartialEnv f env'
partialEnvSkipLHS (LeftHandSideSingle _)   = partialEnvSkip
partialEnvSkipLHS (LeftHandSideWildcard _) = id
partialEnvSkipLHS (LeftHandSidePair l1 l2) = partialEnvSkipLHS l2 . partialEnvSkipLHS l1

partialEnvPush :: PartialEnv f env -> Maybe (f t) -> PartialEnv f (env, t)
partialEnvPush e Nothing  = PNone e
partialEnvPush e (Just a) = PPush e a

partialEnvPushLHS :: LeftHandSide s t env env' -> TupR f t -> PartialEnv f env -> PartialEnv f env'
partialEnvPushLHS (LeftHandSideSingle _) (TupRsingle a) env = PPush env a
partialEnvPushLHS (LeftHandSideWildcard _) _ env = env
partialEnvPushLHS (LeftHandSidePair l1 l2) (TupRpair a1 a2) env =
  partialEnvPushLHS l2 a2 $ partialEnvPushLHS l1 a1 env
partialEnvPushLHS _ _ _ = internalError "Tuple mismatch"

partialUpdate :: f t -> Idx env t -> PartialEnv f env -> PartialEnv f env
partialUpdate v ZeroIdx       env         = PPush (partialEnvTail env) v
partialUpdate v (SuccIdx idx) (PPush e a) = PPush (partialUpdate v idx e) a
partialUpdate v (SuccIdx idx) (PNone e  ) = PNone (partialUpdate v idx e)
partialUpdate v (SuccIdx idx) PEnd        = PNone (partialUpdate v idx PEnd)

partialRemove :: Idx env t -> PartialEnv f env -> PartialEnv f env
partialRemove ZeroIdx       env         = partialEnvSkip $ partialEnvTail env
partialRemove (SuccIdx idx) (PPush e a) = PPush (partialRemove idx e) a
partialRemove (SuccIdx idx) (PNone e  ) = PNone (partialRemove idx e)
partialRemove (SuccIdx _  ) PEnd        = PEnd

partialEnvSameKeys :: PartialEnv f env -> PartialEnv g env -> Bool
partialEnvSameKeys PEnd        PEnd        = True
partialEnvSameKeys (PPush a _) (PPush b _) = partialEnvSameKeys a b
partialEnvSameKeys (PNone a  ) (PNone b  ) = partialEnvSameKeys a b
partialEnvSameKeys (PNone a  ) PEnd        = partialEnvSameKeys a PEnd
partialEnvSameKeys PEnd        (PNone b  ) = partialEnvSameKeys PEnd b
partialEnvSameKeys _           _           = False

partialEnvSub :: PartialEnv f env -> PartialEnv g env -> Bool
partialEnvSub (PPush a _) (PPush b _) = partialEnvSub a b
partialEnvSub (PNone a)   b           = partialEnvSub a $ partialEnvTail b
partialEnvSub PEnd        _           = True
partialEnvSub _           _           = False

-- TODO: This is actually isomorphic to Var. Should we remove this data type?
data EnvBinding f env where
  EnvBinding :: Idx env t -> f t -> EnvBinding f env

partialEnvFromList :: forall f env. (forall t. f t -> f t -> f t) -> [EnvBinding f env] -> PartialEnv f env
-- Pair with ints to make sorting faster.
partialEnvFromList g = go SkipNone . map snd . sortOn fst . map (\b@(EnvBinding ix _) -> (idxToInt ix, b))
  where
    go :: Skip env env' -> [EnvBinding f env] -> PartialEnv f env'
    go _    [] = PEnd
    go skip (EnvBinding idx v : bs) = go' skip (EnvBinding idx' v) bs
      where
        idx' = case skipIdx skip idx of
          Just i  -> i
          Nothing -> error "List wasn't sorted properly"

    go' :: Skip env env' -> EnvBinding f env' -> [EnvBinding f env] -> PartialEnv f env'
    go' skip (EnvBinding (SuccIdx idx) v) bs = PNone $ go' (SkipSucc skip) (EnvBinding idx v) bs
    go' skip (EnvBinding ZeroIdx v)       bs = go'' skip v bs

    go'' :: Skip env (env', t) -> f t -> [EnvBinding f env] -> PartialEnv f (env', t)
    go'' _    v [] = PPush PEnd v
    go'' skip v (EnvBinding idx v' : bs) = case skipIdx skip idx of
      Nothing -> error "List wasn't sorted properly"
      Just ZeroIdx        -> go'' skip (g v v') bs
      Just (SuccIdx idx') -> PPush (go' (SkipSucc skip) (EnvBinding idx' v') bs) v

partialEnvToList :: forall f env. PartialEnv f env -> [EnvBinding f env]
partialEnvToList = go weakenId
  where
    go :: env' :> env -> PartialEnv f env' -> [EnvBinding f env]
    go _ PEnd = []
    go k (PNone env)   = go (weakenSucc k) env
    go k (PPush env a) = EnvBinding (k >:> ZeroIdx) a : go (weakenSucc k) env

mapPartialEnv :: (forall t. a t -> b t) -> PartialEnv a env -> PartialEnv b env
mapPartialEnv _ PEnd          = PEnd
mapPartialEnv f (PPush env a) = PPush (mapPartialEnv f env) (f a)
mapPartialEnv f (PNone env)   = PNone (mapPartialEnv f env)

mapMaybePartialEnv :: (forall t. a t -> Maybe (b t)) -> PartialEnv a env -> PartialEnv b env
mapMaybePartialEnv _ PEnd          = PEnd
mapMaybePartialEnv f (PPush env a) = case f a of
  Nothing -> PNone (mapMaybePartialEnv f env)
  Just b  -> PPush (mapMaybePartialEnv f env) b
mapMaybePartialEnv f (PNone env)   = PNone (mapMaybePartialEnv f env)

partialEnvValues :: PartialEnv (IdentityF a) env -> [a]
partialEnvValues PEnd                      = []
partialEnvValues (PNone env)               =     partialEnvValues env
partialEnvValues (PPush env (IdentityF a)) = a : partialEnvValues env

partialEnvSingleton :: Idx env t -> f t -> PartialEnv f env
partialEnvSingleton ZeroIdx       v = PPush PEnd v
partialEnvSingleton (SuccIdx idx) v = PNone $ partialEnvSingleton idx v

envToPartial :: Env f env -> PartialEnv f env
envToPartial Empty = PEnd
envToPartial (Push env a) = envToPartial env `PPush` a

-- Lazily converts a PartialEnv to an Env.
-- Laziness is here used to allow the environment to be used safely
-- even if some bindings are missing in the PartialEnv.
-- Only when a missing binding is actually used in this Env,
-- it will throw an error.
envFromPartialLazy :: HasCallStack => String -> PartialEnv f env -> Env f env
envFromPartialLazy msg = \case
  PEnd -> internalError (fromString msg)
  PNone env -> envFromPartialLazy msg env `Push` internalError (fromString msg)
  PPush env a -> envFromPartialLazy msg env `Push` a

-- Wrapper to put homogenous types in an Env or PartialEnv
newtype IdentityF t f = IdentityF t

-- Drops some bindings of env' to result in env.
data Skip env env' where
  SkipSucc :: Skip env (env', t) -> Skip env env'
  SkipNone :: Skip env env

skipIdx :: Skip env env' -> Idx env t -> Maybe (Idx env' t)
skipIdx SkipNone     idx = Just idx
skipIdx (SkipSucc s) idx = case skipIdx s idx of
  Just (SuccIdx idx') -> Just idx'
  _                   -> Nothing

chainSkip :: Skip env1 env2 -> Skip env2 env3 -> Skip env1 env3
chainSkip skipL (SkipSucc skipR) = SkipSucc $ chainSkip skipL skipR
chainSkip skipL SkipNone         = skipL

skipWeakenIdx :: Skip env env' -> env' :> env
skipWeakenIdx (SkipSucc s) = weakenSucc $ skipWeakenIdx s
skipWeakenIdx SkipNone     = weakenId

lhsSkip :: forall s t env1 env2. LeftHandSide s t env1 env2 -> Skip env2 env1
lhsSkip = (`go` SkipNone)
  where
    go :: LeftHandSide s t' env env' -> Skip env2 env' -> Skip env2 env
    go (LeftHandSideSingle _)   accum = SkipSucc accum
    go (LeftHandSideWildcard _) accum = accum
    go (LeftHandSidePair l1 l2) accum = go l1 $ go l2 accum

prjUpdate' :: (f t -> (f t, a)) -> Idx env t -> Env f env -> (Env f env, a)
prjUpdate' f ZeroIdx       (Push env v) = (Push env v', a)
  where (v', a) = f v
prjUpdate' f (SuccIdx idx) (Push env v) = (Push env' v, a)
  where (env', a) = prjUpdate' f idx env

prjReplace' :: Idx env t -> f t -> Env f env -> (Env f env, f t)
prjReplace' ix val = prjUpdate' (val, ) ix

update' :: (f t -> f t) -> Idx env t -> Env f env -> Env f env
update' f ZeroIdx       (Push env v) = Push env (f v)
update' f (SuccIdx idx) (Push env v) = Push (update' f idx env) v

-- Updates an environment for a list of indices. This is prefered over
-- calling update' multiple times, as that will create many 'Push' objects
-- as garbage.
-- Duplicate indices are handled only once.
--
updates' :: forall a f t env. (a -> f t -> f t) -> [(Idx env t, a)] -> Env f env -> Env f env
updates' _ []      env          = env
updates' f indices (Push env (v :: f s)) = updates' f succs env `Push` v'
  where
    g :: (Idx (env', s) t, a) -> Either (f s) (Idx env' t, a)
    g (ZeroIdx, a)     = Left $ f a v
    g (SuccIdx idx, a) = Right (idx, a)
    (zeros, succs) = partitionEithers $ map g indices
    v' :: f s
    v' = case zeros of
      v'' : _ -> v'' -- This index is in the list
      []      -> v     -- The index wasn't found
updates' _ _       Empty        = Empty

mapEnv :: (forall t. a t -> b t) -> Env a env -> Env b env
mapEnv _ Empty = Empty
mapEnv g (Push env f) = Push (mapEnv g env) (g f)


-- data Identity a = Identity { runIdentity :: a }

-- instance Functor Identity where
--   {-# INLINE fmap #-}
--   fmap f (Identity a) = Identity (f a)

-- instance Applicative Identity where
--   {-# INLINE (<*>) #-}
--   {-# INLINE pure  #-}
--   Identity f <*> Identity a = Identity (f a)
--   pure a                    = Identity a

-- The type of shifting terms from one context into another
--
-- This is defined as a newtype, as a type synonym containing a forall
-- quantifier may give issues with impredicative polymorphism, which GHC
-- does not support.
--
newtype env :> env' = Weaken { (>:>) :: forall (t' :: Type). Idx env t' -> Idx env' t' } -- Weak or Weaken

-- Weaken is currently just a function. We could consider to partially defunctionalize this and define
-- it as a data type, which constructors for the following functions.
-- Note that we may then also need to fold a chain of weakenSucc to a SkipIdx, and change the internal
-- definition of SkipIdx to Int (like we also did for Idx).

weakenId :: env :> env
weakenId = Weaken id

weakenSucc' :: env :> env' -> env :> (env', t)
weakenSucc' (Weaken f) = Weaken (SuccIdx . f)

weakenSucc :: (env, t) :> env' -> env :> env'
weakenSucc (Weaken f) = Weaken (f . SuccIdx)

weakenKeep :: env :> env' -> (env, t) :> (env', t)
weakenKeep (Weaken f) = Weaken $ \case
  ZeroIdx -> ZeroIdx
  SuccIdx i -> SuccIdx $ f i

weakenEmpty :: () :> env'
weakenEmpty = Weaken $ \(VoidIdx x) -> x

weakenReplace :: forall env env' t. Idx env' t -> env :> env' -> (env, t) :> env'
weakenReplace other k = Weaken f
  where
    f :: forall s. Idx (env, t) s -> Idx env' s
    f ZeroIdx = other
    f (SuccIdx idx) = k >:> idx

sink :: forall env env' t. env :> env' -> (env, t) :> (env', t)
sink (Weaken f) = Weaken g
  where
    g :: Idx (env, t) t' -> Idx (env', t) t'
    g ZeroIdx      = ZeroIdx
    g (SuccIdx ix) = SuccIdx $ f ix

infixr 9 .>
(.>) :: env2 :> env3 -> env1 :> env2 -> env1 :> env3
(.>) (Weaken f) (Weaken g) = Weaken (f . g)

sinkWithLHS :: HasCallStack => LeftHandSide s t env1 env1' -> LeftHandSide s t env2 env2' -> env1 :> env2 -> env1' :> env2'
sinkWithLHS (LeftHandSideWildcard _) (LeftHandSideWildcard _) k = k
sinkWithLHS (LeftHandSideSingle _)   (LeftHandSideSingle _)   k = sink k
sinkWithLHS (LeftHandSidePair a1 b1) (LeftHandSidePair a2 b2) k = sinkWithLHS b1 b2 $ sinkWithLHS a1 a2 k
sinkWithLHS _ _ _ = internalError "left hand sides do not match"

weakenWithLHS :: forall s t env env'. LeftHandSide s t env env' -> env :> env'
weakenWithLHS = go weakenId
  where
    go :: env2 :> env' -> LeftHandSide s arrs env1 env2 -> env1 :> env'
    go k (LeftHandSideWildcard _) = k
    go k (LeftHandSideSingle _)   = weakenSucc k
    go k (LeftHandSidePair l1 l2) = go (go k l2) l1

substituteLHS :: forall s s' t env env'. LeftHandSide s t env env' -> Vars s' env t -> env' :> env
substituteLHS lhs vars = Weaken f
  where
    f :: Idx env' a -> Idx env a
    f ix = case go lhs vars ix of
      Left  ix' -> ix'
      Right ix' -> ix'

    go :: LeftHandSide s u env1 env2 -> Vars s' env u -> Idx env2 a -> Either (Idx env a) (Idx env1 a)
    go (LeftHandSideWildcard _) _ idx = Right idx
    go (LeftHandSideSingle _)   (TupRsingle (Var _ var)) idx = case idx of
      ZeroIdx      -> Left var
      SuccIdx idx' -> Right idx'
    go (LeftHandSidePair l1 l2) (TupRpair v1 v2) idx = go l2 v2 idx >>= go l1 v1
    go _ _ _ = error "LHS and tuple mismatch"


varsGet :: Applicative f => Vars s env t -> Env f env -> f t
varsGet TupRunit _ = pure ()
varsGet (TupRsingle (Var _ idx)) env = prj' idx env
varsGet (TupRpair v1 v2) env = (,) <$> varsGet v1 env <*> varsGet v2 env

varsGetVal :: Vars s env t -> Val env -> t
varsGetVal vars = runIdentity . varsGet vars

stripWithLhs :: LeftHandSide f a env env' -> Env g env' -> Env g env
stripWithLhs (LeftHandSideSingle _) (Push env _) = env
stripWithLhs (LeftHandSideWildcard _) env = env
stripWithLhs (LeftHandSidePair lhs1 lhs2) env = stripWithLhs lhs1 $ stripWithLhs lhs2 env



