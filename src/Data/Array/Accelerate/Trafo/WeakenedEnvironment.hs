{-# LANGUAGE EmptyCase           #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}
{-# OPTIONS_HADDOCK hide #-}
{-# LANGUAGE PatternSynonyms #-}
-- |
-- Module      : Data.Array.Accelerate.AST.WeakenedEnvironment
-- Copyright   : [2008..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.Trafo.WeakenedEnvironment
  ( WEnv, WEnv'(..), wprj, wprj', wupdate, wupdateSetWeakened, wempty, wpush, wpush2, wpush', wremoveSet, wupdatePrjSet
  ) where

import Data.Array.Accelerate.AST.Environment
import Data.Array.Accelerate.AST.Idx
import Data.Array.Accelerate.AST.IdxSet (IdxSet(..))
import Data.Array.Accelerate.AST.LeftHandSide
import Data.Array.Accelerate.Trafo.Substitution

-- Valuation for an environment
--
type WEnv f env = WEnv' f env env

data WEnv' f env' env where
  WEmpty  :: WEnv' f env' ()
  WPushA  :: WEnv' f env' env -> f env'      t -> WEnv' f env'      (env, t)
  WPushB  :: WEnv' f env' env -> f (env', t) t -> WEnv' f (env', t) (env, t)
  WWeaken :: env1 :> env2 -> WEnv' f env1 env -> WEnv' f env2 env

wprj :: Sink f => Idx envB t -> WEnv' f envA envB -> f envA t
wprj = wprj' weakenId

wprj' :: Sink f => env1 :> env2 -> Idx env t -> WEnv' f env1 env -> f env2 t
wprj' k idx (WWeaken k' env) = wprj' (k .> k') idx env
wprj' k ZeroIdx (WPushA _ v) = weaken k v
wprj' k ZeroIdx (WPushB _ v) = weaken k v
wprj' k (SuccIdx idx) (WPushA env _) = wprj' k idx env
wprj' k (SuccIdx idx) (WPushB env _) = wprj' (weakenSucc k) idx env

instance Sink f => Sink (WEnv' f) where
  weaken k (WWeaken k' env) = WWeaken (k .> k') env
  weaken k env              = WWeaken k         env

wupdate :: forall f env' env t. Sink f => (f env' t -> f env' t) -> Idx env t -> WEnv' f env' env -> WEnv' f env' env
wupdate f = go'
  where
    -- Specialized version of go, where env1 ~ env'
    go' :: Idx env2 t -> WEnv' f env' env2 -> WEnv' f env' env2
    go' idx           (WWeaken k' env) = go k' idx env
    go' ZeroIdx       (WPushA env v)   = WPushA env $ f v
    go' ZeroIdx       (WPushB env v)   = WPushB env $ f v
    go' (SuccIdx idx) (WPushA env v)   = WPushA (go' idx env) v
    go' (SuccIdx idx) (WPushB env v)   = WPushA (go (weakenSucc weakenId) idx env) v

    go :: (env1 :> env') -> Idx env2 t -> WEnv' f env1 env2 -> WEnv' f env' env2
    go k idx           (WWeaken k' env) = go (k .> k') idx env
    go k ZeroIdx       (WPushA env v)   = WPushA (weaken k              env) $ f $ weaken k v
    go k ZeroIdx       (WPushB env v)   = WPushA (weaken (weakenSucc k) env) $ f $ weaken k v
    go k (SuccIdx idx) (WPushA env v)   = WPushA (go k idx env)                  $ weaken k v
    go k (SuccIdx idx) (WPushB env v)   = WPushA (go (weakenSucc k) idx env)     $ weaken k v

wupdateSetWeakened :: forall f env' env. (forall env1 t. env1 :> env' -> f env1 t -> f env1 t) -> IdxSet env -> WEnv' f env' env -> WEnv' f env' env
wupdateSetWeakened f (IdxSet set) = go weakenId set
  where
    go :: (env1 :> env') -> PartialEnv g env2 -> WEnv' f env1 env2 -> WEnv' f env1 env2
    go _ PEnd        env              = env
    go k p           (WWeaken k' env) = WWeaken k' $ go (k .> k') p env
    go k (PPush p _) (WPushA env v)   = WPushA (go k p env) (f k v)
    go k (PPush p _) (WPushB env v)   = WPushB (go (weakenSucc k) p env) (f k v)
    go k (PNone p)   (WPushA env v)   = WPushA (go k p env) v
    go k (PNone p)   (WPushB env v)   = WPushB (go (weakenSucc k) p env) v

wempty :: WEnv f ()
wempty = WEmpty

wpush :: WEnv f env -> f (env, t) t -> WEnv f (env, t)
wpush = WPushB

wpush2 :: Sink f => WEnv f env -> f ((env, t), s) t -> f ((env, t), s) s -> WEnv f ((env, t), s)
wpush2 env t s = weaken (weakenSucc $ weakenSucc weakenId) env `WPushA` t `WPushA` s

wpush' :: WEnv' f env' env -> f env' t -> WEnv' f env' (env, t)
wpush' = WPushA

wremoveSet :: forall f env. (forall env' t. f env' t) -> IdxSet env -> WEnv f env -> WEnv f env
wremoveSet nil (IdxSet set) env = go set env
  where
    go :: PartialEnv g env' -> WEnv' f env1 env' -> WEnv' f env1 env'
    go PEnd        e             = e
    go p           (WWeaken k e) = WWeaken k $ go p e
    go (PNone p)   (WPushA e f)  = WPushA (go p e) f
    go (PNone p)   (WPushB e f)  = WPushB (go p e) f
    go (PPush p _) (WPushA e _)  = WPushA (go p e) nil
    go (PPush p _) (WPushB e _)  = WPushB (go p e) nil

wupdatePrjSet :: forall f env. Sink f => (forall env' t. f env' t -> f env' t) -> IdxSet env -> WEnv f env -> ([Exists (f env)], WEnv f env)
wupdatePrjSet update (IdxSet set) env = go weakenId set env
  where
    go :: env1 :> env -> PartialEnv g env' -> WEnv' f env1 env' -> ([Exists (f env)], WEnv' f env1 env')
    go _ PEnd        e             = ([], e)
    go k p           (WWeaken k' e) = (l, WWeaken k' e')
      where (l, e') = go (k .> k') p e
    go k (PNone p)   (WPushA e f)  = (Exists (weaken k f) : l, WPushA e' $ update f)
      where (l, e') = go k p e
    go k (PNone p)   (WPushB e f)  = (Exists (weaken k f) : l, WPushB e' $ update f)
      where (l, e') = go (weakenSucc k) p e
    go k (PPush p _) (WPushA e f)  = (l, WPushA e' f)
      where (l, e') = go k p e
    go k (PPush p _) (WPushB e f)  = (l, WPushB e' f)
      where (l, e') = go (weakenSucc k) p e
