{-
Module      : Data.Array.Accelerate.Trafo.Partitioning.ILP.LabelsNew
Description : Labels representing nodes in the graph.

This module provides the labels that represent nodes in the graph. A node can
either be a computation or a buffer.
-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE QuantifiedConstraints #-}
module Data.Array.Accelerate.Trafo.Partitioning.ILP.LabelsNew where

import Data.Array.Accelerate.AST.Operation
import Data.Array.Accelerate.Representation.Type

import Lens.Micro
import Lens.Micro.TH
import Lens.Micro.Mtl
import Lens.Micro.Extras

import Data.Set (Set)
import qualified Data.Set as S

import Data.Map (Map)
import qualified Data.Map as M

import Data.Hashable (Hashable, hashWithSalt)
import Data.Array.Accelerate.AST.Idx
import Prelude hiding (exp)
import Data.Array.Accelerate.AST.LeftHandSide

import qualified Data.Functor.Const as C
import Data.Coerce
import Control.Monad.State



--------------------------------------------------------------------------------
-- Labels
--------------------------------------------------------------------------------

-- | The types a label can have.
data LabelType = Comp | Buff | Void

-- | Labels for referencing nodes.
--
-- A label uniquely identifies a node and optionally specifies the parent it
-- belongs to. A buffer node can never be a parent.
--
-- A label of type 'Void' is used to represent anything that is relevant for
-- reconstruction but not for the fusion/in-place updates ILP. These are mostly
-- scopes of some kind.
--
-- @VLabel x Nothing@ means that label @x@ is top-level.
-- @VLabel x (Just y)@ means that label @x@ is a sub-computation of label @y@.
data Label (t :: LabelType) where
  CLabel  :: Int                  -- ^ The computation label.
          -> Maybe (Label Void)   -- ^ The parent computation.
          -> Label Comp
  BLabel  :: Int                  -- ^ The buffer label.
          -> Maybe (Label Void)   -- ^ The parent computation.
          -> Label Buff
  VLabel  :: Int                  -- ^ The void label.
          -> Maybe (Label Void)   -- ^ The parent computation.
          -> Label Void

-- | Lens for getting and setting the label id.
labelId :: Lens' (Label t) Int
labelId f (CLabel i p) = fmap (`CLabel` p) (f i)
labelId f (BLabel i p) = fmap (`BLabel` p) (f i)
labelId f (VLabel i p) = fmap (`VLabel` p) (f i)

-- | Lens for getting and setting the parent label.
parent :: Lens' (Label t) (Maybe (Label Void))
parent f (CLabel i p) = fmap (CLabel i) (f p)
parent f (BLabel i p) = fmap (BLabel i) (f p)
parent f (VLabel i p) = fmap (VLabel i) (f p)

-- | Lens for interpreting any label as a computation label.
asCLabel :: Lens' (Label t) (Label Comp)
asCLabel f l@CLabel{} = f l
asCLabel f l = fmap (\(CLabel i p) -> l & labelId .~ i & parent .~ p)
                    (f (CLabel (l ^. labelId) (l ^. parent)))

-- | Lens for interpreting any label as a buffer label.
asBLabel :: Lens' (Label t) (Label Buff)
asBLabel f l@BLabel{} = f l
asBLabel f l = fmap (\(BLabel i p) -> l & labelId .~ i & parent .~ p)
                    (f (BLabel (l ^. labelId) (l ^. parent)))

-- | Lens for interpreting any label as a void label.
asVLabel :: Lens' (Label t) (Label Void)
asVLabel f l@VLabel{} = f l
asVLabel f l = fmap (\(VLabel i p) -> l & labelId .~ i & parent .~ p)
                    (f (VLabel (l ^. labelId) (l ^. parent)))

instance Show (Label t) where
  show :: Label t -> String
  show l = "L" <> show (l ^. labelId) <> "{" <> show (l ^. parent) <> "}"

instance Eq (Label t) where
  (==) :: Label t -> Label t -> Bool
  (==) l1 l2  = l1 ^. labelId == l2 ^. labelId && (l1 ^. parent == l2 ^. parent || parentMismatch l1 l2)

instance Ord (Label t) where
  compare :: Label t -> Label t -> Ordering
  compare l1 l2 = case compare (l1 ^. labelId) (l2 ^. labelId) of
    EQ -> if l1 ^. parent == l2 ^. parent then EQ else parentMismatch l1 l2
    x  -> x

-- | Error message for when parent computation labels do not match.
parentMismatch :: Label t -> Label t -> a
parentMismatch l1 l2 = error $ "parent mismatch: " <> show l1 <> " " <> show l2

instance Hashable (Label t) where
  hashWithSalt :: Int -> Label t -> Int
  hashWithSalt s l = hashWithSalt s (l ^. labelId)

-- | Compute the nesting level of a label.
level :: Label t -> Int
level l = case l ^. parent of
  Nothing -> 0
  Just p  -> 1 + level p

-- | Checks whether a computation can access a buffer. I.e. checks if the buffer
-- is in scope.
--
-- A buffer is in scope when the parent of the buffer is an ancestor of the
-- computation.
--
canAccess :: Label Comp -> Label Buff -> Bool
canAccess l b = l ^. parent == b ^. parent || case l ^. parent of
  Nothing -> False
  Just p  -> canAccess (p ^. asCLabel) b

-- | Set of labels.
type Labels t = Set (Label t)

-- | Replace a label in a set of labels with another.
updateLabels :: Label t -> Label t -> Labels t -> Labels t
updateLabels b b' bs
  | b /= b' && S.member b bs = S.insert b' (S.delete b bs)
  | otherwise                = bs

freshL' :: State (Label t) (Label t)
freshL' = id <%= (labelId +~ 1)



--------------------------------------------------------------------------------
-- Tupled Labels
--------------------------------------------------------------------------------

{- | Variant of 'TupR' that ignores the type information. -}
data TupR_ t a where
  TupRunit_   ::                           TupR_ () a
  TupRsingle_ :: a                      -> TupR_ t  a
  TupRpair_   :: TupR_ s a -> TupR_ t a -> TupR_ (s, t) a

deriving instance Show a => Show (TupR_ t a)

instance Functor (TupR_ t) where
  fmap :: (a -> b) -> TupR_ t a -> TupR_ t b
  fmap _ TupRunit_       = TupRunit_
  fmap f (TupRsingle_ a) = TupRsingle_ (f a)
  fmap f (TupRpair_ l r) = TupRpair_ (fmap f l) (fmap f r)

instance Foldable (TupR_ t) where
  foldMap :: Monoid m => (a -> m) -> TupR_ t a -> m
  foldMap _ TupRunit_       = mempty
  foldMap f (TupRsingle_ a) = f a
  foldMap f (TupRpair_ l r) = foldMap f l <> foldMap f r

instance Traversable (TupR_ t) where
  traverse :: Applicative f => (a -> f b) -> TupR_ t a -> f (TupR_ t b)
  traverse _ TupRunit_       = pure TupRunit_
  traverse f (TupRsingle_ a) = TupRsingle_ <$> f a
  traverse f (TupRpair_ l r) = TupRpair_ <$> traverse f l <*> traverse f r

-- | Create a 'TupR_' containing a single value in the same shape as a 'TupR'.
tupRlike_ :: TupR s t -> b -> TupR_ t b
tupRlike_ TupRunit       _ = TupRunit_
tupRlike_ (TupRsingle _) b = TupRsingle_ b
tupRlike_ (TupRpair l r) b = TupRpair_ (tupRlike_ l b) (tupRlike_ r b)

type LabelTup t s = TupR_ s (Label t)

-- | Get the values associated with 'Vars' in 'LabelEnv'.
getVarsLTup :: Vars s env t -> LabelEnv env -> LabelTup Buff t
getVarsLTup TupRunit         _   = TupRunit_
getVarsLTup (TupRsingle var) env = getVarLTup var env
getVarsLTup (TupRpair l r)   env = TupRpair_ (getVarsLTup l env) (getVarsLTup r env)

-- | Get the value associated with a 'Var' in 'LabelEnv'.
getVarLTup :: Var s env t -> LabelEnv env -> LabelTup Buff t
getVarLTup (varIdx -> idx) = getIdxLTup idx

-- | Get the value associated with an 'Idx' in 'LabelEnv'.
getIdxLTup :: Idx env t -> LabelEnv env -> LabelTup Buff t
getIdxLTup ZeroIdx       (bs :>>: _)   = bs
getIdxLTup (SuccIdx idx) (_  :>>: env) = getIdxLTup idx env



--------------------------------------------------------------------------------
-- Labelled Environment
--------------------------------------------------------------------------------

-- | The environment used during graph construction.
--
-- The environment is basically just a fixed length list of buffers with some
-- associated type information.
--
-- The buffers are stored as a map, mapping the buffer to its current producer.
-- We need to know which computation produces the buffer to make sure we don't
-- create fusible edges when a buffer has multiple writes. In such a case it
-- could be that we write, then read, then write again. Without this information
-- a fusible edge would be created between the reader and the last writer, even
-- though the reader is reading the data of the first writer, not the second.
--
data LabelEnv env where
  -- | The empty environment.
  EnvNil :: LabelEnv ()
  -- | The non-empty environment.
  (:>>:) :: (LabelTup Buff t)  -- ^ The buffers
         -> LabelEnv env       -- ^ The rest of the environment
         -> LabelEnv (env, t)

-- | Map a function over the labels in the environment.
mapLEnv :: (forall t. LabelTup Buff t -> LabelTup Buff t) -> LabelEnv env -> LabelEnv env
mapLEnv _ EnvNil = EnvNil
mapLEnv f (bs :>>: env) = f bs :>>: mapLEnv f env

-- | Flipped version of 'mapLEnv'.
forLEnv :: LabelEnv env -> (forall t. LabelTup Buff t -> LabelTup Buff t) -> LabelEnv env
forLEnv env f = mapLEnv f env
{-# INLINE forLEnv #-}

-- | Fold over the labels in the environment.
foldMapLEnv :: Monoid m => (forall t. LabelTup Buff t -> m) -> LabelEnv env -> m
foldMapLEnv _ EnvNil = mempty
foldMapLEnv f (bs :>>: env) = f bs <> foldMapLEnv f env

-- | Map a monadic function over the labels in the environment.
mapLEnvM :: Monad m => (forall t. LabelTup Buff t -> m (LabelTup Buff t)) -> LabelEnv env -> m (LabelEnv env)
mapLEnvM _ EnvNil = return EnvNil
mapLEnvM f (bs :>>: env) = do
  bs'  <- f bs
  env' <- mapLEnvM f env
  return (bs' :>>: env')

-- | Flipped version of 'mapLEnvM'.
forLEnvM :: Monad m => LabelEnv env -> (forall t. LabelTup Buff t -> m (LabelTup Buff t)) -> m (LabelEnv env)
forLEnvM env f = mapLEnvM f env
{-# INLINE forLEnvM #-}

-- | Map a monadic action over the labels in the environment and discard the result.
mapLEnvM_ :: Monad m => (forall t. LabelTup Buff t -> m ()) -> LabelEnv env -> m ()
mapLEnvM_ _ EnvNil = return ()
mapLEnvM_ f (bs :>>: env) = f bs >> mapLEnvM_ f env

-- | Flipped version of 'mapLEnvM_'.
forLEnvM_ :: Monad m => LabelEnv env -> (forall t. LabelTup Buff t -> m ()) -> m ()
forLEnvM_ env f = mapLEnvM_ f env
{-# INLINE forLEnvM_ #-}


-- | Constructs a new 'LabelEnv' by prepending labels for each element in the
--   left-hand side.
--
-- The case where the left-hand side and the right-hand side are incompatible
-- should neven happen. But in case it does happen I already have an
-- implementation prepared that will duplicate the 'TupRsingle_'.
consLHS :: LeftHandSide s v env env' -> LabelTup Buff v -> LabelEnv env -> LabelEnv env'
consLHS LeftHandSideWildcard{} _  = id
consLHS LeftHandSideSingle{}   bs = (bs :>>:)
consLHS (LeftHandSidePair l r) (TupRpair_ lbs rbs) = consLHS r rbs . consLHS l lbs
consLHS LeftHandSidePair{} TupRsingle_{} = error "consLHS: Inaccesible left-hand side."
-- consLHS (LeftHandSidePair l r) (TupRsingle_ b) = consLHS r (TupRsingle_ b) . consLHS l (TupRsingle_ b)



--------------------------------------------------------------------------------
-- Labelled Arguments
--------------------------------------------------------------------------------

{- |
The code below is for retrieving the labels for arguments to a function.
When the argument is 'ArgVar' (scalar valued variable), we need to retrieve the label(s) of the buffer(s) from the environment.
When the argument is 'ArgExp' (expression), we need to retrieve the labels of buffers the expression depends on.
When the argument is 'ArgFun' (function), we need to retrieve the labels of buffers the function depends on.
When the argument is 'ArgArray' (array), we need to retrieve the label(s) of the array(s).

For now it doesn't seem that a tuple argument needs to know the exact structure of the tuple, only which labels it references.
This means it's sufficient to pair each argument with a set of labels.

The main difference is that 'ArgArray' is the only value that may be fused.
The other types of arguments only ever read a single value from an array and
can therefore not be fused.
-}

-- | An argument to a function paired with some value.
data LabelledArg env t = LArg { unlabel :: Arg env t, unarg :: Labels Buff }
  deriving Show

-- | Labelled arguments to be passed to a function.
type LabelledArgs env = PreArgs (LabelledArg env)

-- | Label the arguments to a function using the given environment.
labelArgs :: Args env args -> LabelEnv env -> LabelledArgs env args
labelArgs ArgsNil _ = ArgsNil
labelArgs (arg :>: args) env =
  LArg arg (getArgDeps arg env) :>: labelArgs args env

-- | Map a function over the labelled arguments.
mapLArgs :: (forall s. LabelledArg env s -> LabelledArg env s) -> LabelledArgs env t -> LabelledArgs env t
mapLArgs _ ArgsNil = ArgsNil
mapLArgs f (larg :>: largs) = f larg :>: mapLArgs f largs

-- | Flipped version of 'mapLArgs'.
forLArgs :: LabelledArgs env t -> (forall s. LabelledArg env s -> LabelledArg env s) -> LabelledArgs env t
forLArgs largs f = mapLArgs f largs
{-# INLINE forLArgs #-}

-- | Fold over the labelled arguments and combine the resulting monoidal values.
foldMapLArgs :: Monoid m => (forall s. LabelledArg env s -> m) -> LabelledArgs env t -> m
foldMapLArgs _ ArgsNil = mempty
foldMapLArgs f (larg :>: largs) = f larg <> foldMapLArgs f largs

-- | Map a monadic function over the labelled arguments.
mapLArgsM :: Monad m => (forall s. LabelledArg env s -> m (LabelledArg env s)) -> LabelledArgs env t -> m (LabelledArgs env t)
mapLArgsM _ ArgsNil = return ArgsNil
mapLArgsM f (larg :>: largs) = do
  larg'  <- f larg
  largs' <- mapLArgsM f largs
  return (larg' :>: largs')

-- | Flipped version of 'mapLArgsM'.
forLArgsM :: Monad m => LabelledArgs env t -> (forall s. LabelledArg env s -> m (LabelledArg env s)) -> m (LabelledArgs env t)
forLArgsM largs f = mapLArgsM f largs
{-# INLINE forLArgsM #-}

-- | Map a monadic action over the labelled arguments and discard the result.
mapLArgsM_ :: Monad m => (forall s. LabelledArg env s -> m ()) -> LabelledArgs env t -> m ()
mapLArgsM_ _ ArgsNil = return ()
mapLArgsM_ f (larg :>: largs) = f larg >> mapLArgsM_ f largs

-- | Flipped version of 'mapLArgsM_'.
forLArgsM_ :: Monad m => LabelledArgs env t -> (forall s. LabelledArg env s -> m ()) -> m ()
forLArgsM_ largs f = mapLArgsM_ f largs
{-# INLINE forLArgsM_ #-}

-- | Map a monadic function over the labelled arguments and accumulate the result.
mapAccumLArgsM :: Monad m => (forall s. a -> LabelledArg env s -> m (a, LabelledArg env s)) -> a -> LabelledArgs env t -> m (a, LabelledArgs env t)
mapAccumLArgsM _ a ArgsNil = return (a, ArgsNil)
mapAccumLArgsM f a (larg :>: largs) = do
  (acc' , larg')  <- f a larg
  (acc'', largs') <- mapAccumLArgsM f acc' largs
  return (acc'', larg' :>: largs')

-- | Flipped version of 'mapAccumLArgsM'.
forAccumLArgsM :: Monad m => a -> LabelledArgs env t -> (forall s. a -> LabelledArg env s -> m (a, LabelledArg env s)) -> m (a, LabelledArgs env t)
forAccumLArgsM a largs f = mapAccumLArgsM f a largs
{-# INLINE forAccumLArgsM #-}

-- | Select labels from labeled arguments that satisfy the given predicate.
selectLArgs :: (forall s. Arg env s -> Bool) -> LabelledArgs env t -> Labels Buff
selectLArgs f = foldMapLArgs (\(LArg arg bs) -> if f arg then bs else mempty)
{-# INLINE selectLArgs #-}


--------------------------------------------------------------------------------
-- Getting Argument Dependencies
--------------------------------------------------------------------------------

-- | Get the dependencies of an argument.
getArgDeps :: Arg env t -> LabelEnv env -> Labels Buff
getArgDeps (ArgVar tup)         env = getVarsDeps tup env
getArgDeps (ArgExp exp)         env = getExpDeps  exp env
getArgDeps (ArgFun fun)         env = getFunDeps  fun env
getArgDeps (ArgArray _ _ sh bu) env = getVarsDeps sh env <> getVarsDeps bu env

-- | Get the dependencies of a tuple of variables.
getVarsDeps :: Vars s env t -> LabelEnv env -> Labels Buff
getVarsDeps vars env = toSet (getVarsLTup vars env)

-- | Get the dependencies of a variable.
getVarDeps :: Var s env t -> LabelEnv env -> Labels Buff
getVarDeps vars env = toSet (getVarLTup vars env)

-- | Get the dependencies of an expression.
getExpDeps :: OpenExp x env y -> LabelEnv env -> Labels Buff
getExpDeps (ArrayInstr (Index     var) poe) env = getVarDeps var  env <> getExpDeps poe  env
getExpDeps (ArrayInstr (Parameter var) poe) env = getVarDeps var  env <> getExpDeps poe  env
getExpDeps (Let _ poe1 poe2)                env = getExpDeps poe1 env <> getExpDeps poe2 env
getExpDeps (Evar _)                         _   = mempty
getExpDeps  Foreign{}                       _   = mempty
getExpDeps (Pair  poe1 poe2)                env = getExpDeps poe1 env <> getExpDeps poe2 env
getExpDeps  Nil                             _   = mempty
getExpDeps (VecPack _ poe)                  env = getExpDeps poe  env
getExpDeps (VecUnpack _ poe)                env = getExpDeps poe  env
getExpDeps (IndexSlice _ poe1 poe2)         env = getExpDeps poe1 env <> getExpDeps poe2 env
getExpDeps (IndexFull  _ poe1 poe2)         env = getExpDeps poe1 env <> getExpDeps poe2 env
getExpDeps (ToIndex    _ poe1 poe2)         env = getExpDeps poe1 env <> getExpDeps poe2 env
getExpDeps (FromIndex  _ poe1 poe2)         env = getExpDeps poe1 env <> getExpDeps poe2 env
getExpDeps (Case poe1 poes poe2)            env = getExpDeps poe1 env <>
                                                  foldMap ((`getExpDeps` env) . snd) poes <>
                                                  maybe mempty (`getExpDeps` env) poe2
getExpDeps (Cond poe1 poe2 exp3)            env = getExpDeps poe1 env <>
                                                  getExpDeps poe2 env <>
                                                  getExpDeps exp3 env
getExpDeps (While pof1 pof2 poe)            env = getFunDeps pof1 env <>
                                                  getFunDeps pof2 env <>
                                                  getExpDeps poe  env
getExpDeps (Const _ _)                      _   = mempty
getExpDeps (PrimConst _)                    _   = mempty
getExpDeps (PrimApp   _ poe)                env = getExpDeps poe  env
getExpDeps (ShapeSize _ poe)                env = getExpDeps poe  env
getExpDeps (Undef _)                        _   = mempty
getExpDeps  Coerce{}                        _   = mempty

-- | Get the dependencies of a function.
getFunDeps :: OpenFun x env y -> LabelEnv env -> Labels Buff
getFunDeps (Body  poe) env = getExpDeps poe env
getFunDeps (Lam _ fun) env = getFunDeps fun env



--------------------------------------------------------------------------------
-- Helpers
--------------------------------------------------------------------------------

-- | Convert a foldable structure to a set.
toSet :: (Foldable f, Ord a) => f a -> Set a
toSet = foldMap S.singleton
