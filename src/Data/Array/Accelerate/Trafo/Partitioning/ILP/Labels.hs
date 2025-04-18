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
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Data.Array.Accelerate.Trafo.Partitioning.ILP.Labels where

import Data.Array.Accelerate.AST.Operation
import Data.Array.Accelerate.Representation.Type

import Lens.Micro
import Lens.Micro.TH
import Lens.Micro.Mtl
import Lens.Micro.Extras

import Data.Set (Set)
import qualified Data.Set as S

import Data.Hashable (Hashable, hashWithSalt)
import Data.Array.Accelerate.AST.Idx
import Prelude hiding (exp)
import Data.Array.Accelerate.AST.LeftHandSide

import qualified Data.Functor.Const as C
import Data.Coerce
import Control.Monad.State
import Data.Foldable
import Data.Typeable
import Data.Array.Accelerate.Type (ScalarType)
import Data.Array.Accelerate.Representation.Array
import Data.Bifunctor (Bifunctor(..))
import Data.Maybe (fromJust)



--------------------------------------------------------------------------------
-- Labels
--------------------------------------------------------------------------------

-- | The types a label can have.
data LabelType = Comp | Buff

-- | Labels for referencing nodes.
--
-- A label uniquely identifies a node and optionally specifies the parent it
-- belongs to. Only 'Comp' labels may be parents.
--
-- A label of type 'Comp' is used to represent anything that is relevant for
-- reconstruction but not for the fusion/in-place updates ILP. This type mostly
-- represents the labels for bodies of functions, if-then-else branches, and
-- while loops.
--
-- @VLabel x Nothing@ means that label @x@ is top-level.
-- @VLabel x (Just y)@ means that label @x@ is a sub-computation of label @y@.
data Label (t :: LabelType) where
  Label :: Int      -- ^ The computation label.
        -> Parent   -- ^ The parent computation.
        -> Label t

type Parent = Maybe (Label Comp)

-- | Lens for getting and setting the label id.
labelId :: Lens' (Label t) Int
labelId f (Label i p) = f i <&> (`Label` p)

-- | Lens for getting and setting the parent label.
parent :: Lens' (Label t) Parent
parent f (Label i p) = f p <&> Label i

-- | Lens for setting and unsafely getting the parent.
parent' :: Lens' (Label t) (Label Comp)
parent' f (Label i p) = f (fromJust p) <&> (Label i . Just)

-- | Lens for interpreting any label as a computation label.
asComp :: Lens' (Label t) (Label Comp)
asComp f l = coerce <$> f (coerce l)

-- | Lens for interpreting any label as a buffer label.
asBuff :: Lens' (Label t) (Label Buff)
asBuff f l = coerce <$> f (coerce l)

instance Show (Label t) where
  show :: Label t -> String
  show l = "L" <> show (l^.labelId) <> "{" <> show (l^.parent) <> "}"

instance Eq (Label t) where
  (==) :: Label t -> Label t -> Bool
  (==) (Label i1 p1) (Label i2 p2)
    | i1 == i2  = checkMismatch p1 p2 True
    | otherwise = False

instance Ord (Label t) where
  compare :: Label t -> Label t -> Ordering
  compare (Label i1 p1) (Label i2 p2) = case compare i1 i2 of
    EQ -> checkMismatch p1 p2 EQ
    LT -> LT
    GT -> GT

-- | Checks if two parents are equal and throw an error if they are not.
checkMismatch :: Parent -> Parent -> a -> a
checkMismatch (Just l1) (Just l2) | l1 == l2 = id
checkMismatch Nothing Nothing = id
checkMismatch _ _ = error "checkMismatch: Mismatching labels detected."

instance Hashable (Label t) where
  hashWithSalt :: Int -> Label t -> Int
  hashWithSalt s l = hashWithSalt s (l ^. labelId)

-- | Compute the nesting level of a label.
level :: Label t -> Int
level l = case l^.parent of
  Nothing -> 0
  Just p  -> 1 + level p

-- | Check if a parent label is an ancestor of another label.
ancestorOf :: Parent -> Label t -> Bool
ancestorOf Nothing _ = True  -- The top-level label is always an ancestor.
ancestorOf p1 (Label _ p2) = p1 == p2 || maybe False (ancestorOf p1) p2

-- | Create a new label.
freshL' :: State (Label t) (Label t)
freshL' = id <%= (labelId +~ 1)

-- | Set of labels.
type Labels t = Set (Label t)



--------------------------------------------------------------------------------
-- Constant-valued Tuple Representation
--------------------------------------------------------------------------------

-- | Flipped, constant 'TupR'.
newtype TupF t a = TupF { unTupF :: TupR (C.Const a) t }
pattern TupFunit :: TupF () a
pattern TupFunit = TupF TupRunit
pattern TupFsingle :: a -> TupF t a
pattern TupFsingle a = TupF (TupRsingle (C.Const a))
pattern TupFpair :: TupF s a -> TupF t a -> TupF (s, t) a
pattern TupFpair l r <- TupF (TupRpair (TupF -> l) (TupF -> r)) where
  TupFpair (unTupF -> l) (unTupF -> r) = TupF (TupRpair l r)
{-# COMPLETE TupFunit, TupFsingle, TupFpair #-}

instance Show a => Show (TupF t a) where
  show :: Show a => TupF t a -> String
  show (TupF tup) = show tup

instance Functor (TupF t) where
  fmap :: forall a b. (a -> b) -> TupF t a -> TupF t b
  fmap f = TupF . go . unTupF
    where
      go :: TupR (C.Const a) s -> TupR (C.Const b) s
      go TupRunit       = TupRunit
      go (TupRsingle a) = TupRsingle (coerce f a)
      go (TupRpair l r) = TupRpair (go l) (go r)


instance Foldable (TupF t) where
  foldMap :: forall m a. Monoid m => (a -> m) -> TupF t a -> m
  foldMap f = go . unTupF
    where
      go :: TupR (C.Const a) s -> m
      go TupRunit       = mempty
      go (TupRsingle a) = f (coerce a)
      go (TupRpair l r) = go l <> go r

instance Traversable (TupF t) where
  traverse :: forall f a b. Applicative f => (a -> f b) -> TupF t a -> f (TupF t b)
  traverse f = (TupF <$>) . go . unTupF
    where
      go :: TupR (C.Const a) s -> f (TupR (C.Const b) s)
      go TupRunit       = pure TupRunit
      go (TupRsingle a) = TupRsingle . coerce <$> f (coerce a)
      go (TupRpair l r) = TupRpair <$> go l <*> go r

instance Semigroup a => Semigroup (TupF t a) where
  (<>) :: TupF t a -> TupF t a -> TupF t a
  (<>) (TupF t1) (TupF t2) = TupF (go t1 t2)
    where
      go :: TupR (C.Const a) s -> TupR (C.Const a) s -> TupR (C.Const a) s
      go TupRunit         TupRunit         = TupRunit
      go (TupRsingle a)   (TupRsingle b)   = TupRsingle (coerce (a <> b))
      go (TupRpair l1 r1) (TupRpair l2 r2) = TupRpair (go l1 l2) (go r1 r2)
      go _ _ = error "TupR_: Inaccessible left-hand side"


-- | Create a 'TupF' containing a single value in the same shape as a 'TupR'.
tupFlike :: TupR s t -> b -> TupF t b
tupFlike TupRunit       _ = TupFunit
tupFlike (TupRsingle _) b = TupFsingle b
tupFlike (TupRpair l r) b = TupFpair (tupFlike l b) (tupFlike r b)



--------------------------------------------------------------------------------
-- Labelled Environment
--------------------------------------------------------------------------------

-- | An 'ELabel' uniquely identifies an element of the environment.
newtype EnvLabel = EnvLabel { unELabel :: Int }
  deriving (Show, Eq, Ord, Num)

-- | A 'TupF' of 'EnvLabel'.
type EnvLabelTupF t = TupF t EnvLabel

freshE' :: State EnvLabel EnvLabel
freshE' = id <%= (+1)

-- | Tuple of 'Labels' of type 'Buff' to be stored in the environment.
--
-- We use a tuple of labels instead of a single label because after an
-- if-then-else there are now two labels that could be referenced depending
-- on the branch taken.
type BuffersTupF t = TupF t (Labels Buff)

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
data LabelsEnv env where
  -- | The empty environment.
  EnvNil :: LabelsEnv ()
  -- | The non-empty environment.
  (:>>:) :: (EnvLabel, BuffersTupF t)  -- ^ A pair of 'EnvLabel' and 'BuffersTupF'.
         -> LabelsEnv env              -- ^ The rest of the environment.
         -> LabelsEnv (env, t)

instance Semigroup (LabelsEnv env) where
  (<>) :: LabelsEnv env -> LabelsEnv env -> LabelsEnv env
  (<>) EnvNil EnvNil = EnvNil
  (<>) ((e1, bs1) :>>: env1) ((e2, bs2) :>>: env2)
    | e1 == e2  = (e1, bs1 <> bs2) :>>: (env1 <> env2)
    | otherwise = error "mappend: Encountered diverging EnvLabels."


-- | Constructs a new 'LabelsEnv' by prepending labels for each element in the
--   left-hand side.
--
-- The case where the left-hand side and the right-hand side are incompatible
-- should neven happen. But in case it does happen I already have an
-- implementation prepared that will duplicate the 'TupRsingle_'.
weakenEnv :: LeftHandSide s v env env' -> BuffersTupF v -> LabelsEnv env -> State EnvLabel (LabelsEnv env')
weakenEnv LeftHandSideWildcard{} _                  = pure
weakenEnv LeftHandSideSingle{}   bs                 = \lenv -> freshE' >>= \e -> return ((e, bs) :>>: lenv)
weakenEnv (LeftHandSidePair l r) (TupFpair lbs rbs) = weakenEnv l lbs >=> weakenEnv r rbs
weakenEnv (LeftHandSidePair _ _) _ = error "consLHS: Inaccesible left-hand side."



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

-- | 'EnvLabels' retrieved from the 'LabelsEnv' stored with an 'Arg', but only
--   if the argument is an array.
data ArgLabels t where
  -- | The argument is an array.
  Arr    :: EnvLabelTupF e  -- ^ The array (as structure-of-arrays).
         -> ArgLabels (m sh e)
  -- | The argument is a scalar 'Var'', 'Exp'' or 'Fun''.
  NotArr :: ArgLabels (t e)

deriving instance Show (ArgLabels t)

-- | The argument to a function paired with its 'ArgLabels' and other
--   dependencies.
data LabelledArg env t = L (Arg env t) (ArgLabels t, Labels Buff)
  deriving (Show)

-- | Labelled arguments to be passed to a function.
type LabelledArgs env = PreArgs (LabelledArg env)

-- | Label the arguments to a function using the given environment.
labelArgs :: Args env args -> LabelsEnv env -> LabelledArgs env args
labelArgs ArgsNil _ = ArgsNil
labelArgs (arg :>: args) env =
  L arg (getArgLabels arg env) :>: labelArgs args env

-- | Get the 'ArgLabels' associated with 'Arg' from 'LabelsEnv'.
getArgLabels :: Arg env t -> LabelsEnv env -> (ArgLabels t, Labels Buff)
getArgLabels (ArgVar vars) env = (NotArr, getVarsDeps vars env)
getArgLabels (ArgExp exp)  env = (NotArr, getExpDeps  exp  env)
getArgLabels (ArgFun fun)  env = (NotArr, getFunDeps  fun  env)
getArgLabels (ArgArray _ (ArrayR _ tp) sh bu) env
  | (_       , shBs) <- getVarsFromEnv sh env
  , (Arr buEs, buBs) <- getVarsFromEnv bu env
  = (unbuffers tp $ Arr buEs, fold shBs <> fold buBs)
getArgLabels _ _ = error "getArgLabels: Inaccessible left-hand side."

-- | Get the values associated with 'Vars' from 'LabelsEnv'.
getVarsFromEnv :: Vars a env b -> LabelsEnv env -> (ArgLabels (m sh b), BuffersTupF b)
getVarsFromEnv TupRunit         _   = (Arr TupFunit, TupFunit)
getVarsFromEnv (TupRsingle var) env = getVarFromEnv var env
getVarsFromEnv (TupRpair l r)   env | (Arr l', bs1) <- getVarsFromEnv l env
                                    , (Arr r', bs2) <- getVarsFromEnv r env
                                    = (Arr (TupFpair l' r'), TupFpair bs1 bs2)
getVarsFromEnv _ _ = error "getVarsFromEnv: Inaccessible left-hand side."

-- | Get the value associated with a 'Var' from 'LabelsEnv'.
getVarFromEnv :: Var a env b -> LabelsEnv env -> (ArgLabels (m sh b), BuffersTupF b)
getVarFromEnv (varIdx -> idx) = first (Arr . TupFsingle) . lookupIdxInEnv idx

-- | Get the value associated with an 'Idx' from 'LabelsEnv'.
lookupIdxInEnv :: Idx env a -> LabelsEnv env -> (EnvLabel, BuffersTupF a)
lookupIdxInEnv ZeroIdx       (bs :>>: _)   = bs
lookupIdxInEnv (SuccIdx idx) (_  :>>: env) = lookupIdxInEnv idx env


-- | Get the dependencies of a tuple of variables.
getVarsDeps :: Vars s env t -> LabelsEnv env -> Labels Buff
getVarsDeps vars = fold . snd . getVarsFromEnv vars

-- | Get the dependencies of a tuple of variables.
getVarDeps :: Var s env t -> LabelsEnv env -> Labels Buff
getVarDeps var = fold . snd . getVarFromEnv var

-- | Get the dependencies of an expression.
getExpDeps :: OpenExp x env y -> LabelsEnv env -> Labels Buff
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
getFunDeps :: OpenFun x env y -> LabelsEnv env -> Labels Buff
getFunDeps (Body  poe) env = getExpDeps poe env
getFunDeps (Lam _ fun) env = getFunDeps fun env

-- | Remove the 'Buffers' type from 'ArgLabels'.
unbuffers :: forall m sh e. TypeR e -> ArgLabels (m sh (Buffers e)) -> ArgLabels (m sh e)
unbuffers TupRunit _ = Arr TupFunit
unbuffers (TupRsingle t) (Arr (TupFsingle e))
  | Refl <- reprIsSingle @ScalarType @e @Buffer t
  = Arr (TupFsingle e)
unbuffers (TupRpair t1 t2) (Arr (TupFpair l r))
  | Arr l' <- unbuffers t1 (Arr l)
  , Arr r' <- unbuffers t2 (Arr r)
  = Arr (TupFpair l' r')
unbuffers _ (Arr _) = error "Tuple mismatch"
unbuffers _ _ = error "Not an array"



--------------------------------------------------------------------------------
-- Helpers for Labelled Environment
--------------------------------------------------------------------------------

-- | Map a function over the labels in the environment.
mapLEnv :: (forall t. BuffersTupF t -> BuffersTupF t) -> LabelsEnv env -> LabelsEnv env
mapLEnv _ EnvNil = EnvNil
mapLEnv f ((e, bs) :>>: env) = (e, f bs) :>>: mapLEnv f env

-- | Flipped version of 'mapLEnv'.
forLEnv :: LabelsEnv env -> (forall t. BuffersTupF t -> BuffersTupF t) -> LabelsEnv env
forLEnv env f = mapLEnv f env
{-# INLINE forLEnv #-}

-- | Fold over the labels in the environment.
foldMapLEnv :: Monoid m => (forall t. BuffersTupF t -> m) -> LabelsEnv env -> m
foldMapLEnv _ EnvNil = mempty
foldMapLEnv f ((_, bs) :>>: env) = f bs <> foldMapLEnv f env

-- | Map a monadic function over the labels in the environment.
mapLEnvM :: Monad m => (forall t. BuffersTupF t -> m (BuffersTupF t)) -> LabelsEnv env -> m (LabelsEnv env)
mapLEnvM _ EnvNil = return EnvNil
mapLEnvM f ((e, bs) :>>: env) = do
  bs'  <- f bs
  env' <- mapLEnvM f env
  return ((e, bs') :>>: env')

-- | Flipped version of 'mapLEnvM'.
forLEnvM :: Monad m => LabelsEnv env -> (forall t. BuffersTupF t -> m (BuffersTupF t)) -> m (LabelsEnv env)
forLEnvM env f = mapLEnvM f env
{-# INLINE forLEnvM #-}

-- | Map a monadic action over the labels in the environment and discard the result.
mapLEnvM_ :: Monad m => (forall t. BuffersTupF t -> m ()) -> LabelsEnv env -> m ()
mapLEnvM_ _ EnvNil = return ()
mapLEnvM_ f ((_, bs) :>>: env) = f bs >> mapLEnvM_ f env

-- | Flipped version of 'mapLEnvM_'.
forLEnvM_ :: Monad m => LabelsEnv env -> (forall t. BuffersTupF t -> m ()) -> m ()
forLEnvM_ env f = mapLEnvM_ f env
{-# INLINE forLEnvM_ #-}



--------------------------------------------------------------------------------
-- Helpers for Labelled Arguments
--------------------------------------------------------------------------------

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
