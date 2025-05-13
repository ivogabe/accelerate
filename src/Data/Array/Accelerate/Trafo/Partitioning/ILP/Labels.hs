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
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE LambdaCase #-}
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
import Control.Monad.State.Strict
import Data.Foldable
import Data.Typeable
import Data.Array.Accelerate.Type (ScalarType)
import Data.Array.Accelerate.Representation.Array
import Data.Bifunctor (Bifunctor(..))
import Data.Maybe (fromJust, fromMaybe)
import Data.List
import Debug.Trace



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

instance Show (Label Comp) where
  show :: Label Comp -> String
  show c = "C" ++ intercalate "." (map show . reverse $ labelIds c)

instance Show (Label Buff) where
  show :: Label Buff -> String
  show b = "B" ++ intercalate "." (map show . reverse $ labelIds b)

labelIds :: Label t -> [Int]
labelIds (Label i p) = i : maybe [] labelIds p

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

-- | Tuple of 'Labels' of type 'Buff'.
type BuffersTup t = TupF t (Labels Buff)

-- | Tuple of 'Labels' of type 'Comp'.
type ComputationsTup t = TupF t (Labels Comp)


--------------------------------------------------------------------------------
-- Labelled Environment
--------------------------------------------------------------------------------

-- | An 'ELabel' uniquely identifies an element of the environment.
newtype EnvLabel = EnvLabel { unELabel :: Int }
  deriving (Eq, Ord, Num)

instance Show EnvLabel where
  show :: EnvLabel -> String
  show (EnvLabel i) = "E" ++ show i

-- | An 'EnvLabel' and all buffers associated with it.
--
-- 'EnvLabel' can probably be removed because its equivalent to @BufferTup t@.
type EnvLabels t = (EnvLabel, BuffersTup t)

-- | A 'TupF' of 'EnvLabel'.
type EnvLabelTup t = TupF t EnvLabel

-- | Create a fresh 'EnvLabel' from the current state.
freshE' :: State EnvLabel EnvLabel
freshE' = id <%= (+1)

-- | The environment used during graph construction.
--
-- The environment is basically just a fixed length list of buffers with some
-- associated type information.
--
-- We use a tuple of labels instead of a single label because after an
-- if-then-else there are now two labels that could be referenced depending
-- on the branch taken.
--
data BuffersEnv env where
  -- | The empty environment.
  EnvNil :: BuffersEnv ()
  -- | The non-empty environment.
  (:>>:) :: EnvLabels t     -- ^ See 'EnvLabels'.
         -> BuffersEnv env  -- ^ The rest of the environment.
         -> BuffersEnv (env, t)

instance Show (BuffersEnv env) where
  show :: BuffersEnv env -> String
  show EnvNil = "EnvNil"
  show (envl :>>: env) = show envl ++ " :>>: " ++ show env

-- TODO: Is this instance necessary?
instance Semigroup (BuffersEnv env) where
  (<>) :: BuffersEnv env -> BuffersEnv env -> BuffersEnv env
  (<>) EnvNil EnvNil = EnvNil
  (<>) ((e1, bs1) :>>: env1) ((e2, bs2) :>>: env2)
    | e1 == e2  = (e1, bs1 <> bs2) :>>: (env1 <> env2)
    | otherwise = error "mappend: Encountered diverging EnvLabels."

-- | Constructs a new 'BuffersEnv' by prepending labels for each element in the
--   left-hand side.
--
-- The case where the left-hand side and the right-hand side are incompatible
-- should neven happen, but in case it does just replicate the labels.
weakenEnv :: LeftHandSide s v env env' -> BuffersTup v -> BuffersEnv env -> State EnvLabel (BuffersEnv env')
weakenEnv LeftHandSideWildcard{} _                  = pure
weakenEnv LeftHandSideSingle{}   bs                 = \lenv -> freshE' >>= \e -> return ((e, bs) :>>: lenv)
weakenEnv (LeftHandSidePair l r) (TupFpair lbs rbs) = weakenEnv l lbs >=> weakenEnv r rbs
weakenEnv (LeftHandSidePair _ _) _ = error "consLHS: Inaccesible left-hand side."



--------------------------------------------------------------------------------
-- Bound left-hand side
--------------------------------------------------------------------------------

-- | A 'LeftHandSide' with the values bound at its leaves.
data BoundLHS s v env env' where
  BoundLHSsingle
    :: EnvLabels v
    -> s v
    -> BoundLHS s v env (env, v)

  BoundLHSwildcard
    :: TupR s v
    -> BoundLHS s v env env

  BoundLHSpair
    :: BoundLHS s v1       env  env'
    -> BoundLHS s v2       env' env''
    -> BoundLHS s (v1, v2) env  env''

instance Show (BoundLHS s v env env') where
  show :: BoundLHS s v env env' -> String
  show (BoundLHSsingle e _) = "BLHS(" ++ show e ++ ")"
  show (BoundLHSwildcard _) = "BLHS_"
  show (BoundLHSpair l r)   = "BLHS(" ++ show l ++ ", " ++ show r ++ ")"

type BoundGLHS = BoundLHS GroundR

-- | Get bindings from the environment and bind them to the left-hand side.
bindLHS :: LeftHandSide s v env env' -> BuffersEnv env' -> BoundLHS s v env env'
bindLHS (LeftHandSideSingle sv) (l :>>: _) = BoundLHSsingle l sv
bindLHS (LeftHandSideWildcard tr) _ = BoundLHSwildcard tr
bindLHS (LeftHandSidePair l r) env = BoundLHSpair (bindLHS l (stripLHS r env)) (bindLHS r env)

-- | Remove values bound by the left-hand side from the environment.
stripLHS :: LeftHandSide s v env env' -> BuffersEnv env' -> BuffersEnv env
stripLHS (LeftHandSideSingle _) (_ :>>: le') = le'
stripLHS (LeftHandSideWildcard _) le = le
stripLHS (LeftHandSidePair l r) le = stripLHS l (stripLHS r le)

createLHS :: BoundLHS s v _env _env'
          -> BuffersEnv env
          -> (forall env'. BuffersEnv env' -> LeftHandSide s v env env' -> r)
          -> r
createLHS (BoundLHSsingle e sv) env k = k (e :>>: env) (LeftHandSideSingle sv)
createLHS (BoundLHSwildcard tr) env k = k env (LeftHandSideWildcard tr)
createLHS (BoundLHSpair l r)    env k =
  createLHS   l env  $ \env'  l' ->
    createLHS r env' $ \env'' r' ->
      k env'' (LeftHandSidePair l' r')



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

-- | A label to be stored with an argument, indicating whether an argument is an
--   array or not, and if so, which buffers it is associated with as a 'TupF'.
data ArgIsArray t where
  -- | The argument is an array.
  Arr :: EnvLabelTup e  -- ^ The array (as structure-of-arrays).
      -> ArgIsArray (m sh e)
  -- | The argument is a scalar 'Var'', 'Exp'' or 'Fun''.
  NotArr :: ArgIsArray (t e)

deriving instance Show (ArgIsArray t)

-- | An 'ArgIsArray', all dependencies of the argument, and all shape
--   dependencies of the argument.
--
-- The first set of buffers contains all dependencies of the argument.
-- The second set of buffers contains only those dependencies that represent
-- the shape of the argument.
-- This means that the second set of buffers is a subset of the first set of
-- buffers.
type ArgLabels t = (ArgIsArray t, Labels Buff, Labels Buff)

-- | The argument to a function paired with 'ArgLabels'
data LabelledArg env t = L (Arg env t) (ArgLabels t)
  deriving (Show)

-- | Labelled arguments to be passed to a function.
type LabelledArgs env = PreArgs (LabelledArg env)

-- | Label the arguments to a function using the given environment.
labelArgs :: Args env args -> BuffersEnv env -> LabelledArgs env args
labelArgs ArgsNil _ = ArgsNil
labelArgs (arg :>: args) env =
  L arg (getArgLabels arg env) :>: labelArgs args env

-- | Get the 'ArgLabels' associated with 'Arg' from 'BuffersEnv'.
getArgLabels :: Arg env t -> BuffersEnv env -> ArgLabels t
getArgLabels (ArgVar vars) env = (NotArr, getVarsDeps vars env, mempty)
getArgLabels (ArgExp exp)  env = (NotArr, getExpDeps  exp  env, mempty)
getArgLabels (ArgFun fun)  env = (NotArr, getFunDeps  fun  env, mempty)
getArgLabels (ArgArray _ (ArrayR _ tp) sh arr) env
  | (_     , fold ->  sh_bs) <- getVarsFromEnv sh  env
  , (arr_es, fold -> arr_bs) <- getVarsFromEnv arr env
  = (unbuffers tp arr_es, arr_bs <> sh_bs, sh_bs)

-- | Get the values associated with 'Vars' from 'BuffersEnv'.
getVarsFromEnv :: Vars a env b -> BuffersEnv env -> (ArgIsArray (m sh b), BuffersTup b)
getVarsFromEnv TupRunit         _   = (Arr TupFunit, TupFunit)
getVarsFromEnv (TupRsingle var) env = getVarFromEnv var env
getVarsFromEnv (TupRpair l r)   env | (Arr l', bs1) <- getVarsFromEnv l env
                                    , (Arr r', bs2) <- getVarsFromEnv r env
                                    = (Arr (TupFpair l' r'), TupFpair bs1 bs2)
getVarsFromEnv _ _ = error "getVarsFromEnv: Inaccessible left-hand side."

-- | Get the value associated with a 'Var' from 'BuffersEnv'.
getVarFromEnv :: Var a env b -> BuffersEnv env -> (ArgIsArray (m sh b), BuffersTup b)
getVarFromEnv (varIdx -> idx) = first (Arr . TupFsingle) . lookupIdxInEnv idx

-- | Get the value associated with an 'Idx' from 'BuffersEnv'.
lookupIdxInEnv :: Idx env a -> BuffersEnv env -> (EnvLabel, BuffersTup a)
lookupIdxInEnv ZeroIdx       (bs :>>: _)   = bs
lookupIdxInEnv (SuccIdx idx) (_  :>>: env) = lookupIdxInEnv idx env


-- | Get the dependencies of a tuple of variables.
getVarsDeps :: Vars s env t -> BuffersEnv env -> Labels Buff
getVarsDeps vars = fold . snd . getVarsFromEnv vars

-- | Get the dependencies of a tuple of variables.
getVarDeps :: Var s env t -> BuffersEnv env -> Labels Buff
getVarDeps var = fold . snd . getVarFromEnv var

-- | Get the dependencies of an expression.
getExpDeps :: OpenExp x env y -> BuffersEnv env -> Labels Buff
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
getFunDeps :: OpenFun x env y -> BuffersEnv env -> Labels Buff
getFunDeps (Body  poe) env = getExpDeps poe env
getFunDeps (Lam _ fun) env = getFunDeps fun env

-- | Remove the 'Buffers' type from 'ArgIsArray'.
unbuffers :: forall m sh e. TypeR e -> ArgIsArray (m sh (Buffers e)) -> ArgIsArray (m sh e)
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
mapLEnv :: (forall t. BuffersTup t -> BuffersTup t) -> BuffersEnv env -> BuffersEnv env
mapLEnv _ EnvNil = EnvNil
mapLEnv f ((e, bs) :>>: env) = (e, f bs) :>>: mapLEnv f env

-- | Fold over the labels in the environment.
foldMapLEnv :: Monoid m => (forall t. BuffersTup t -> m) -> BuffersEnv env -> m
foldMapLEnv _ EnvNil = mempty
foldMapLEnv f ((_, bs) :>>: env) = f bs <> foldMapLEnv f env

-- | Map a monadic function over the labels in the environment.
mapLEnvM :: Monad m => (forall t. BuffersTup t -> m (BuffersTup t)) -> BuffersEnv env -> m (BuffersEnv env)
mapLEnvM _ EnvNil = return EnvNil
mapLEnvM f ((e, bs) :>>: env) = do
  bs'  <- f bs
  env' <- mapLEnvM f env
  return ((e, bs') :>>: env')

-- | Flipped version of 'mapLEnvM'.
forLEnvM :: Monad m => BuffersEnv env -> (forall t. BuffersTup t -> m (BuffersTup t)) -> m (BuffersEnv env)
forLEnvM env f = mapLEnvM f env
{-# INLINE forLEnvM #-}

-- | Map a monadic action over the labels in the environment and discard the result.
mapLEnvM_ :: Monad m => (forall t. BuffersTup t -> m ()) -> BuffersEnv env -> m ()
mapLEnvM_ _ EnvNil = return ()
mapLEnvM_ f ((_, bs) :>>: env) = f bs >> mapLEnvM_ f env

-- | Flipped version of 'mapLEnvM_'.
forLEnvM_ :: Monad m => BuffersEnv env -> (forall t. BuffersTup t -> m ()) -> m ()
forLEnvM_ env f = mapLEnvM_ f env
{-# INLINE forLEnvM_ #-}

-- | Traverse over the labels in the environment.
traverseLEnv :: Applicative f => (forall t. BuffersTup t -> f (BuffersTup t)) -> BuffersEnv env -> f (BuffersEnv env)
traverseLEnv _ EnvNil = pure EnvNil
traverseLEnv f ((e, bs) :>>: env) = ((:>>:) . (e,) <$> f bs) <*> traverseLEnv f env

-- | Flipped version of 'traverseLEnv'.
forLEnv :: Applicative f => BuffersEnv env -> (forall t. BuffersTup t -> f (BuffersTup t)) -> f (BuffersEnv env)
forLEnv env f = traverseLEnv f env
{-# INLINE forLEnv #-}

-- | Traverse over the labels in the environment and discard the result.
traverseLEnv_ :: Applicative f => (forall t. BuffersTup t -> f ()) -> BuffersEnv env -> f ()
traverseLEnv_ _ EnvNil = pure ()
traverseLEnv_ f ((_, bs) :>>: env) = f bs *> traverseLEnv_ f env

-- | Flipped version of 'traverseLEnv_'.
forLEnv_ :: Applicative f => BuffersEnv env -> (forall t. BuffersTup t -> f ()) -> f ()
forLEnv_ env f = traverseLEnv_ f env
{-# INLINE forLEnv_ #-}



--------------------------------------------------------------------------------
-- Helpers for Labelled Arguments
--------------------------------------------------------------------------------

-- | Map a function over the labelled arguments.
mapLArgs :: (forall s. LabelledArg env s -> LabelledArg env s) -> LabelledArgs env t -> LabelledArgs env t
mapLArgs _ ArgsNil = ArgsNil
mapLArgs f (larg :>: largs) = f larg :>: mapLArgs f largs

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

-- | Traverse over the labelled arguments.
traverseLArgs :: Applicative f => (forall s. LabelledArg env s -> f (LabelledArg env s)) -> LabelledArgs env t -> f (LabelledArgs env t)
traverseLArgs _ ArgsNil = pure ArgsNil
traverseLArgs f (larg :>: largs) = (:>:) <$> f larg <*> traverseLArgs f largs

-- | Flipped version of 'traverseLArgs'.
forLArgsT :: Applicative f => LabelledArgs env t -> (forall s. LabelledArg env s -> f (LabelledArg env s)) -> f (LabelledArgs env t)
forLArgsT largs f = traverseLArgs f largs
{-# INLINE forLArgsT #-}

-- | Traverse over the labelled arguments and discard the result.
traverseLArgs_ :: Applicative f => (forall s. LabelledArg env s -> f ()) -> LabelledArgs env t -> f ()
traverseLArgs_ _ ArgsNil = pure ()
traverseLArgs_ f (larg :>: largs) = f larg *> traverseLArgs_ f largs

-- | Flipped version of 'traverseLArgs_'.
forLArgs_ :: Applicative f => LabelledArgs env t -> (forall s. LabelledArg env s -> f ()) -> f ()
forLArgs_ largs f = traverseLArgs_ f largs
{-# INLINE forLArgs_ #-}

-- | All arrays that the function reads from. This includes the shapes.
inputArrays :: LabelledArgs env t -> Labels Buff
inputArrays = foldMapLArgs \case
  L (ArgArray In  _ _ _) (Arr _, deps,  _) -> deps
  L (ArgArray Mut _ _ _) (Arr _, deps,  _) -> deps
  L (ArgArray Out _ _ _) (Arr _,    _, sh) -> sh
  _ -> mempty

-- | All arrays that the function writes to. This does not include the shapes.
outputArrays :: LabelledArgs env t -> Labels Buff
outputArrays = foldMapLArgs \case
  L (ArgArray Out _ _ _) (Arr _, deps, sh) -> deps S.\\ sh
  L (ArgArray Mut _ _ _) (Arr _, deps, sh) -> deps S.\\ sh
  _ -> mempty

-- | All arguments that are not arrays.
notArrays :: LabelledArgs env t -> Labels Buff
notArrays = foldMapLArgs \case
  L _ (NotArr, bs, _) -> bs
  _ -> mempty



--------------------------------------------------------------------------------
-- Debugging
--------------------------------------------------------------------------------

-- | Trace a value using a function to format the output.
traceWith :: (Show a) => (a -> String) -> a -> a
traceWith f x = trace (f x) x
{-# INLINE traceWith #-}
