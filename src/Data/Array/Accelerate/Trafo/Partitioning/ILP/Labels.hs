{-
Module      : Data.Array.Accelerate.Trafo.Partitioning.ILP.LabelsNew
Description : Nodes representing nodes in the graph.

This module provides the labels that represent nodes in the graph. A node can
either be a computation or a buffer.
-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
module Data.Array.Accelerate.Trafo.Partitioning.ILP.Labels where

import Data.Array.Accelerate.AST.Idx
import Data.Array.Accelerate.AST.IdxSet (IdxSet)
import qualified Data.Array.Accelerate.AST.IdxSet as IdxSet
import Data.Array.Accelerate.AST.LeftHandSide
import Data.Array.Accelerate.AST.Operation
import Data.Array.Accelerate.Error
import Data.Array.Accelerate.Array.Buffer
import Data.Array.Accelerate.Representation.Type

import Lens.Micro
import Lens.Micro.Mtl

import Data.Set (Set)
import qualified Data.Set as S

import Data.Hashable (Hashable, hashWithSalt)
import Prelude hiding (exp)

import qualified Data.Functor.Const as C
import Data.Coerce
import Control.Monad.State.Strict
import Data.Maybe (fromJust)
import Data.List ( intercalate )
import Debug.Trace
import Data.Array.Accelerate.Analysis.Match
import Data.Array.Accelerate.Representation.Ground (groundRelt)
import qualified Data.Array.Accelerate.Pretty.Operation as P
import qualified Data.Array.Accelerate.Pretty.Exp as P
import Data.String (fromString)
import Control.Monad


--------------------------------------------------------------------------------
-- Nodes
--------------------------------------------------------------------------------

data Comp  -- ^ The type of computation nodes.
data GVal  -- ^ The type of ground value nodes.


-- | Nodes for referencing nodes.
data Node t where
  Node :: Int      -- ^ The computation node.
       -> Parent   -- ^ The parent computation.
       -> Node t


-- | The parent of a node is either 'Nothing' (the root node) or 'Just' (a parent computation).
-- Parent nodes are set when a computation is nested within for instance an Acond or Awhile.
-- See the use of 'zoom (scope ...)' in Graph.hs
type Parent = Maybe (Node Comp)


-- | Lens for getting and setting the nodes unique identifier.
nodeId :: Lens' (Node t) Int
nodeId f (Node i p) = f i <&> (`Node` p)


-- | Lens for getting and setting the parent node.
parent :: Lens' (Node t) Parent
parent f (Node i p) = f p <&> Node i


-- | Lens for setting and unsafely getting the parent.
parent' :: Lens' (Node t) (Node Comp)
parent' f (Node i p) = f (fromJust p) <&> (Node i . Just)


-- | Lens for interpreting any node as a computation node.
asComp :: Lens' (Node t) (Node Comp)
asComp f l = coerce <$> f (coerce l)


-- | Lens for interpreting any node as a buffer node.
asBuff :: Lens' (Node t) (Node GVal)
asBuff f l = coerce <$> f (coerce l)

instance Show (Node Comp) where
  show :: Node Comp -> String
  show c = "C" ++ intercalate "." (map show . reverse $ nodeIds c)

instance Show (Node GVal) where
  show :: Node GVal -> String
  show b = "B" ++ intercalate "." (map show . reverse $ nodeIds b)


nodeIds :: Node t -> [Int]
nodeIds l = l^.nodeId : maybe [] nodeIds (l^.parent)


instance Eq (Node t) where
  (==) :: Node t -> Node t -> Bool
  (==) l1 l2 = (l1^.nodeId == l2^.nodeId) && checkMismatch (l1^.parent) (l2^.parent) True


instance Ord (Node t) where
  compare :: Node t -> Node t -> Ordering
  compare l1 l2 = case compare (l1^.nodeId) (l2^.nodeId) of
    EQ  -> checkMismatch (l1^.parent) (l2^.parent) EQ
    ord -> ord


-- | Checks if two parents are equal and throw an error if they are not.
checkMismatch :: Parent -> Parent -> a -> a
checkMismatch (Just l1) (Just l2) | l1 == l2 = id
checkMismatch Nothing Nothing = id
checkMismatch _ _ = internalError "mismatching nodes"


instance Hashable (Node t) where
  hashWithSalt :: Int -> Node t -> Int
  hashWithSalt s l = hashWithSalt s (l^.nodeId)


-- | Compute the nesting level of a 'Node'.
level :: Node t -> Int
level n = case n^.parent of
  Nothing -> 0
  Just p  -> 1 + level p


-- | Compute the ancestry tree of a 'Node', staring with the ancestor underneath the root.
ancestree :: Node Comp -> [Node Comp]
ancestree n = ancestree' [n] n


-- | Helper function for 'ancestree'.
ancestree' :: [Node Comp] -> Node t -> [Node Comp]
ancestree' ps n = case n^.parent of
  Nothing -> ps
  Just p  -> ancestree' (p:ps) p


-- | Compute the difference between the 'ancestree's of two 'Node's.
difftree :: Node Comp -> Node Comp -> ([Node Comp], [Node Comp])
difftree n1 n2 = difftree' (ancestree n1) (ancestree n2)


-- | Compute the difference between two 'ancestree's.
difftree' :: [Node Comp] -> [Node Comp] -> ([Node Comp], [Node Comp])
difftree' (x:xs) (y:ys) | x == y = difftree' xs ys
difftree' xs ys = (xs, ys)


-- | The first nodes in the 'ancestree's of the two 'Node's that differ, which
--   may be one or both of the original 'Node's, but always two different 'Node's.
ancestors :: Node Comp -> Node Comp -> Maybe (Node Comp, Node Comp)
ancestors n1 n2 = case ancestors' n1 n2 of
  (a1, a2) | a1 /= a2  -> Just (a1, a2)
           | otherwise -> Nothing


-- | The first nodes in the 'ancestree's of the two 'Node's that differ, which
--   may be one or both of the original 'Node's.
ancestors' :: Node Comp -> Node Comp -> (Node Comp, Node Comp)
ancestors' n1 n2 = if n1^.parent == n2^.parent then (n1, n2)
  else case compare (level n1) (level n2) of
    LT -> ancestors'  n1           (n2^.parent')
    GT -> ancestors' (n1^.parent')  n2
    EQ -> ancestors' (n1^.parent') (n2^.parent')


-- | Create a fresh 'Node'.
freshL' :: State (Node t) (Node t)
freshL' = id <%= (nodeId +~ 1)


-- | Set of 'Node's.
type Nodes t = Set (Node t)

type ReadEdge      = (Node GVal, Node Comp)
type WriteEdge     = (Node Comp, Node GVal)
type StrictEdge    = (Node Comp, Node Comp)
type DataflowEdge  = (Node Comp, Node GVal, Node Comp)
type FusibleEdge   = DataflowEdge
type InfusibleEdge = DataflowEdge
type InplacePath   = (ReadEdge, WriteEdge)

-- | A value consists of its type @s t@ and and the 'Node' that represents it.
data Val s t = Val
  { valType :: s t -- Type is needed to make mkReindexPartial safe
  , valNode :: Node GVal
  }

-- TODO: Remove this function, and let all callers directly work with a single
-- Node instead of a Set
valNodes :: Val s t -> Nodes GVal
valNodes (Val _ n) = S.singleton n

-- | A 'TupR' of 'Val's.
type Vals s = TupR (Val s)


-- | The type of ground values.
type GroundVal = Val GroundR


-- | A 'TupR' of 'GroundVal's.
type GroundVals = Vals GroundR


val :: s t -> Node GVal -> Val s t
val t n = Val t n


-- | Get the nodes of 'Vals'.
valsNodes :: Vals s t -> Nodes GVal
valsNodes = foldMapTupR valNodes


-- | Get the type of 'Vals'.
valsType :: Vals s t -> TupR s t
valsType = mapTupR valType


-- | Match the types of two 'GroundVals'.
matchGroundValsType :: GroundVals s -> GroundVals t -> Maybe (s :~: t)
matchGroundValsType = matchTupR matchGroundValType


-- | Match the types of two 'GroundVal's.
matchGroundValType :: GroundVal s -> GroundVal t -> Maybe (s :~: t)
matchGroundValType (Val t1 _) (Val t2 _) = matchGroundR t1 t2


-- | Expect 'GroundVals' of the given type.
expectGroundVals :: HasCallStack => GroundsR t -> Exists GroundVals -> GroundVals t
expectGroundVals repr (Exists vals)
  | Just Refl <- matchGroundsR repr (groundsR vals) = vals
  | otherwise = internalError $ fromString $
      "Result of lambda has unexpected type.\nExpected: "
      ++ show (P.prettyTupR (const P.prettyGroundR) 0 repr)
      ++ "\nActual: "
      ++ show (P.prettyTupR (const P.prettyGroundR) 0 $ groundsR vals)


instance HasGroundsR GroundVals where
  groundsR :: GroundVals a -> GroundsR a
  groundsR = valsType


instance HasGroundsR GroundVal where
  groundsR :: GroundVal a -> GroundsR a
  groundsR (Val tp _) = TupRsingle tp


instance Eq (Val s t) where
  (==) :: Val s t -> Val s t -> Bool
  (==) (Val _ n1) (Val _ n2) = n1 == n2

instance Show (Val s t) where
  show :: Val s t -> String
  show (Val _ n) = "Val " ++ show n


--------------------------------------------------------------------------------
-- Labelled Environment
--------------------------------------------------------------------------------

-- | An 'EnvLabel' uniquely identifies an element of the environment.
newtype EnvLabel = EnvLabel Int
  deriving (Eq, Ord, Show, Num)


-- | A 'TupR' of 'EnvLabel'.
type EnvLabels = TupR (C.Const EnvLabel)


-- | Create a fresh 'EnvLabel' from the current state.
freshE' :: State EnvLabel EnvLabel
freshE' = id <%= (+1)


-- | An environment value consists of a unique 'EnvLabel', the stored 'GroundVals'
--   and the 'Uniquenesses' of the stored values.
type EnvVal t = (EnvLabel, GroundVals t, Uniquenesses t)


-- | A collection of multiple 'EnvVal's. Individual elements can be accessed by
--   pattern matching on 'EnvLabels'.
type EnvVals t = (EnvLabels t, GroundVals t, Uniquenesses t)


-- | The environment used during graph construction.
data Env env where
  -- | The empty environment.
  EnvNil :: Env ()
  -- | The non-empty environment.
  (:>>:) :: EnvVal t  -- ^ See 'EnvVal'.
         -> Env env   -- ^ The rest of the environment.
         -> Env (env, t)


instance Show (Env env) where
  show :: Env env -> String
  show EnvNil = "EnvNil"
  show (envl :>>: env) = show envl ++ " :>>: " ++ show env


-- | Constructs a new 'Env' by prepending labels for each element in the left-hand side.
weakenEnv :: LeftHandSide s v env env' -> GroundVals v -> Uniquenesses v -> Env env -> State EnvLabel (Env env')
weakenEnv LeftHandSideWildcard{} _ _ = pure
weakenEnv LeftHandSideSingle{} bs us = \lenv -> freshE' >>= \e -> return ((e, bs, us) :>>: lenv)
weakenEnv (LeftHandSidePair l r) (TupRpair lbs rbs) (TupRpair lus rus) = weakenEnv l lbs lus >=> weakenEnv r rbs rus
weakenEnv (LeftHandSidePair _ _) _ _ = internalError "mismatching left-hand side"


-- | Look up 'Vars' in 'Env', returing 'EnvVals'.
lookupVars :: Vars a env b -> Env env -> EnvVals b
lookupVars TupRunit         _   = (TupRunit, TupRunit, TupRunit)
lookupVars (TupRsingle var) env | (e, bs, u) <- lookupVar var env
                                    = (TupRsingle (C.Const e), bs, u)
lookupVars (TupRpair l r)   env | (el, bsl, ul) <- lookupVars l env
                                    , (er, bsr, ur) <- lookupVars r env
                                    = (TupRpair el er, TupRpair bsl bsr, TupRpair ul ur)


-- | Look up a 'Var' in 'Env', returning an 'EnvVal'.
lookupVar :: Var a env b -> Env env -> EnvVal b
lookupVar = lookupIdx . varIdx


-- | Look up an 'Idx' in 'Env', returning an 'EnvVal'.
lookupIdx :: Idx env t -> Env env -> EnvVal t
lookupIdx ZeroIdx       (bs :>>: _)   = bs
lookupIdx (SuccIdx idx) (_  :>>: env) = lookupIdx idx env



--------------------------------------------------------------------------------
-- Bound left-hand side
--------------------------------------------------------------------------------

-- | A 'LeftHandSide' and the 'EnvVal' bound by it.
data BoundLHS s v env env' where
  BoundLHSsingle
    :: EnvVal v
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


-- | The type of left-hand sides binding ground values.
type BoundGLHS = BoundLHS GroundR


-- | Bind values to the 'LeftHandSide' that produced the 'Env'
bindLHS :: LeftHandSide s v env env' -> Env env' -> BoundLHS s v env env'
bindLHS (LeftHandSideSingle sv) (l :>>: _) = BoundLHSsingle l sv
bindLHS (LeftHandSideWildcard tr) _ = BoundLHSwildcard tr
bindLHS (LeftHandSidePair l r) env = BoundLHSpair (bindLHS l (stripLHS r env)) (bindLHS r env)


-- | Unbind values from the 'BoundLHS'.
unbindLHS :: BoundLHS s v env env' -> LeftHandSide s v env env'
unbindLHS (BoundLHSsingle _ sv) = LeftHandSideSingle sv
unbindLHS (BoundLHSwildcard tr) = LeftHandSideWildcard tr
unbindLHS (BoundLHSpair l r)    = LeftHandSidePair (unbindLHS l) (unbindLHS r)


-- | Strip the values bound by the 'LeftHandSide' from the 'Env'.
stripLHS :: LeftHandSide s v env env' -> Env env' -> Env env
stripLHS (LeftHandSideSingle _) (_ :>>: le') = le'
stripLHS (LeftHandSideWildcard _) le = le
stripLHS (LeftHandSidePair l r) le = stripLHS l (stripLHS r le)


createLHS :: BoundLHS s v _env _env'
          -> Env env
          -> (forall env'. Env env' -> LeftHandSide s v env env' -> r)
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

-- | A label to add to function arguments.
--
-- If the argument is an array, then we need all information about the array and its
-- shape from the environment.
-- If the argument is not an array, e.g. a scalar, function or expression, then we only
-- need 'Node's referenced by the scalar, function or expression.
data ArgLabel t where
  -- | The argument is an array.
  Arr     :: EnvVals (Buffers e)  -- ^ The array values.
          -> EnvVals sh           -- ^ The shape values.
          -> ArgLabel (m sh e)
  -- | The argument is a scalar 'Var'', 'Exp'' or 'Fun''.
  NotArr  :: Nodes GVal  -- ^ The variables referenced by the argument.
          -> ArgLabel (t e)

deriving instance Show (ArgLabel t)


-- | Get the set of dependent buffers of an 'ArgLabel'.
getLabelDeps :: ArgLabel t -> Nodes GVal
getLabelDeps (Arr (_, arr, _) (_, sh, _)) = valsNodes arr <> valsNodes sh
getLabelDeps (NotArr deps) = deps


-- | Get the set of unique array dependencies of an 'ArgLabel'.
getLabelUniqueArrDeps :: ArgLabel t -> Nodes GVal
getLabelUniqueArrDeps (Arr (_, arr, u) _) = uniqueNodes u arr
getLabelUniqueArrDeps (NotArr _) = internalError "getLabelUniqueArrDeps: Expected Arr but got NotArr"


-- | Given 'Uniquenesses', get the unique nodes from 'GroundVals'.
uniqueNodes :: Uniquenesses e -> GroundVals e -> Nodes GVal
uniqueNodes TupRunit TupRunit      = mempty
uniqueNodes (TupRsingle Shared) _  = mempty
uniqueNodes (TupRsingle Unique) bs = valsNodes bs
uniqueNodes (TupRpair ul ur) (TupRpair l r) = uniqueNodes ul l <> uniqueNodes ur r
uniqueNodes _ _ = internalError "uniqueNodes: Tuple mismatch "


-- | Get the arrays of an 'ArgLabel'.
getLabelArrays :: ArgLabel (m sh e) -> GroundVals (Buffers e)
getLabelArrays (Arr (_, arr, _) (_, _, _)) = arr
getLabelArrays (NotArr _) = internalError "getLabelArrays: Expected Arr but got NotArr"


-- | Get the array dependencies of an 'ArgLabel'.
getLabelArrDeps :: ArgLabel (m sh e) -> Nodes GVal
getLabelArrDeps = valsNodes . getLabelArrays


-- | Get a single array dependency of an 'ArgLabel'.
getLabelArrDep :: ArgLabel (m sh e) -> Node GVal
getLabelArrDep = foldr1 const . getLabelArrDeps


-- | Get the shapes of an 'ArgLabel'.
getLabelShape :: ArgLabel (m sh e) -> GroundVals sh
getLabelShape (Arr (_, _, _) (_, sh, _)) = sh
getLabelShape (NotArr _) = internalError "getLabelShape: Expected Arr but got NotArr"


-- | Get the shape dependencies of an 'ArgLabel'.
getLabelShDeps :: ArgLabel (m sh e) -> Nodes GVal
getLabelShDeps = valsNodes . getLabelShape


-- | Check if two arguments have the same shape.
sameShape :: ArgLabel (m1 sh1 e1) -> ArgLabel (m2 sh2 e2) -> Bool
sameShape (getLabelShape -> sh1) (getLabelShape -> sh2)
  | Just Refl <- matchGroundValsType sh1 sh2 = sh1 == sh2
  | otherwise = False


-- | The argument to a function paired with an 'ArgLabel'
data LabelledArg env t = L (Arg env t) (ArgLabel t)
  deriving (Show)


-- | Arguments to a function paired with their 'ArgLabel's.
type LabelledArgs env = PreArgs (LabelledArg env)


-- | Node the arguments to a function using the given environment.
labelArgs :: Args env args -> Env env -> LabelledArgs env args
labelArgs (arg :>: args) env = labelArg arg env :>: labelArgs args env
labelArgs ArgsNil _ = ArgsNil


-- | Get the 'ArgLabels' associated with 'Arg' from 'Env'.
labelArg :: Arg env t -> Env env -> LabelledArg env t
labelArg arg env = L arg $ case arg of
  (ArgVar vars) -> NotArr $ getVarsDeps vars env
  (ArgExp exp)  -> NotArr $ getExpDeps  exp  env
  (ArgFun fun)  -> NotArr $ getFunDeps  fun  env
  (ArgArray _ _ sh arr) ->
    Arr (lookupVars arr env) (lookupVars sh env)



-- | Get the dependencies of a tuple of variables.
getVarsDeps :: Vars s env t -> Env env -> Nodes GVal
getVarsDeps vars = valsNodes . (^._2) . lookupVars vars


-- | Get the dependencies of a variable.
getVarDeps :: Var s env t -> Env env -> Nodes GVal
getVarDeps var = valsNodes . (^._2) . lookupVar var

-- | Get the dependencies, given the index of a variable.
getIdxDeps :: Idx env t -> Env env -> Nodes GVal
getIdxDeps idx = valsNodes . (^._2) . lookupIdx idx

-- | Get the dependencies of a set of indices.
getIdxSetDeps :: IdxSet env -> Env env -> Nodes GVal
getIdxSetDeps deps env = mconcat $ map (\(Exists idx) -> getIdxDeps idx env) $ IdxSet.toList deps


-- | Get the dependencies of an expression.
getExpDeps :: OpenExp x env y -> Env env -> Nodes GVal
getExpDeps (ArrayInstr (Index     var) poe) env = getVarDeps var  env <> getExpDeps poe  env
getExpDeps (ArrayInstr (Parameter var) poe) env = getVarDeps var  env <> getExpDeps poe  env
getExpDeps (Let _ poe1 poe2)                env = getExpDeps poe1 env <> getExpDeps poe2 env
getExpDeps (Evar _)                         _   = mempty
getExpDeps  Foreign{}                       _   = mempty
getExpDeps (Pair  poe1 poe2)                env = getExpDeps poe1 env <> getExpDeps poe2 env
getExpDeps  Nil                             _   = mempty
getExpDeps (VecPack _ poe)                  env = getExpDeps poe  env
getExpDeps (VecUnpack _ poe)                env = getExpDeps poe  env
getExpDeps (ToIndex    _ poe1 poe2)         env = getExpDeps poe1 env <> getExpDeps poe2 env
getExpDeps (FromIndex  _ poe1 poe2)         env = getExpDeps poe1 env <> getExpDeps poe2 env
getExpDeps (Case poe1 poes poe2)            env = getExpDeps poe1 env <>
                                                  foldMap ((`getExpDeps` env) . snd) poes <>
                                                  maybe mempty (`getExpDeps` env) poe2
getExpDeps (Cond poe1 poe2 exp3)            env = getExpDeps poe1 env <>
                                                  getExpDeps poe2 env <>
                                                  getExpDeps exp3 env
getExpDeps (Select poe1 poe2 exp3)          env = getExpDeps poe1 env <>
                                                  getExpDeps poe2 env <>
                                                  getExpDeps exp3 env
getExpDeps (While pof1 pof2 poe)            env = getFunDeps pof1 env <>
                                                  getFunDeps pof2 env <>
                                                  getExpDeps poe  env
getExpDeps (Const _ _)                      _   = mempty
getExpDeps (PrimApp   _ poe)                env = getExpDeps poe  env
getExpDeps (ShapeSize _ poe)                env = getExpDeps poe  env
getExpDeps (Undef _)                        _   = mempty
getExpDeps  Coerce{}                        _   = mempty
getExpDeps (Assert _ g e)                   env = getExpDeps g env <> getExpDeps e env
getExpDeps (Assume g e)                     env = getExpDeps g env <> getExpDeps e env


-- | Get the dependencies of a function.
getFunDeps :: OpenFun x env y -> Env env -> Nodes GVal
getFunDeps (Body  poe) env = getExpDeps poe env
getFunDeps (Lam _ fun) env = getFunDeps fun env



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
forLArgs :: Applicative f => LabelledArgs env t -> (forall s. LabelledArg env s -> f (LabelledArg env s)) -> f (LabelledArgs env t)
forLArgs largs f = traverseLArgs f largs
{-# INLINE forLArgs #-}

-- | Traverse over the labelled arguments and discard the result.
traverseLArgs_ :: Applicative f => (forall s. LabelledArg env s -> f ()) -> LabelledArgs env t -> f ()
traverseLArgs_ _ ArgsNil = pure ()
traverseLArgs_ f (larg :>: largs) = f larg *> traverseLArgs_ f largs

-- | Flipped version of 'traverseLArgs_'.
forLArgs_ :: Applicative f => LabelledArgs env t -> (forall s. LabelledArg env s -> f ()) -> f ()
forLArgs_ largs f = traverseLArgs_ f largs
{-# INLINE forLArgs_ #-}

-- | All arrays that the function reads from.
inputArrays :: LabelledArgs env t -> Nodes GVal
inputArrays = foldMapLArgs \case
  L (ArgArray In  _ _ _) (Arr (_,arr,_) _) -> valsNodes arr
  L (ArgArray Mut _ _ _) (Arr (_,arr,_) _) -> valsNodes arr
  _ -> mempty

-- | All arrays that the function writes to.
outputArrays :: LabelledArgs env t -> Nodes GVal
outputArrays = foldMapLArgs \case
  L (ArgArray Out _ _ _) (Arr (_,arr,_) _) -> valsNodes arr
  L (ArgArray Mut _ _ _) (Arr (_,arr,_) _) -> valsNodes arr
  _ -> mempty

-- | All non-array arguments and array shapes.
notArrays :: LabelledArgs env t -> Nodes GVal
notArrays = foldMapLArgs \case
  L _ (Arr _ (_,sh,_)) -> valsNodes sh
  L _ (NotArr deps)    -> deps

-- | Fold map over all inputs.
foldMapInputLabels :: Monoid m => (forall sh e. ArgLabel (In sh e) -> m) -> LabelledArgs env t -> m
foldMapInputLabels f = foldMapLArgs \case
  L (ArgArray In _ _ _) l -> f l
  _ -> mempty

-- | Fold map over all outputs.
foldMapOutputLabels :: Monoid m => (forall sh e. ArgLabel (Out sh e) -> m) -> LabelledArgs env t -> m
foldMapOutputLabels f = foldMapLArgs \case
  L (ArgArray Out _ _ _) l -> f l
  _ -> mempty



--------------------------------------------------------------------------------
-- Debugging
--------------------------------------------------------------------------------

-- | Trace a value using a function to format the output.
traceWith :: (Show a) => (a -> String) -> a -> a
traceWith f x = trace (f x) x
{-# INLINE traceWith #-}
