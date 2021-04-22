{-# LANGUAGE BangPatterns          #-}
{-# LANGUAGE EmptyCase             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# OPTIONS_HADDOCK hide #-}
-- |
-- Module      : Data.Array.Accelerate.AST.Operation
-- Copyright   : [2008..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.AST.Operation (
  PreOpenAcc(..), PreOpenAfun(..),
  OperationAcc, OperationAfun,
  Uniqueness(..), Uniquenesses, shared,

  GroundR(..), GroundsR, GroundVar, GroundVars, GLeftHandSide, Var(..), Vars,
  HasGroundsR(..), groundToExpVar,

  PreArgs(..), Arg(..), Args, Modifier(..), argArrayR, argVarType,

  Var', Exp', Fun', In, Out, Mut,

  OpenExp, OpenFun, Exp, Fun, ArrayInstr(..),
  expGroundVars, funGroundVars, arrayInstrsInExp, arrayInstrsInFun,

  encodeGroundR, encodeGroundsR, encodeGroundVar, encodeGroundVars,
  rnfGroundR, rnfGroundsR, rnfGroundVar, rnfGroundVars,
  liftGroundR, liftGroundsR, liftGroundVar, liftGroundVars,

  bufferImpossible, groundFunctionImpossible,

  paramIn, paramsIn, paramIn', paramsIn',

  ReindexPartial, reindexArg, reindexArgs, reindexExp, reindexVar, reindexVars,
  weakenReindex,
  argVars, argsVars, AccessGroundR(..),

  mapAccExecutable, mapAfunExecutable,

  module Data.Array.Accelerate.AST.Exp
) where

import Data.Array.Accelerate.AST.Environment
import Data.Array.Accelerate.AST.Exp
import Data.Array.Accelerate.AST.LeftHandSide
import Data.Array.Accelerate.AST.Idx
import Data.Array.Accelerate.AST.Var
import Data.Array.Accelerate.Analysis.Hash.Exp
import Data.Array.Accelerate.Representation.Array
import Data.Array.Accelerate.Representation.Shape
import Data.Array.Accelerate.Representation.Type
import Data.Array.Accelerate.Trafo.Exp.Substitution
import Data.Array.Accelerate.Trafo.Exp.Shrink
import Data.Array.Accelerate.Type
import Data.Array.Accelerate.Error
import Data.Typeable                                ( (:~:)(..) )

import Data.ByteString.Builder.Extra
import Language.Haskell.TH                                          ( Q, TExp )
import Data.Kind (Type)

-- | An intermediate representation parameterized over executable operations.
-- This data type only consists of the control flow structure and
-- bookkeeping (allocating or copying buffers).
--
-- The data type is parameterized over the type of executable operations. In
-- the compiler pipeline, it is first instantiated with 'Execute op', which
-- means that the Exec constructor will target a single operation. Type
-- argument op is platform dependent, such that we can have different
-- operations for each backend and thus have backend specific optimizations
-- for some combinators. For instance, some backends may have a three kernel
-- scan whereas others have a single pass scan, or we may have different
-- operations based on which atomic instructions are available on the backend.
--
-- The data type is also parameterized over the environment of the terms,
-- consisting of ground values typed by 'GroundR', and the return type, which
-- is a tuple of ground values, typed by 'GroundsR'.
--
data PreOpenAcc (op :: Type -> Type) env a where
  -- | Executes an executable operation. Such execution does not return a
  -- value, the effects of the execution are only visible by the mutation of
  -- buffers which were annotated with either 'Mut' or 'Out'.
  -- Provides the operation arguments from the environment.
  --
  Exec    :: op args
          -> Args env args
          -> PreOpenAcc op env ()

  -- | Returns the values of the given variables.
  --
  Return  :: GroundVars env a
          -> PreOpenAcc op env a

  -- | Evaluates the expression and returns its value.
  --
  Compute :: Exp env t
          -> PreOpenAcc op env t

  -- | Local binding of ground values.
  -- As it is common in this intermediate representation to evaluate some program
  -- resulting in unit, for instance when execution some operation, and then
  -- and then do some other code, we write 'a; b' to denote 'let () = a in b'.
  Alet    :: GLeftHandSide bnd env env'
          -> Uniquenesses bnd
          -> PreOpenAcc op env  bnd
          -> PreOpenAcc op env' t
          -> PreOpenAcc op env  t

  -- | Allocates a new buffer of the given size.
  --
  Alloc   :: ShapeR sh
          -> ScalarType e
          -> ExpVars env sh
          -> PreOpenAcc op env (Buffer e)

  -- | Buffer inlet. To pass an array constant in this data type, one may need
  -- multiple 'Use' constructs because of the explicit Structure-of-Arrays.
  -- Triggers (possibly) asynchronous host->device transfer if necessary.
  --
  Use     :: ScalarType e
          -> Buffer e
          -> PreOpenAcc op env (Buffer e)

  -- | Capture a scalar in a singleton buffer
  --
  Unit    :: ExpVar env e
          -> PreOpenAcc op env (Buffer e)

  -- | If-then-else for array-level computations
  --
  Acond   :: ExpVar env PrimBool
          -> PreOpenAcc op env a
          -> PreOpenAcc op env a
          -> PreOpenAcc op env a

  -- Value-recursion for array-level computations
  -- The uniqueness guarantees are an invariant of the loop
  -- and should hold before and after each iteration.
  --
  Awhile  :: Uniquenesses a
          -> PreOpenAfun op env (a -> PrimBool)
          -> PreOpenAfun op env (a -> a)
          -> GroundVars     env a
          -> PreOpenAcc  op env a

-- | Function abstraction over parametrised array computations
--
data PreOpenAfun op env t where
  Abody ::                             PreOpenAcc  op env  t -> PreOpenAfun op env t
  Alam  :: GLeftHandSide a env env' -> PreOpenAfun op env' t -> PreOpenAfun op env (a -> t)


-- | Ground values are buffers or scalars.
--
data GroundR a where
  GroundRbuffer :: ScalarType e -> GroundR (Buffer e)
  GroundRscalar :: ScalarType e -> GroundR e

-- | Tuples of ground values
--
type GroundsR = TupR GroundR

-- | Types for local bindings
--
type GLeftHandSide = LeftHandSide GroundR
type GroundVar      = Var  GroundR
type GroundVars env = Vars GroundR env

-- | Uniqueness annotations for buffers
--
data Uniqueness t where
  Unique :: Uniqueness (Buffer t)
  Shared :: Uniqueness t

type Uniquenesses = TupR Uniqueness

shared :: TupR s t -> Uniquenesses t
shared = mapTupR (const Shared)

-- | The arguments to be passed to an operation of type `t`.
-- This type is represented as a cons list, separated by (->) and ending
-- in (). This function type represents the type of the operations.
-- `PreArgs a t` provides the arguments for function type `t`, where `a`
-- provides a single argument.
--
data PreArgs a t where
  ArgsNil :: PreArgs a ()
  (:>:)   :: a s -> PreArgs a t -> PreArgs a (s -> t)
infixr :>:

-- | A single argument to an operation.
--
data Arg env t where
  ArgVar      :: ExpVars env e         -> Arg env (Var' e)

  ArgExp      :: Exp env e             -> Arg env (Exp' e)

  ArgFun      :: Fun env e             -> Arg env (Fun' e)

  -- | An array is represented as scalar variables denoting the size and buffer variables.
  -- We assume that all the buffer variables stored in 'ArgBuffers' have the same size,
  -- as specified by the scalar variables of the size.
  --
  ArgArray    :: Modifier m
              -> ArrayR (Array sh e)
              -> GroundVars env sh
              -> GroundVars env (Buffers e)
              -> Arg env (m sh e)

-- | The arguments to be passed to an operation, in some environment.
--
type Args env = PreArgs (Arg env)

-- | Array arguments are annotated with an access modifier
--
data Modifier m where
  -- | The operation only reads from this array
  In  :: Modifier In
  -- | The operation only writes to the array. The initial content of the array is thus irrelevant
  Out :: Modifier Out
  -- | The operation both reads and writes to the array.
  Mut :: Modifier Mut

-- Empty data types, which are only used for the types of 'Arg'.
data Var' e   where
data Exp' e   where
data Fun' t   where
data In  sh e where
data Out sh e where
data Mut sh e where

argVarType :: Arg env (Var' e) -> TypeR e
argVarType (ArgVar vars) = varsType vars

argArrayR :: Arg env (m sh e) -> ArrayR (Array sh e)
argArrayR (ArgArray _ repr _ _) = repr

-- | An intermediate representation consisting of operations. This data type
-- only consists of the control flow structure and bookkeeping (allocating or
-- copying buffers). It is parameterized over the actual type of operations.
--
type OperationAcc op = PreOpenAcc op

-- | Functions on an intermediate representation consisting of operations.
-- This data type only consists of the control flow structure and bookkeeping (allocating or
-- copying buffers). It is parameterized over the actual type of operations.
--
type OperationAfun op = PreOpenAfun op

class HasGroundsR f where
  groundsR :: f a -> GroundsR a

instance HasGroundsR (PreOpenAcc exe env) where
  groundsR (Exec _ _)          = TupRunit
  groundsR (Return vars)     = groundsR vars
  groundsR (Compute e)       = groundsR e
  groundsR (Alet _ _ _ a)    = groundsR a
  groundsR (Alloc _ tp _)    = TupRsingle $ GroundRbuffer tp
  groundsR (Use tp _)        = TupRsingle $ GroundRbuffer tp
  groundsR (Unit (Var tp _)) = TupRsingle $ GroundRbuffer tp
  groundsR (Acond _ a _)     = groundsR a
  groundsR (Awhile _ _ _ a)  = groundsR a

instance HasGroundsR (GroundVar env) where
  groundsR (Var repr _) = TupRsingle repr

instance HasGroundsR (GroundVars env) where
  groundsR = varsType

instance HasGroundsR (OpenExp env benv) where
  groundsR = typeRtoGroundsR . expType

typeRtoGroundsR :: TypeR t -> GroundsR t
typeRtoGroundsR = mapTupR GroundRscalar

bufferImpossible :: ScalarType (Buffer e) -> a
bufferImpossible (SingleScalarType (NumSingleType (IntegralNumType tp))) = case tp of {}
bufferImpossible (SingleScalarType (NumSingleType (FloatingNumType tp))) = case tp of {}

groundFunctionImpossible :: GroundsR (s -> t) -> a
groundFunctionImpossible (TupRsingle (GroundRscalar t)) = functionImpossible (TupRsingle t)

type OpenExp env benv = PreOpenExp (ArrayInstr benv) env
type OpenFun env benv = PreOpenFun (ArrayInstr benv) env
type Fun benv = OpenFun () benv
type Exp benv = OpenExp () benv

data ArrayInstr benv t where
  Index     :: GroundVar benv (Buffer e) -> ArrayInstr benv (Int -> e)
  Parameter :: ExpVar benv e -> ArrayInstr benv (() -> e)

instance IsArrayInstr (ArrayInstr benv) where
  arrayInstrType arr = TupRsingle $ case arr of
    Index (Var (GroundRbuffer tp) _) -> tp
    Index (Var (GroundRscalar tp) _) -> bufferImpossible tp
    Parameter (Var tp _)             -> tp

  liftArrayInstr (Index var)     = [|| Index $$(liftGroundVar var) ||]
  liftArrayInstr (Parameter var) = [|| Parameter $$(liftExpVar var) ||]

  rnfArrayInstr  (Index var)     = rnfGroundVar var
  rnfArrayInstr  (Parameter var) = rnfExpVar var

  showArrayInstrOp Index{}       = "Index"
  showArrayInstrOp Parameter{}   = "Parameter"

  matchArrayInstr (Index v1)     (Index v2)     | Just Refl <- matchVar v1 v2 = Just Refl
  matchArrayInstr (Parameter v1) (Parameter v2) | Just Refl <- matchVar v1 v2 = Just Refl
  matchArrayInstr _              _              = Nothing

  encodeArrayInstr (Index v)     = intHost $(hashQ "Index")     <> encodeGroundVar v
  encodeArrayInstr (Parameter v) = intHost $(hashQ "Parameter") <> encodeExpVar v

encodeGroundR :: GroundR t -> Builder
encodeGroundR (GroundRscalar tp) = intHost $(hashQ "Scalar")    <> encodeScalarType tp
encodeGroundR (GroundRbuffer tp) = intHost $(hashQ "Buffer")    <> encodeScalarType tp

encodeGroundsR :: GroundsR t -> Builder
encodeGroundsR = encodeTupR encodeGroundR

encodeGroundVar :: GroundVar env t -> Builder
encodeGroundVar (Var repr ix) = encodeGroundR repr <> encodeIdx ix

encodeGroundVars :: GroundVars env t -> Builder
encodeGroundVars = encodeTupR encodeGroundVar

rnfGroundR :: GroundR t -> ()
rnfGroundR (GroundRscalar tp) = rnfScalarType tp
rnfGroundR (GroundRbuffer tp) = rnfScalarType tp

rnfGroundsR :: GroundsR t -> ()
rnfGroundsR = rnfTupR rnfGroundR

rnfGroundVar :: GroundVar env t -> ()
rnfGroundVar = rnfVar rnfGroundR

rnfGroundVars :: GroundVars env t -> ()
rnfGroundVars = rnfTupR rnfGroundVar

liftGroundR :: GroundR t -> Q (TExp (GroundR t))
liftGroundR (GroundRscalar tp) = [|| GroundRscalar $$(liftScalarType tp) ||]
liftGroundR (GroundRbuffer tp) = [|| GroundRbuffer $$(liftScalarType tp) ||]

liftGroundsR :: GroundsR t -> Q (TExp (GroundsR t))
liftGroundsR = liftTupR liftGroundR

liftGroundVar :: GroundVar env t -> Q (TExp (GroundVar env t))
liftGroundVar = liftVar liftGroundR

liftGroundVars :: GroundVars env t -> Q (TExp (GroundVars env t))
liftGroundVars = liftTupR liftGroundVar

paramIn :: ScalarType e -> GroundVar benv e -> OpenExp env benv e
paramIn t (Var _ ix) = ArrayInstr (Parameter $ Var t ix) Nil

paramsIn :: HasCallStack => TypeR e -> GroundVars benv e -> OpenExp env benv e
paramsIn TupRunit         TupRunit                = Nil
paramsIn (TupRpair t1 t2) (TupRpair v1 v2)        = paramsIn t1 v1 `Pair` paramsIn t2 v2
paramsIn (TupRsingle t)   (TupRsingle (Var _ ix)) = ArrayInstr (Parameter $ Var t ix) Nil
paramsIn _                _                       = internalError "Tuple mismatch"

paramIn' :: ExpVar benv e -> OpenExp env benv e
paramIn' v = ArrayInstr (Parameter v) Nil

paramsIn' :: ExpVars benv e -> OpenExp env benv e
paramsIn' TupRunit         = Nil
paramsIn' (TupRpair v1 v2) = paramsIn' v1 `Pair` paramsIn' v2
paramsIn' (TupRsingle v)   = ArrayInstr (Parameter v) Nil

type ReindexPartial f env env' = forall a. Idx env a -> f (Idx env' a)

reindexVar :: Applicative f => ReindexPartial f env env' -> Var s env t -> f (Var s env' t)
reindexVar k (Var repr ix) = Var repr <$> k ix

reindexVars :: Applicative f => ReindexPartial f env env' -> Vars s env t -> f (Vars s env' t)
reindexVars k (TupRsingle var) = TupRsingle <$> reindexVar k var
reindexVars k (TupRpair v1 v2) = TupRpair <$> reindexVars k v1 <*> reindexVars k v2
reindexVars _ TupRunit         = pure TupRunit

reindexArrayInstr :: Applicative f => ReindexPartial f env env' -> ArrayInstr env (s -> t) -> f (ArrayInstr env' (s -> t))
reindexArrayInstr k (Index     v) = Index     <$> reindexVar k v
reindexArrayInstr k (Parameter v) = Parameter <$> reindexVar k v

reindexExp :: (Applicative f, RebuildableExp e) => ReindexPartial f benv benv' -> e (ArrayInstr benv) env t -> f (e (ArrayInstr benv') env t)
reindexExp k = rebuildArrayInstrPartial (rebuildArrayInstrMap $ reindexArrayInstr k)

reindexArg :: Applicative f => ReindexPartial f env env' -> Arg env t -> f (Arg env' t)
reindexArg k (ArgVar vars)                = ArgVar <$> reindexVars k vars
reindexArg k (ArgExp e)                   = ArgExp <$> reindexExp k e
reindexArg k (ArgFun f)                   = ArgFun <$> reindexExp k f
reindexArg k (ArgArray m repr sh buffers) = ArgArray m repr <$> reindexVars k sh <*> reindexVars k buffers

reindexArgs :: Applicative f => ReindexPartial f env env' -> Args env t -> f (Args env' t)
reindexArgs _ ArgsNil    = pure ArgsNil
reindexArgs k (a :>: as) = (:>:) <$> reindexArg k a <*> reindexArgs k as

weakenReindex :: benv :> benv' -> ReindexPartial Identity benv benv'
weakenReindex k = Identity . (k >:>)

data AccessGroundR tp where
  AccessGroundRscalar :: ScalarType tp -> AccessGroundR tp
  AccessGroundRbuffer :: Modifier m -> ScalarType tp -> AccessGroundR (Buffer tp)

readonlyGroundRToAccessGroundR :: Exists (GroundVar env) -> Exists (Var AccessGroundR env)
readonlyGroundRToAccessGroundR (Exists (Var (GroundRscalar tp) ix)) = Exists $ Var (AccessGroundRscalar    tp) ix
readonlyGroundRToAccessGroundR (Exists (Var (GroundRbuffer tp) ix)) = Exists $ Var (AccessGroundRbuffer In tp) ix

argVars :: Arg env t -> [Exists (Var AccessGroundR env)]
argVars (ArgVar vars) = flattenTupR $ mapTupR (\(Var tp ix) -> Var (AccessGroundRscalar tp) ix) vars
argVars (ArgExp e) = map readonlyGroundRToAccessGroundR $ expGroundVars e
argVars (ArgFun e) = map readonlyGroundRToAccessGroundR $ funGroundVars e
argVars (ArgArray m _ sh buffers) = go buffers $ map readonlyGroundRToAccessGroundR $ flattenTupR sh
  where
    go :: GroundVars env s -> [Exists (Var AccessGroundR env)] -> [Exists (Var AccessGroundR env)]
    go TupRunit                                 accum = accum
    go (TupRsingle (Var (GroundRbuffer tp) ix)) accum = Exists (Var (AccessGroundRbuffer m tp) ix) : accum
    go (TupRsingle _)                           _     = error "Expected buffer"
    go (TupRpair v1 v2)                         accum = go v1 $ go v2 accum

argsVars :: Args env t -> [Exists (Var AccessGroundR env)]
argsVars (a :>: as) = argVars a ++ argsVars as
argsVars ArgsNil    = []

expGroundVars :: OpenExp env benv t -> [Exists (GroundVar benv)]
expGroundVars = map arrayInstrGroundVars . arrayInstrsInExp

funGroundVars :: OpenFun env benv t -> [Exists (GroundVar benv)]
funGroundVars = map arrayInstrGroundVars . arrayInstrsInFun

arrayInstrGroundVars :: Exists (ArrayInstr benv) -> Exists (GroundVar benv)
arrayInstrGroundVars (Exists (Parameter (Var tp ix))) = Exists $ Var (GroundRscalar tp) ix
arrayInstrGroundVars (Exists (Index var))             = Exists var

flattenTupR :: TupR s t -> [Exists s]
flattenTupR = (`go` [])
  where
    go :: TupR s t -> [Exists s] -> [Exists s]
    go (TupRsingle s)   accum = Exists s : accum
    go (TupRpair t1 t2) accum = go t1 $ go t2 accum
    go TupRunit         accum = accum

mapAccExecutable :: (forall args. op args -> op' args) -> PreOpenAcc op benv t -> PreOpenAcc op' benv t
mapAccExecutable f = \case
  Exec op args                  -> Exec (f op) args
  Return vars                   -> Return vars
  Compute e                     -> Compute e
  Alet lhs uniqueness bnd body  -> Alet lhs uniqueness (mapAccExecutable f bnd) (mapAccExecutable f body)
  Alloc shr tp sh               -> Alloc shr tp sh
  Use tp buffer                 -> Use tp buffer
  Unit vars                     -> Unit vars
  Acond var a1 a2               -> Acond var (mapAccExecutable f a1) (mapAccExecutable f a2)
  Awhile uniqueness c g a       -> Awhile uniqueness (mapAfunExecutable f c) (mapAfunExecutable f g) a

mapAfunExecutable :: (forall args. op args -> op' args) -> PreOpenAfun op benv t -> PreOpenAfun op' benv t
mapAfunExecutable f (Abody a)    = Abody    $ mapAccExecutable  f a
mapAfunExecutable f (Alam lhs a) = Alam lhs $ mapAfunExecutable f a

groundToExpVar :: TypeR e -> GroundVars benv e -> ExpVars benv e
groundToExpVar (TupRsingle t)   (TupRsingle (Var _ ix)) = TupRsingle (Var t ix)
groundToExpVar (TupRpair t1 t2) (TupRpair v1 v2)        = groundToExpVar t1 v1 `TupRpair` groundToExpVar t2 v2
groundToExpVar TupRunit         TupRunit                = TupRunit
groundToExpVar _                _                       = error "Impossible pair"
