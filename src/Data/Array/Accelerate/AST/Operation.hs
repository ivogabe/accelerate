{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE InstanceSigs          #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE StandaloneDeriving    #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeOperators         #-}
{-# OPTIONS_GHC -Wno-orphans #-}
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
  Uniqueness(..), Uniquenesses, shared, unique, pairUniqueness,

  GroundR(..), GroundsR, GroundVar, GroundVars, GLeftHandSide, Var(..), Vars,
  HasGroundsR(..), groundToExpVar,

  PreArgs(..), Arg(..), Args, argsToList, Modifier(..), argArrayR, argVarType,
  rnfArg, rnfArgs, rnfPreArgs, mapArgs,

  Var', Exp', Fun', In, Out, Mut,

  ArrayDescriptor(..), ArrayDescriptors, weakenArrayDescriptor, weakenArrayDescriptors,

  OpenExp, OpenFun, Exp, Fun, ArrayInstr(..),
  expGroundVars, funGroundVars, arrayInstrsInExp, arrayInstrsInFun,

  encodeGroundR, encodeGroundsR, encodeGroundVar, encodeGroundVars, encodeArrayDescriptors,
  rnfGroundR, rnfGroundsR, rnfGroundVar, rnfGroundVars, rnfUniqueness,
  liftGroundR, liftGroundsR, liftGroundVar, liftGroundVars,

  bufferImpossible, groundFunctionImpossible,

  paramIn, paramsIn, paramIn', paramsIn',

  ReindexPartial, reindexArg, reindexArgs, reindexExp, reindexPreArgs, reindexVar, reindexVars, reindexArrayDescriptors,
  reindexIdxSet,
  weakenReindex,
  arrayDescriptorsIdxSet,
  argVars, argsVars, argsInputs, argsOutputs, AccessGroundR(..),

  mapAccExecutable, mapAfunExecutable,

  GroundRWithUniqueness(..), groundsRWithUniquenesses, lhsWithUniquesses,

  module Data.Array.Accelerate.AST.Exp,

  NFData'(..)
,reindexAcc,toGrounds,fromGrounds,weakenThroughReindex,fuseArgsWith,argsFromList,expToGroundVar) where

import Data.Array.Accelerate.AST.Environment
import Data.Array.Accelerate.AST.Exp
import Data.Array.Accelerate.AST.LeftHandSide
import Data.Array.Accelerate.AST.Idx
import Data.Array.Accelerate.AST.Var
import Data.Array.Accelerate.Analysis.Hash.Exp
import Data.Array.Accelerate.Representation.Array
import Data.Array.Accelerate.Representation.Ground
import Data.Array.Accelerate.Representation.Shape
import Data.Array.Accelerate.Representation.Type
import Data.Array.Accelerate.Trafo.Exp.Substitution
import Data.Array.Accelerate.Trafo.Exp.Shrink
import Data.Array.Accelerate.Type
import Data.Array.Accelerate.Error
import Data.Typeable                                                ( (:~:)(..) )
import Data.Maybe
import Data.Text                                                    ( Text )

import Language.Haskell.TH.Extra                                    ( CodeQ )
import Data.Kind (Type)
import Control.DeepSeq (NFData (rnf))
import Data.Functor.Identity
import Data.Array.Accelerate.AST.IdxSet (IdxSet)
import qualified Data.Array.Accelerate.AST.IdxSet as IdxSet

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

  -- | Fusion boundary.
  -- Corresponds with 'compute' in the user-facing language. Internally we use
  -- a different name as 'compute' already has a different meaning (computing
  -- expressions).
  --
  -- This constructor may only occur before fusion.
  --
  Manifest :: GroundVar env (Buffer e)
           -> PreOpenAcc op env (Buffer e)

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
          -> Int -- Number of elements
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

  -- | Value-recursion for array-level computations.
  -- The uniqueness guarantees are an invariant of the loop
  -- and should hold before and after each iteration.
  --
  Awhile  :: Uniquenesses a
          -> PreOpenAfun op env (a -> PrimBool)
          -> PreOpenAfun op env (a -> a)
          -> GroundVars     env a
          -> PreOpenAcc  op env a

  Atrace :: Text
         -> ArrayDescriptors env t
         -> PreOpenAcc op env Word8

  -- | Asserts that the given expression evaluates to true.
  --
  -- The return value of this operation is intentionally not specified.
  -- The value must be stored in a variable (in Alet) and that variable must be
  -- used in a Fence. This ensures that the assertion runs before the
  -- statements under the Fence are executed.
  --
  -- Forgetting to use the return value in a Fence may cause that the assertion
  -- is removed from the program (and thus not evaluated).
  --
  Aassert :: Text
          -> Exp env PrimBool
          -> PreOpenAcc op env Word8

  -- | Assumes that the given expression evaluates to true,
  -- without checking.
  --
  -- See Aassert for the description of the return value and the interaction
  -- with Fence.
  --
  Aassume :: Exp env PrimBool
          -> PreOpenAcc op env Word8

  -- | Compiler fence, to prevent the compiler from reordering the computation
  -- of the given variables past this point.
  --
  -- This is indented to be used with the return value of Aassert and Aassume,
  -- to ensure an assertion runs before certain instructions. By having two
  -- separate instructions (Aassert and Fence), we can more granually specify
  -- which parts of the program depend on an assertion. Without this
  -- granularity, assertions can block fusion in certain situations
  --
  Fence   :: IdxSet env
          -> PreOpenAcc op env t
          -> PreOpenAcc op env t

-- | Function abstraction over parametrised array computations
--
data PreOpenAfun op env t where
  Abody ::                             PreOpenAcc  op env  t -> PreOpenAfun op env t
  Alam  :: GLeftHandSide a env env' -> PreOpenAfun op env' t -> PreOpenAfun op env (a -> t)


-- | Types for local bindings
--
type GLeftHandSide = LeftHandSide GroundR
type GroundVar      = Var  GroundR
type GroundVars env = Vars GroundR env

toGround :: ExpVar env a -> GroundVar env a
toGround (Var st idx) = Var (GroundRscalar st) idx

toGrounds :: ExpVars env a -> GroundVars env a
toGrounds TupRunit = TupRunit
toGrounds (TupRsingle var) = TupRsingle (toGround var)
toGrounds (TupRpair x y) = TupRpair (toGrounds x) (toGrounds y)

fromGround :: GroundVar env a -> ExpVar env a
fromGround (Var (GroundRscalar st) idx) = Var st idx
fromGround (Var (GroundRbuffer _) _) = error "Not a scalar"

fromGrounds :: GroundVars env a -> ExpVars env a
fromGrounds TupRunit = TupRunit
fromGrounds (TupRsingle var) = TupRsingle (fromGround var)
fromGrounds (TupRpair x y) = TupRpair (fromGrounds x) (fromGrounds y)

-- | Uniqueness annotations for buffers
--
data Uniqueness t where
  Unique :: Uniqueness (Buffer t)
  Shared :: Uniqueness t

type Uniquenesses = TupR Uniqueness

deriving instance Show (Uniqueness t)

instance Semigroup (Uniqueness t) where
  (<>) :: Uniqueness t -> Uniqueness t -> Uniqueness t
  (<>) Unique Unique = Unique
  (<>) _      _      = Shared

shared :: TupR s t -> Uniquenesses t
shared = mapTupR (const Shared)

unique :: GroundsR t -> Uniquenesses t
unique = mapTupR f
  where
    f :: GroundR s -> Uniqueness s
    f (GroundRbuffer _) = Unique
    f _                 = Shared

pairUniqueness :: Uniquenesses (s, t) -> (Uniquenesses s, Uniquenesses t)
pairUniqueness (TupRpair u1 u2)    = (u1, u2)
pairUniqueness (TupRsingle Shared) = (TupRsingle Shared, TupRsingle Shared)

rnfUniqueness :: Uniqueness t -> ()
rnfUniqueness Unique = ()
rnfUniqueness Shared = ()

data ArrayDescriptor env a where
  ArrayDescriptor :: ShapeR sh
                  -> GroundVars env sh
                  -> GroundVars env (Buffers e)
                  -> ArrayDescriptor env (Array sh e)

type ArrayDescriptors env = TupR (ArrayDescriptor env)

weakenArrayDescriptors :: env :> env' -> ArrayDescriptors env a -> ArrayDescriptors env' a
weakenArrayDescriptors k = mapTupR (weakenArrayDescriptor k)

weakenArrayDescriptor :: env :> env' -> ArrayDescriptor env a -> ArrayDescriptor env' a
weakenArrayDescriptor k (ArrayDescriptor shr sh buffers) = ArrayDescriptor shr (weakenVars k sh) (weakenVars k buffers)

arrayDescriptorIdxSet :: ArrayDescriptor env t -> IdxSet env
arrayDescriptorIdxSet (ArrayDescriptor _ sh buffers) = IdxSet.fromVars sh `IdxSet.union` IdxSet.fromVars buffers

arrayDescriptorsIdxSet :: ArrayDescriptors env t -> IdxSet env
arrayDescriptorsIdxSet = foldMapTupR arrayDescriptorIdxSet

encodeArrayDescriptors :: ArrayDescriptors env t -> Builder
encodeArrayDescriptors = encodeTupR encodeArrayDescriptor

encodeArrayDescriptor :: ArrayDescriptor env t -> Builder
encodeArrayDescriptor (ArrayDescriptor shr sh buffer) = encodeShapeR shr <> encodeGroundVars sh <> encodeGroundVars buffer

-- | The arguments to be passed to an operation of type `t`.
-- This type is represented as a cons list, separated by (->) and ending
-- in (). This function type represents the type of the operations.
-- `PreArgs a t` provides the arguments for function type `t`, where `a`
-- provides a single argument.
--
data PreArgs a t where
  ArgsNil :: PreArgs a ()
  (:>:)   :: a s -> PreArgs a t -> PreArgs a (s -> t)
infixr 7 :>:

deriving instance (forall s. Show (a s)) => Show (PreArgs a t)

fuseArgsWith :: PreArgs a t -> PreArgs b t -> (forall x. a x -> b x -> c x) -> PreArgs c t
fuseArgsWith ArgsNil ArgsNil _ = ArgsNil
fuseArgsWith (a :>: as) (b :>: bs) f = f a b :>: fuseArgsWith as bs f

argsToList :: PreArgs a t -> [Exists a]
argsToList ArgsNil = []
argsToList (a :>: as) = Exists a : argsToList as

argsFromList :: [Exists a] -> Exists (PreArgs a)
argsFromList [] = Exists ArgsNil
argsFromList (Exists a : as) = case argsFromList as of Exists args -> Exists (a :>: args)

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

instance Show (Arg env a) where
  show = \case
    ArgVar{} -> "ArgVar"
    ArgExp{} -> "ArgExp"
    ArgFun{} -> "ArgFun"
    ArgArray m _ _ _ -> case m of
      In -> "in"
      Out -> "out"
      Mut -> "mut"


rnfPreArgs :: (forall s. a s -> ()) -> PreArgs a t -> ()
rnfPreArgs f (a :>: as) = f a `seq` rnfPreArgs f as
rnfPreArgs _ ArgsNil    = ()

rnfArg :: Arg env t -> ()
rnfArg (ArgVar vars) = rnfTupR rnfExpVar vars
rnfArg (ArgExp e)    = rnfOpenExp e
rnfArg (ArgFun f)    = rnfOpenFun f
rnfArg (ArgArray m repr sh buffers) = m `seq` rnfArrayR repr `seq` rnfGroundVars sh `seq` rnfGroundVars buffers

rnfArgs :: Args env t -> ()
rnfArgs = rnfPreArgs rnfArg

mapArgs :: (forall s. a s -> b s) -> PreArgs a t -> PreArgs b t
mapArgs f (a :>: as) = f a :>: mapArgs f as
mapArgs _ ArgsNil    = ArgsNil

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
deriving instance Show (Modifier m)

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

instance HasGroundsR (PreOpenAcc op env) where
  groundsR (Exec _ _)        = TupRunit
  groundsR (Return vars)     = groundsR vars
  groundsR (Manifest var)    = groundsR var
  groundsR (Compute e)       = groundsR e
  groundsR (Alet _ _ _ a)    = groundsR a
  groundsR (Alloc _ tp _)    = TupRsingle $ GroundRbuffer tp
  groundsR (Use tp _ _)      = TupRsingle $ GroundRbuffer tp
  groundsR (Unit (Var tp _)) = TupRsingle $ GroundRbuffer tp
  groundsR (Acond _ a _)     = groundsR a
  groundsR (Awhile _ _ _ a)  = groundsR a
  groundsR (Aassert _ _)     = TupRsingle $ GroundRscalar scalarTypeWord8
  groundsR (Aassume _)       = TupRsingle $ GroundRscalar scalarTypeWord8
  groundsR (Atrace _ _)      = TupRsingle $ GroundRscalar scalarTypeWord8
  groundsR (Fence _ a)       = groundsR a

instance HasGroundsR (GroundVar env) where
  groundsR (Var repr _) = TupRsingle repr

instance HasGroundsR (GroundVars env) where
  groundsR = varsType

instance HasGroundsR (OpenExp env benv) where
  groundsR :: OpenExp env benv a -> GroundsR a
  groundsR = typeRtoGroundsR . expType

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

  liftArrayInstr :: ArrayInstr benv t -> CodeQ (ArrayInstr benv t)
  liftArrayInstr (Index var)     = [|| Index $$(liftGroundVar var) ||]
  liftArrayInstr (Parameter var) = [|| Parameter $$(liftExpVar var) ||]

  rnfArrayInstr  (Index var)     = rnfGroundVar var
  rnfArrayInstr  (Parameter var) = rnfExpVar var

  showArrayInstrOp Index{}       = "Index"
  showArrayInstrOp Parameter{}   = "Parameter"

  matchArrayInstr (Index v1)     (Index v2)     | Just Refl <- matchVar v1 v2 = Just Refl
  matchArrayInstr (Parameter v1) (Parameter v2) | Just Refl <- matchVar v1 v2 = Just Refl
  matchArrayInstr _              _              = Nothing

  encodeArrayInstr (Index v)     = intHost $(hashQ ("Index" :: String))     <> encodeGroundVar v
  encodeArrayInstr (Parameter v) = intHost $(hashQ ("Parameter" :: String)) <> encodeExpVar v

  inlineArrayInstr = \case
    Parameter _ -> True
    _ -> False

encodeGroundR :: GroundR t -> Builder
encodeGroundR (GroundRscalar tp) = intHost $(hashQ ("Scalar" :: String))    <> encodeScalarType tp
encodeGroundR (GroundRbuffer tp) = intHost $(hashQ ("Buffer" :: String))    <> encodeScalarType tp

encodeGroundsR :: GroundsR t -> Builder
encodeGroundsR = encodeTupR encodeGroundR

encodeGroundVar :: GroundVar env t -> Builder
encodeGroundVar (Var repr ix) = encodeGroundR repr <> encodeIdx ix

encodeGroundVars :: GroundVars env t -> Builder
encodeGroundVars = encodeTupR encodeGroundVar

rnfGroundVar :: GroundVar env t -> ()
rnfGroundVar = rnfVar rnfGroundR

rnfGroundVars :: GroundVars env t -> ()
rnfGroundVars = rnfTupR rnfGroundVar

liftGroundR :: GroundR t -> CodeQ (GroundR t)
liftGroundR (GroundRscalar tp) = [|| GroundRscalar $$(liftScalarType tp) ||]
liftGroundR (GroundRbuffer tp) = [|| GroundRbuffer $$(liftScalarType tp) ||]

liftGroundsR :: GroundsR t -> CodeQ (GroundsR t)
liftGroundsR = liftTupR liftGroundR

liftGroundVar :: GroundVar env t -> CodeQ (GroundVar env t)
liftGroundVar = liftVar liftGroundR

liftGroundVars :: GroundVars env t -> CodeQ (GroundVars env t)
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

-- The first argument is ReindexPartial, but without the forall and specialized to 't'.
-- This makes it usable in more situations.
--
reindexVar :: Applicative f => (Idx env t -> f (Idx env' t)) -> Var s env t -> f (Var s env' t)
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
reindexArgs = reindexPreArgs reindexArg

reindexPreArgs
  :: Applicative f
  => (forall f' t'. Applicative f' => ReindexPartial f' env env' ->          s env  t' -> f'         (s env'  t'))
                                   -> ReindexPartial f  env env' -> PreArgs (s env) t  -> f (PreArgs (s env') t)
reindexPreArgs _ _ ArgsNil = pure ArgsNil
reindexPreArgs reindex k (a :>: as) = (:>:) <$> reindex k a <*> reindexPreArgs reindex k as

reindexIdxSet
  :: forall f env env' . Applicative f
  => ReindexPartial f env env'
  -> IdxSet.IdxSet env
  -> f (IdxSet.IdxSet env')
reindexIdxSet k set =
  foldr go (pure IdxSet.empty) (IdxSet.toList set)
  where
    go :: Exists (Idx env) -> f (IdxSet.IdxSet env') -> f (IdxSet.IdxSet env')
    go (Exists ix) acc = IdxSet.insert <$> k ix <*> acc

reindexAcc :: Applicative f => ReindexPartial f env env' -> PreOpenAcc op env t -> f (PreOpenAcc op env' t)
reindexAcc r (Exec opargs pa) = Exec opargs <$> reindexArgs r pa
reindexAcc r (Return tr) = Return <$> reindexVars r tr
reindexAcc r (Manifest var) = Manifest <$> reindexVar r var
reindexAcc r (Compute poe) = Compute <$> reindexExp r poe
reindexAcc r (Alet lhs tr poa poa') = reindexLHS r lhs $ \lhs' r' -> Alet lhs' tr <$> reindexAcc r poa <*> reindexAcc r' poa'
reindexAcc r (Alloc sr st tr) = Alloc sr st <$> reindexVars r tr
reindexAcc _ (Use st n bu) = pure $ Use st n bu
reindexAcc r (Unit var) = Unit <$> reindexVar r var
reindexAcc r (Acond var poa poa') = Acond <$> reindexVar r var <*> reindexAcc r poa <*> reindexAcc r poa'
reindexAcc r (Awhile tr poa poa' tr') = Awhile tr <$> reindexAfun r poa <*> reindexAfun r poa' <*> reindexVars r tr'
reindexAcc r (Aassert msg cond) = Aassert msg <$> reindexExp r cond
reindexAcc r (Aassume cond) = Aassume <$> reindexExp r cond
reindexAcc r (Atrace msg t) = Atrace msg <$> reindexArrayDescriptors r t
reindexAcc r (Fence set e) = Fence <$> reindexIdxSet r set <*> reindexAcc r e

reindexArrayDescriptors :: (Applicative f) => ReindexPartial f env env' -> ArrayDescriptors env a -> f (ArrayDescriptors env' a)
reindexArrayDescriptors k = traverseTupR (reindexArrayDescriptor k)

reindexArrayDescriptor :: Applicative f => ReindexPartial f env env' -> ArrayDescriptor env a -> f (ArrayDescriptor env' a)
reindexArrayDescriptor k (ArrayDescriptor shr sh buffers) = ArrayDescriptor shr <$> reindexVars k sh <*> reindexVars k buffers

reindexAfun :: Applicative f => ReindexPartial f env env' -> PreOpenAfun op env t -> f (PreOpenAfun op env' t)
reindexAfun r (Abody poa) = Abody <$> reindexAcc r poa
reindexAfun r (Alam lhs poa) = reindexLHS r lhs $ \lhs' r' -> Alam lhs' <$> reindexAfun r' poa

reindexLHS :: Applicative f => ReindexPartial f env env' -> LeftHandSide s t env env1 -> (forall env1'. LeftHandSide s t env' env1' -> ReindexPartial f env1 env1' -> r) -> r
reindexLHS r (LeftHandSideSingle st) k = k (LeftHandSideSingle st) $ \case
  ZeroIdx -> pure ZeroIdx
  SuccIdx idx -> SuccIdx <$> r idx
reindexLHS r (LeftHandSideWildcard tr) k = k (LeftHandSideWildcard tr) r
reindexLHS r (LeftHandSidePair left right) k = reindexLHS r left $ \left' r' ->
                                                reindexLHS r' right $ \right' r'' ->
                                                  k (LeftHandSidePair left' right') r''

weakenReindex :: benv :> benv' -> ReindexPartial Identity benv benv'
weakenReindex k = Identity . (k >:>)

weakenThroughReindex :: (benv :> benv') -> (ReindexPartial Identity benv benv' -> x -> Identity y) -> x -> y
weakenThroughReindex w k x = runIdentity $ k (weakenReindex w) x

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

argsInputs :: Args env t -> [Exists (Idx env)]
argsInputs = mapMaybe input . argsVars
  where
    input :: Exists (Var AccessGroundR env) -> Maybe (Exists (Idx env))
    input (Exists (Var (AccessGroundRbuffer Out _) _)) = Nothing
    input (Exists (Var _ idx)) = Just $ Exists idx

argsOutputs :: Args env t -> [Exists (Idx env)]
argsOutputs = mapMaybe output . argsVars
  where
    output :: Exists (Var AccessGroundR env) -> Maybe (Exists (Idx env))
    output (Exists (Var (AccessGroundRbuffer Out _) idx)) = Just $ Exists idx
    output (Exists (Var (AccessGroundRbuffer Mut _) idx)) = Just $ Exists idx
    output _ = Nothing

expGroundVars :: OpenExp env benv t -> [Exists (GroundVar benv)]
expGroundVars = map arrayInstrGroundVars . arrayInstrsInExp

funGroundVars :: OpenFun env benv t -> [Exists (GroundVar benv)]
funGroundVars = map arrayInstrGroundVars . arrayInstrsInFun

arrayInstrGroundVars :: Exists (ArrayInstr benv) -> Exists (GroundVar benv)
arrayInstrGroundVars (Exists (Parameter (Var tp ix))) = Exists $ Var (GroundRscalar tp) ix
arrayInstrGroundVars (Exists (Index var))             = Exists var

mapAccExecutable :: (forall args benv'. op args -> Args benv' args -> op' args) -> PreOpenAcc op benv t -> PreOpenAcc op' benv t
mapAccExecutable f = \case
  Exec op args                  -> Exec (f op args) args
  Return vars                   -> Return vars
  Manifest var                  -> Manifest var
  Compute e                     -> Compute e
  Alet lhs uniqueness bnd body  -> Alet lhs uniqueness (mapAccExecutable f bnd) (mapAccExecutable f body)
  Alloc shr tp sh               -> Alloc shr tp sh
  Use tp n buffer               -> Use tp n buffer
  Unit vars                     -> Unit vars
  Acond var a1 a2               -> Acond var (mapAccExecutable f a1) (mapAccExecutable f a2)
  Awhile uniqueness c g a       -> Awhile uniqueness (mapAfunExecutable f c) (mapAfunExecutable f g) a
  Aassert msg cond              -> Aassert msg cond
  Aassume cond                  -> Aassume cond
  Atrace msg t                  -> Atrace msg t
  Fence set e                   -> Fence set (mapAccExecutable f e)

mapAfunExecutable :: (forall args benv'. op args -> Args benv' args -> op' args) -> PreOpenAfun op benv t -> PreOpenAfun op' benv t
mapAfunExecutable f (Abody a)    = Abody    $ mapAccExecutable  f a
mapAfunExecutable f (Alam lhs a) = Alam lhs $ mapAfunExecutable f a

groundToExpVar :: TypeR e -> GroundVars benv e -> ExpVars benv e
groundToExpVar (TupRsingle t)   (TupRsingle (Var _ ix)) = TupRsingle (Var t ix)
groundToExpVar (TupRpair t1 t2) (TupRpair v1 v2)        = groundToExpVar t1 v1 `TupRpair` groundToExpVar t2 v2
groundToExpVar TupRunit         TupRunit                = TupRunit
groundToExpVar _                _                       = internalError "Impossible pair"

expToGroundVar :: ExpVars env e -> GroundVars env e
expToGroundVar  TupRunit = TupRunit
expToGroundVar  (TupRsingle (Var a ix)) = TupRsingle $ Var (GroundRscalar a) ix
expToGroundVar  (TupRpair x y) = TupRpair (expToGroundVar x) (expToGroundVar y)

class NFData' f where
  rnf' :: f a -> ()

instance NFData' op => NFData (OperationAcc op env a) where
  rnf (Exec op args)                = rnf' op `seq` rnfArgs args
  rnf (Return vars)                 = rnfGroundVars vars
  rnf (Manifest var)                = rnfGroundVar var
  rnf (Compute expr)                = rnfOpenExp expr
  rnf (Alet lhs us bnd a)           = rnfLeftHandSide rnfGroundR lhs `seq` rnfTupR rnfUniqueness us `seq` rnf bnd `seq` rnf a
  rnf (Alloc shr tp sh)             = rnfShapeR shr `seq` rnfScalarType tp `seq` rnfTupR rnfExpVar sh
  rnf (Use tp n buffer)             = n `seq` buffer `seq` rnfScalarType tp
  rnf (Unit var)                    = rnfVar rnfScalarType var
  rnf (Acond cond true false)       = rnfVar rnfScalarType cond `seq` rnf true `seq` rnf false
  rnf (Awhile us cond step initial) = rnfTupR rnfUniqueness us `seq` rnf cond `seq` rnf step `seq` rnfGroundVars initial
  rnf (Aassert _ cond)              = rnfOpenExp cond
  rnf (Aassume cond)                = rnfOpenExp cond
  rnf (Atrace _ t)                  = rnfTupR rnf t
  rnf (Fence set a)                 = IdxSet.rnfIdxSet set `seq` rnf a

instance NFData (ArrayDescriptor env a) where
  rnf (ArrayDescriptor shr sh buffers) = rnfShapeR shr `seq` rnfGroundVars sh `seq` rnfGroundVars buffers

instance NFData' op => NFData (OperationAfun op env a) where
  rnf (Abody a) = rnf a
  rnf (Alam lhs f) = rnfLeftHandSide rnfGroundR lhs `seq` rnf f

instance NFData' arg => NFData' (PreArgs arg) where
  rnf' ArgsNil = ()
  rnf' (a :>: args) = rnf' a `seq` rnf' args

-- Orphan, but because we need NFData' this is a safe place to write it
instance (NFData' s) => NFData (TupR s a) where
  rnf = rnfTupR rnf'


data GroundRWithUniqueness t where
  GroundRWithUniqueness :: GroundR t -> Uniqueness t -> GroundRWithUniqueness t

groundsRWithUniquenesses :: GroundsR t -> Uniquenesses t -> TupR GroundRWithUniqueness t
groundsRWithUniquenesses TupRunit         _                = TupRunit
groundsRWithUniquenesses (TupRpair g1 g2) (TupRpair u1 u2) = groundsRWithUniquenesses g1 u1 `TupRpair` groundsRWithUniquenesses g2 u2
groundsRWithUniquenesses (TupRpair g1 g2) _                = groundsRWithUniquenesses g1 (TupRsingle Shared) `TupRpair` groundsRWithUniquenesses g2 (TupRsingle Shared)
groundsRWithUniquenesses (TupRsingle tp)  (TupRsingle u)   = TupRsingle $ GroundRWithUniqueness tp u
groundsRWithUniquenesses _                _                = internalError "Tuple mismatch"

lhsWithUniquesses :: GLeftHandSide t env env' -> Uniquenesses t -> LeftHandSide GroundRWithUniqueness t env env'
lhsWithUniquesses (LeftHandSideWildcard g) uniquenesses     = LeftHandSideWildcard $ groundsRWithUniquenesses g uniquenesses
lhsWithUniquesses (LeftHandSideSingle g)   (TupRsingle u)   = LeftHandSideSingle $ GroundRWithUniqueness g u
lhsWithUniquesses (LeftHandSidePair l1 l2) (TupRpair u1 u2) = LeftHandSidePair (lhsWithUniquesses l1 u1) (lhsWithUniquesses l2 u2)
lhsWithUniquesses (LeftHandSidePair l1 l2) _                = LeftHandSidePair (lhsWithUniquesses l1 $ TupRsingle Shared) (lhsWithUniquesses l2 $ TupRsingle Shared)
lhsWithUniquesses _                        _                = internalError "Tuple mismatch"
