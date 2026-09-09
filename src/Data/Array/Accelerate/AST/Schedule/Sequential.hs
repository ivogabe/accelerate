{-# LANGUAGE GADTs                #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeFamilies         #-}
{-# OPTIONS_HADDOCK hide #-}
-- |
-- Module      : Data.Array.Accelerate.AST.Schedule.Sequential
-- Copyright   : [2008..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.AST.Schedule.Sequential (
  SArg(..), SArgs,
  module Operation,
  Cluster,
  SequentialSchedule(..),
  SeqSchedule(..),
  SeqScheduleFun(..)
) where

import Data.Array.Accelerate.AST.Exp
import Data.Array.Accelerate.AST.Var
import Data.Array.Accelerate.Type
import Data.Array.Accelerate.Representation.Array
import Data.Array.Accelerate.Representation.Shape
import Data.Array.Accelerate.Representation.Type
import Data.Array.Accelerate.AST.LeftHandSide
import qualified Data.Array.Accelerate.AST.Operation as Operation
import Data.Array.Accelerate.AST.Partitioned                        hiding (PreOpenAcc(..), PartitionedAcc, PartitionedAfun)
import qualified Data.Array.Accelerate.AST.Partitioned as Partition
import Data.Array.Accelerate.AST.Kernel
import Data.Array.Accelerate.AST.Schedule
import Data.Array.Accelerate.AST.Schedule.Uniform ( SArg(..), SArgs )
import Data.Array.Accelerate.Trafo.Schedule.Uniform ( compileKernel', CompiledKernel(..), rnfSArgs )
import Data.Array.Accelerate.AST.Execute
import Control.Concurrent.MVar
import Data.Typeable                                                ( (:~:)(..) )
import Data.Kind (Type)
import Data.Text (Text)
import Control.DeepSeq (NFData (rnf))

-- Generic schedule for a uniform memory space and uniform scheduling,
-- without task parallelism.
data SequentialSchedule kernel env t where
  SequentialLam
    :: GLeftHandSide s env env'
    -> SequentialSchedule kernel env' t
    -> SequentialSchedule kernel env  (s -> t)

  SequentialBody
    :: SeqSchedule        kernel env t
    -> SequentialSchedule kernel env (MVar t -> ())

data SeqSchedule (kernel :: (Type -> Type)) env t where
  -- | Executes a kernel. Such a kernel does not return a
  -- value, the effects of the execution are only visible by the mutation of
  -- buffers which were annotated with either 'Mut' or 'Out'.
  -- Provides the operation arguments from the environment.
  --
  Exec    :: KernelMetadata kernel f
          -> KernelFun kernel args
          -> SArgs env args
          -> SeqSchedule kernel env ()

  -- | Returns the values of the given variables.
  --
  Return  :: GroundVars env a
          -> SeqSchedule kernel env a

  -- | Evaluates the expression and returns its value.
  --
  Compute :: Exp env t
          -> SeqSchedule kernel env t

  -- | Local binding of ground values.
  -- As it is common in this intermediate representation to evaluate some program
  -- resulting in unit, for instance when execution some operation, and then
  -- and then do some other code, we write 'a; b' to denote 'let () = a in b'.
  Alet    :: GLeftHandSide bnd env env'
          -> Uniquenesses bnd
          -> SeqSchedule kernel env  bnd
          -> SeqSchedule kernel env' t
          -> SeqSchedule kernel env  t

  -- | Allocates a new buffer of the given size.
  --
  Alloc   :: ShapeR sh
          -> ScalarType e
          -> ExpVars env sh
          -> SeqSchedule op env (Buffer e)

  -- | Buffer inlet. To pass an array constant in this data type, one may need
  -- multiple 'Use' constructs because of the explicit Structure-of-Arrays.
  -- Triggers (possibly) asynchronous host->device transfer if necessary.
  --
  Use     :: ScalarType e
          -> Int -- Number of elements
          -> Buffer e
          -> SeqSchedule op env (Buffer e)

  -- | Capture a scalar in a singleton buffer
  --
  Unit    :: ExpVar env e
          -> SeqSchedule op env (Buffer e)

  -- | If-then-else for array-level computations
  --
  Acond   :: ExpVar env PrimBool
          -> SeqSchedule op env a
          -> SeqSchedule op env a
          -> SeqSchedule op env a

  -- Value-recursion for array-level computations
  -- The uniqueness guarantees are an invariant of the loop
  -- and should hold before and after each iteration.
  --
  Awhile  :: Uniquenesses a
          -> SeqScheduleFun op env (a -> PrimBool)
          -> SeqScheduleFun op env (a -> a)
          -> GroundVars     env a
          -> SeqSchedule  op env a

  Aassert :: Text
          -> Exp env PrimBool
          -> SeqSchedule kernel env ()

  Aassume :: Exp env PrimBool
          -> SeqSchedule kernel env ()

data SeqScheduleFun kernel env t where
  Slam  :: GLeftHandSide s env env'
        -> SeqScheduleFun kernel env' t
        -> SeqScheduleFun kernel env  (s -> t)

  Sbody :: SeqSchedule    kernel env t
        -> SeqScheduleFun kernel env t

instance IsSchedule SequentialSchedule where
  -- 'a' is a ground type (ie, can be represented using GroundR)
  type ScheduleInput  SequentialSchedule a = a
  type ScheduleOutput SequentialSchedule a = MVar a

  rnfSchedule (SequentialLam lhs f) = rnfLeftHandSide rnfGroundR lhs `seq` rnfSchedule f
  rnfSchedule (SequentialBody body) = rnfSchedule' body

  convertScheduleFun = convertScheduleFun'

  callScheduledFun (GFunctionRbody repr) f
    | Refl <- reprIsBody @SequentialSchedule repr = do
      destination <- newEmptyMVar
      f destination
      takeMVar destination
  callScheduledFun (GFunctionRlam _ ret) f = do
    return $ \a -> do
      callScheduledFun @SequentialSchedule ret $ f a

convertScheduleFun'
  :: IsKernel kernel
  => Partition.PartitionedAfun (KernelOperation kernel) env t -> SequentialSchedule kernel env (Scheduled SequentialSchedule t)
convertScheduleFun' (Operation.Alam lhs f) = SequentialLam lhs $ convertScheduleFun' f
convertScheduleFun' (Operation.Abody body)
  | Refl <- reprIsBody @SequentialSchedule $ groundsR body = SequentialBody $ convertSchedule' body

convertSchedule' :: forall kernel env t. IsKernel kernel => Partition.PartitionedAcc (KernelOperation kernel) env t -> SeqSchedule kernel env t
convertSchedule' (Operation.Exec op args)
  | CompiledKernel kernel args' <- compileKernel' @env @kernel op args = Exec (kernelMetadata kernel) kernel args'
convertSchedule' (Operation.Return vars) = Return vars
convertSchedule' (Operation.Manifest var) = Return $ TupRsingle var
convertSchedule' (Operation.Compute expr) = Compute expr
convertSchedule' (Operation.Alet lhs us bnd expr) = Alet lhs us (convertSchedule' bnd) (convertSchedule' expr)
convertSchedule' (Operation.Alloc shr tp sh) = Alloc shr tp sh
convertSchedule' (Operation.Use tp n buffer) = Use tp n buffer
convertSchedule' (Operation.Unit var) = Unit var
convertSchedule' (Operation.Acond var true false) = Acond var (convertSchedule' true) (convertSchedule' false)
convertSchedule' (Operation.Awhile us condition step initial) = Awhile us (convertScheduleFun'' condition) (convertScheduleFun'' step) initial
convertSchedule' (Operation.Aassert msg cond) = Alet (LeftHandSideWildcard TupRunit) TupRunit (Aassert msg cond) $ Compute $ Const scalarTypeWord8 0
convertSchedule' (Operation.Aassume cond) = Alet (LeftHandSideWildcard TupRunit) TupRunit (Aassume cond) $ Compute $ Const scalarTypeWord8 0
convertSchedule' (Operation.Fence _ next) = convertSchedule' next
convertSchedule' Operation.Atrace{} = error "TODO WALL: NON-EXHAUSTIVE PATTERN MATCH"

convertScheduleFun'' :: forall kernel env t. IsKernel kernel => Partition.PartitionedAfun (KernelOperation kernel) env t -> SeqScheduleFun kernel env t
convertScheduleFun'' (Operation.Alam lhs f) = Slam lhs $ convertScheduleFun'' f
convertScheduleFun'' (Operation.Abody body) = Sbody $ convertSchedule' body

rnfSchedule' :: IsKernel kernel => SeqSchedule kernel env t -> ()
rnfSchedule' (Exec metadata kernel args) = rnf' metadata `seq` rnf' kernel `seq` rnfSArgs args
rnfSchedule' (Return vars) = rnfGroundVars vars
rnfSchedule' (Compute expr) = rnfOpenExp expr
rnfSchedule' (Alet lhs us bnd expr)
  = rnfLeftHandSide rnfGroundR lhs
  `seq` rnfTupR rnfUniqueness us
  `seq` rnfSchedule' bnd
  `seq` rnfSchedule' expr
rnfSchedule' (Alloc shr tp sh) = rnfShapeR shr `seq` rnfScalarType tp `seq` rnfTupR rnfExpVar sh
rnfSchedule' (Use tp n buffer) = n `seq` buffer `seq` rnfScalarType tp
rnfSchedule' (Unit var) = rnfExpVar var
rnfSchedule' (Acond var true false) = rnfExpVar var `seq` rnfSchedule' true `seq` rnfSchedule' false
rnfSchedule' (Awhile us condition step initial) = rnfTupR rnfUniqueness us `seq` rnfScheduleFun condition `seq` rnfScheduleFun step `seq` rnfGroundVars initial
rnfSchedule' (Aassert msg cond) = rnf msg `seq` rnfOpenExp cond
rnfSchedule' (Aassume cond) = rnfOpenExp cond

rnfScheduleFun :: IsKernel kernel => SeqScheduleFun kernel env t -> ()
rnfScheduleFun (Slam lhs f) = rnfLeftHandSide rnfGroundR lhs `seq` rnfScheduleFun f
rnfScheduleFun (Sbody body) = rnfSchedule' body
