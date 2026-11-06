{-# LANGUAGE DefaultSignatures    #-}
{-# LANGUAGE ImpredicativeTypes   #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE UndecidableInstances #-}

-- |
-- Module      : Data.Array.Accelerate.AST.Kernel
-- Copyright   : [2012..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--
-- This module defines the interface for kernels, to be implemented
-- in other modules.
--

module Data.Array.Accelerate.AST.Kernel (
  IsKernel(..), KernelArgR(..),
  OpenKernelFun(..), KernelFun,
  NoKernelMetadata, kernelFunKernel,
  FirstOrderSArgs, FirstOrderSArgsScalars, FirstOrderSArgsBuffers,
  firstOrderSArgScalar, SFunToEnv, SFunToEnv'
) where

import Data.Array.Accelerate.AST.Environment
import Data.Array.Accelerate.AST.Partitioned
import Data.Array.Accelerate.AST.LeftHandSide
import Data.Array.Accelerate.Representation.Shape
import Data.Array.Accelerate.Type
import Data.Array.Accelerate.Array.Buffer
import Data.Array.Accelerate.Analysis.Hash.Exp
import Data.Kind
import Data.Typeable                                                ( (:~:)(..) )

class (NFData' kernel, NFData' (KernelMetadata kernel)) => IsKernel kernel where
  type KernelOperation kernel :: Bool -> Type -> Type
  type KernelMetadata  kernel :: Type -> Type

  compileKernel :: ExecCluster (KernelOperation kernel) args -> Either
    -- Compile the kernel by compacting the arguments list. This deduplicates
    -- repeated arguments (which is very common for sizes of arrays), and
    -- supports Exp' and Fun' arguments, by extracting their free variables.
    (forall env. Env AccessGroundR env -> Args env args -> kernel env)
    -- Compile a first-order kernel by directly flattening the arguments list.
    -- Repeated arguments are stored multiple times in the environment.
    -- Exp' and Fun' are not supported.
    -- Typically only used for the foreign function interface.
    (kernel (SFunToEnv (FirstOrderSArgs args)))

  kernelMetadata :: KernelFun kernel f -> KernelMetadata kernel f
  default kernelMetadata :: KernelMetadata kernel ~ NoKernelMetadata => KernelFun kernel f -> KernelMetadata kernel f
  kernelMetadata _ = NoKernelMetadata

  -- Depending on the backend, it may either be easier
  -- to return the hash/UID of an already hashed kernel,
  -- or manually encode the kernel.
  encodeKernel :: kernel env -> Either Hash Builder

-- Converts args to an environment for a first-order kernel
type family FirstOrderSArgs args where
  FirstOrderSArgs (Var' a -> f) = FirstOrderSArgsScalars a (FirstOrderSArgs f)
  FirstOrderSArgs (m sh t -> f) = FirstOrderSArgsScalars sh (FirstOrderSArgsBuffers m (Buffers t) (FirstOrderSArgs f))
  FirstOrderSArgs () = ()

type family FirstOrderSArgsScalars arg f where
  FirstOrderSArgsScalars () f = f
  FirstOrderSArgsScalars (a, b) f = FirstOrderSArgsScalars a (FirstOrderSArgsScalars b f)
  FirstOrderSArgsScalars a f = Var' a -> f

type family FirstOrderSArgsBuffers m arg f where
  FirstOrderSArgsBuffers m () f = f
  FirstOrderSArgsBuffers m (a, b) f = FirstOrderSArgsBuffers m a (FirstOrderSArgsBuffers m b f)
  FirstOrderSArgsBuffers m (Buffer a) f = m DIM1 a -> f

type SFunToEnv f = SFunToEnv' f ()
type family SFunToEnv' f accum where
  SFunToEnv' ()              accum = accum
  SFunToEnv' (Var' e -> t)   accum = SFunToEnv' t (accum, e)
  SFunToEnv' (m DIM1 e -> t) accum = SFunToEnv' t (accum, Buffer e)

firstOrderSArgScalar :: forall t f. ScalarType t -> FirstOrderSArgsScalars t f :~: (Var' t -> f)
firstOrderSArgScalar (VectorScalarType _) = Refl
firstOrderSArgScalar (SingleScalarType t) = case t of
  NumSingleType (IntegralNumType tp) -> case tp of
    TypeInt    -> Refl
    TypeInt8   -> Refl
    TypeInt16  -> Refl
    TypeInt32  -> Refl
    TypeInt64  -> Refl
    TypeWord   -> Refl
    TypeWord8  -> Refl
    TypeWord16 -> Refl
    TypeWord32 -> Refl
    TypeWord64 -> Refl
  NumSingleType (FloatingNumType tp) -> case tp of
    TypeHalf   -> Refl
    TypeFloat  -> Refl
    TypeDouble -> Refl

type KernelFun kernel = OpenKernelFun kernel ()

data OpenKernelFun kernel env t where
  KernelFunLam
    :: KernelArgR t r
    -> OpenKernelFun kernel (env, r) f
    -> OpenKernelFun kernel env (t -> f)
  
  KernelFunBody
    :: kernel env
    -> OpenKernelFun kernel env ()

data KernelArgR t r where
  KernelArgRscalar :: ScalarType s -> KernelArgR (Var' s) s
  KernelArgRbuffer :: Modifier m -> ScalarType s -> KernelArgR (m DIM1 s) (Buffer s)

instance NFData' kernel => NFData' (OpenKernelFun kernel env) where
  rnf' (KernelFunLam g fun) = rnfKernelArgR g `seq` rnf' fun
  rnf' (KernelFunBody kernel) = rnf' kernel

rnfKernelArgR :: KernelArgR t r -> ()
rnfKernelArgR (KernelArgRscalar tp)   = rnfScalarType tp
rnfKernelArgR (KernelArgRbuffer m tp) = m `seq` rnfScalarType tp 

data NoKernelMetadata f = NoKernelMetadata

instance NFData' NoKernelMetadata where
  rnf' NoKernelMetadata = ()

kernelFunKernel :: OpenKernelFun kernel env t -> Exists kernel
kernelFunKernel (KernelFunBody kernel) = Exists kernel
kernelFunKernel (KernelFunLam _ f)
  | Exists k <- kernelFunKernel f
  = Exists k
