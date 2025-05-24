{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE GADTs             #-}
{-# LANGUAGE TypeFamilies      #-}
{-# LANGUAGE TypeOperators     #-}

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
  NoKernelMetadata, kernelFunKernel
) where

import Data.Array.Accelerate.AST.Environment
import Data.Array.Accelerate.AST.Partitioned
import Data.Array.Accelerate.AST.LeftHandSide
import Data.Array.Accelerate.Representation.Shape
import Data.Array.Accelerate.Type
import Data.Array.Accelerate.Array.Buffer
import Data.Array.Accelerate.Analysis.Hash.Exp
import Data.Kind

class (NFData' kernel, NFData' (KernelMetadata kernel)) => IsKernel kernel where
  type KernelOperation kernel :: Type -> Type
  type KernelMetadata  kernel :: Type -> Type

  compileKernel :: Env AccessGroundR env -> Clustered (KernelOperation kernel) args -> Args env args -> kernel env

  kernelMetadata :: KernelFun kernel f -> KernelMetadata kernel f
  default kernelMetadata :: KernelMetadata kernel ~ NoKernelMetadata => KernelFun kernel f -> KernelMetadata kernel f
  kernelMetadata _ = NoKernelMetadata

  -- Depending on the backend, it may either be easier
  -- to return the hash/UID of an already hashed kernel,
  -- or manually encode the kernel.
  encodeKernel :: kernel env -> Either Hash Builder

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
