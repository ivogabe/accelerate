{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE MagicHash           #-}
{-# LANGUAGE MonoLocalBinds      #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# OPTIONS_HADDOCK hide #-}
-- |
-- Module      : Data.Array.Accelerate.Analysis.Hash.Exp
-- Copyright   : [2017..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.Analysis.Hash.Schedule.Uniform (
  hashUniformScheduleFun
) where

import Data.Array.Accelerate.AST.Var
import Data.Array.Accelerate.AST.Kernel
import Data.Array.Accelerate.AST.Schedule.Uniform
import Data.Array.Accelerate.Analysis.Hash.TH
import Data.Array.Accelerate.Analysis.Hash.Exp
import Data.Array.Accelerate.Analysis.Hash.Operation (encodePreArgs)

import Crypto.Hash.XKCP
import Data.ByteString.Builder
import Data.ByteString.Short.Internal                               ( ShortByteString(..) )
import qualified Data.Hashable                                      as Hashable

hashUniformScheduleFun :: IsKernel kernel => UniformScheduleFun kernel env f -> Hash
hashUniformScheduleFun = hashlazy . toLazyByteString . encodeUniformScheduleFun

encodeUniformScheduleFun :: IsKernel kernel => UniformScheduleFun kernel env f -> Builder
encodeUniformScheduleFun (Slam lhs f) = intHost $(hashQ ("Slam" :: String)) <> encodeBLeftHandSide lhs <> encodeUniformScheduleFun f
encodeUniformScheduleFun (Sbody body) = intHost $(hashQ ("Sbody" :: String)) <> encodeUniformSchedule body

encodeUniformSchedule :: IsKernel kernel => UniformSchedule kernel env -> Builder
encodeUniformSchedule Return = intHost $(hashQ ("Return" :: String))
encodeUniformSchedule (Alet lhs bnd next)
  = intHost $(hashQ ("Alet" :: String))
  <> encodeBLeftHandSide lhs
  <> encodeBinding bnd
  <> encodeUniformSchedule next
encodeUniformSchedule (Effect effect next)
  = intHost $(hashQ ("Effect" :: String))
  <> encodeEffect effect
  <> encodeUniformSchedule next
encodeUniformSchedule (Acond (Var _ idx) true false next)
  = intHost $(hashQ ("Acond" :: String))
  <> encodeIdx idx
  <> encodeUniformSchedule true
  <> encodeUniformSchedule false
  <> encodeUniformSchedule next
encodeUniformSchedule (Awhile io fn initial next)
  = intHost $(hashQ ("Awhile" :: String))
  <> encodeIO io
  <> encodeUniformScheduleFun fn
  <> encodeTupR (\(Var _ idx) -> encodeIdx idx) initial
  <> encodeUniformSchedule next
encodeUniformSchedule (AwhileSeq io fn initial next)
  = intHost $(hashQ ("AwhileSeq" :: String))
  <> encodeIO io
  <> encodeUniformScheduleFun fn
  <> encodeTupR (\(Var _ idx) -> encodeIdx idx) initial
  <> encodeUniformSchedule next
encodeUniformSchedule (Spawn a b)
  = intHost $(hashQ ("Spawn" :: String))
  <> encodeUniformSchedule a
  <> encodeUniformSchedule b

encodeBLeftHandSide :: BLeftHandSide t env env' -> Builder
encodeBLeftHandSide = encodeLeftHandSide encodeBaseR

encodeBaseR :: BaseR t -> Builder
encodeBaseR (BaseRground tp)    = intHost $(hashQ ("Ground" :: String)) <> encodeGroundR tp
encodeBaseR BaseRsignal         = intHost $(hashQ ("Signal" :: String))
encodeBaseR BaseRsignalResolver = intHost $(hashQ ("SignalResolver" :: String))
encodeBaseR (BaseRref tp)       = intHost $(hashQ ("Ref" :: String)) <> encodeGroundR tp
encodeBaseR (BaseRrefWrite tp)  = intHost $(hashQ ("RefWrite" :: String)) <> encodeGroundR tp

{- TODO WALL: DEAD CODE
encodeBasesR :: BasesR t -> Builder
encodeBasesR = encodeTupR encodeBaseR
-}

encodeBinding :: Binding env t -> Builder
encodeBinding = \case
  Compute expr -> intHost $(hashQ ("Compute" :: String)) <> encodeOpenExp expr
  NewSignal _ -> intHost $(hashQ ("NewSignal" :: String))
  NewRef tp -> intHost $(hashQ ("NewRef" :: String)) <> encodeGroundR tp
  Alloc shr tp sh ->
    intHost $(hashQ ("Alloc" :: String))
    <> encodeShapeR shr
    <> encodeScalarType tp
    <> encodeTupR (\(Var _ idx) -> encodeIdx idx) sh
  -- Buffer is passed indirectly, via %imports_t in accelerate-llvm-native,
  -- so the buffer/pointer does not need to included in the hashing.
  Use tp _ _ -> intHost $(hashQ ("Use" :: String)) <> encodeScalarType tp
  Unit (Var tp idx) -> intHost $(hashQ ("Unit" :: String)) <> encodeScalarType tp <> encodeIdx idx
  RefRead (Var _ idx) -> intHost $(hashQ ("RefRead" :: String)) <> encodeIdx idx

encodeEffect :: IsKernel kernel => Effect kernel env -> Builder
encodeEffect = \case
  Exec _ kernel args -> encodeKernelFun kernel <> encodePreArgs encodeSArg args
  SignalAwait indices ->
    intHost $(hashQ ("SignalAwait" :: String))
    <> intHost (length indices)
    <> mconcat (map encodeIdx indices)
  SignalResolve indices ->
    intHost $(hashQ ("SignalResolve" :: String))
    <> intHost (length indices)
    <> mconcat (map encodeIdx indices)
  RefWrite (Var _ ref) (Var _ var) ->
    intHost $(hashQ ("RefWrite" :: String))
    <> encodeIdx ref
    <> encodeIdx var
  Aassert msg cond ->
    intHost $(hashQ ("Aassert" :: String))
    <> intHost (Hashable.hash msg)
    <> encodeOpenExp cond
  Atrace msg t ->
    intHost $(hashQ ("Atrace" :: String))
    <> intHost (Hashable.hash msg)
    <> encodeArrayDescriptors t

encodeIO :: InputOutputR input output -> Builder
encodeIO = \case
  InputOutputRsignal   -> intHost $(hashQ ("signal" :: String))
  InputOutputRref tp   -> intHost $(hashQ ("ref" :: String)) <> encodeGroundR tp
  InputOutputRpair a b -> intHost $(hashQ ("pair" :: String)) <> encodeIO a <> encodeIO b
  InputOutputRunit     -> intHost $(hashQ ("unit" :: String))

encodeSArg :: SArg env t -> Builder
encodeSArg (SArgScalar (Var tp idx)) =
  intHost $(hashQ ("SArgScalar" :: String))
  <> encodeScalarType tp
  <> encodeIdx idx
encodeSArg (SArgBuffer m (Var tp idx)) =
  intHost $(hashQ ("SArgBuffer" :: String))
  <> m'
  <> encodeGroundR tp
  <> encodeIdx idx
  where
    m' = case m of
      In  -> intHost $(hashQ ("In" :: String))
      Out -> intHost $(hashQ ("Out" :: String))
      Mut -> intHost $(hashQ ("Mut" :: String))

encodeKernelFun :: IsKernel kernel => OpenKernelFun kernel env t -> Builder
-- Argument types are encoded via encodeSArg
encodeKernelFun (KernelFunLam _ f) = encodeKernelFun f
encodeKernelFun (KernelFunBody kernel) = case encodeKernel kernel of
  Left (SHA3_256 ba#) -> shortByteString (SBS ba#)
  Right builder -> builder
