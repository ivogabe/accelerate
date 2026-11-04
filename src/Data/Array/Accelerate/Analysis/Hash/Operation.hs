{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_HADDOCK hide #-}
-- |
-- Module      : Data.Array.Accelerate.Analysis.Hash
-- Copyright   : [2017..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.Analysis.Hash.Operation ( EncodeOperation(..), EncodeExecute(..), hashOperation, hashCluster, encodePreArgs, encodeArg ) where

import Data.Array.Accelerate.Analysis.Hash.Exp
import Data.Array.Accelerate.AST.Partitioned

import Crypto.Hash.XKCP
import Data.ByteString.Builder

hashOperation :: EncodeOperation op => op f t -> Args env t -> Hash
hashOperation op args
  = hashlazy
  $ toLazyByteString
  $ encodeOperation op <> encodePreArgs encodeArg args

hashCluster :: EncodeOperation op => Cluster op t -> Args env t -> Hash
hashCluster cluster args
  = hashlazy
  $ toLazyByteString
  $ encodeCluster cluster <> encodePreArgs encodeArg args

class EncodeOperation op where
  encodeOperation :: op b t -> Builder

class EncodeExecute exe where
  encodeExecute :: exe t -> Builder

instance EncodeOperation op => EncodeExecute (ExecOp op) where
  encodeExecute (ExecOp f op) = encodeIsFusible f <> encodeOperation op

instance EncodeOperation op => EncodeExecute (ExecCluster op) where
  encodeExecute (ExecSingle op) =
    intHost $(hashQ ("ExecSingle" :: String)) <> encodeOperation op
  encodeExecute (ExecClustered cluster) =
    intHost $(hashQ ("ExecClustered" :: String)) <> encodeCluster cluster

encodeIsFusible :: IsFusible f -> Builder
encodeIsFusible Fusible    = intHost $(hashQ ("Fusible" :: String))
encodeIsFusible NotFusible = intHost $(hashQ ("NotFusible" :: String))

encodePreArgs :: (forall t. arg t -> Builder) -> PreArgs arg f -> Builder
encodePreArgs f  (a :>: as) = intHost $(hashQ (":>:" :: String)) <> f a <> encodePreArgs f as
encodePreArgs _f ArgsNil    = intHost $(hashQ ("ArgsNil" :: String))

encodeArg :: Arg env t -> Builder
encodeArg (ArgArray m repr sh buffers)
  = intHost $(hashQ ("Array" :: String)) <> encodeModifier m <> encodeArrayType repr <> encodeGroundVars sh <> encodeGroundVars buffers
encodeArg (ArgVar var)  = intHost $(hashQ ("Var" :: String)) <> encodeTupR encodeExpVar var
encodeArg (ArgExp exp') = intHost $(hashQ ("Exp" :: String)) <> encodeOpenExp exp'
encodeArg (ArgFun fun)  = intHost $(hashQ ("Fun" :: String)) <> encodeOpenFun fun

encodeModifier :: Modifier m -> Builder
encodeModifier In  = intHost $(hashQ ("In" :: String))
encodeModifier Out = intHost $(hashQ ("Out" :: String))
encodeModifier Mut = intHost $(hashQ ("Mut" :: String))

encodeCluster :: EncodeOperation op => Cluster op args -> Builder
encodeCluster (SingleOp op label)
  = intHost $(hashQ ("SingleOp" :: String)) <> encodeSingleOp op <> encodeLabel label
encodeCluster (Fused fusion clusterL clusterR)
  = intHost $(hashQ ("Fused" :: String)) <> encodeFusion fusion <> encodeCluster clusterL <> encodeCluster clusterR

encodeLabel :: Node Comp -> Builder
encodeLabel (Node idx Nothing) = intHost idx <> intHost $(hashQ ("Nothing" :: String))
encodeLabel (Node idx (Just l)) = intHost idx <> intHost $(hashQ ("Just" :: String)) <> encodeLabel l

encodeFusion :: Fusion largs rargs args -> Builder
encodeFusion EmptyF         = intHost $(hashQ ("EmptyF" :: String))
encodeFusion (Vertical r f) = intHost $(hashQ ("Vertical" :: String))   <> encodeArrayType r <> encodeFusion f
encodeFusion (Horizontal f) = intHost $(hashQ ("Horizontal" :: String)) <> encodeFusion f
encodeFusion (Diagonal f)   = intHost $(hashQ ("Diagonal" :: String))   <> encodeFusion f
encodeFusion (IntroI1 f)    = intHost $(hashQ ("IntroI1" :: String))    <> encodeFusion f
encodeFusion (IntroI2 f)    = intHost $(hashQ ("IntroI2" :: String))    <> encodeFusion f
encodeFusion (IntroO1 f)    = intHost $(hashQ ("IntroO1" :: String))    <> encodeFusion f
encodeFusion (IntroO2 f)    = intHost $(hashQ ("IntroO2" :: String))    <> encodeFusion f
encodeFusion (IntroL f)     = intHost $(hashQ ("IntroL" :: String))     <> encodeFusion f
encodeFusion (IntroR f)     = intHost $(hashQ ("IntroR" :: String))     <> encodeFusion f

encodeSingleOp :: EncodeOperation op => SingleOp op args -> Builder
encodeSingleOp (Single op args)
  = encodeOperation op
  <> encodeClusterArgs args

encodeClusterArgs :: ClusterArgs env f -> Builder
encodeClusterArgs = encodePreArgs encodeClusterArg

encodeClusterArg :: ClusterArg env t -> Builder
encodeClusterArg (ClusterArgSingle idx)
  = intHost $(hashQ ("ClusterArgSingle" :: String)) <> encodeIdx idx
encodeClusterArg (ClusterArgArray m _ _ buffers)
  = intHost $(hashQ ("ClusterArgArray" :: String))  <> encodeModifier m <> encodeClusterArgBuffers buffers

encodeClusterArgBuffers :: ClusterArgBuffers env m sh t -> Builder
encodeClusterArgBuffers (ClusterArgBuffersPair l r)
  = intHost $(hashQ ("ClusterArgBuffersPair" :: String)) <> encodeClusterArgBuffers l <> encodeClusterArgBuffers r
encodeClusterArgBuffers (ClusterArgBuffersDead _ idx)
  = intHost $(hashQ ("ClusterArgBuffersDead" :: String)) <> encodeIdx idx
encodeClusterArgBuffers (ClusterArgBuffersLive _ idx)
  = intHost $(hashQ ("ClusterArgBuffersLive" :: String)) <> encodeIdx idx
