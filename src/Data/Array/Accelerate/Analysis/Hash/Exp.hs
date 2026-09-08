{-# LANGUAGE MagicHash           #-}
{-# LANGUAGE MonoLocalBinds      #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
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

module Data.Array.Accelerate.Analysis.Hash.Exp (
  Hash,
  HashOptions(..), defaultHashOptions,
  hashOpenFun, hashOpenExp,
  encodeOpenExp,
  encodeOpenFun,

  encodeExpVar,
  encodeLeftHandSide,
  encodeTupR,
  encodeArraysType,
  encodeArrayType,
  encodeIdx,
  encodeIdxSet,
  encodeShapeR,
  encodeScalarType,
  encodeScalarConst,
  encodeTypeR,
  encodeSliceIndex,
  encodeMaybe,
  encodeIntegralType,
  hashQ,
  Builder,
  intHost,

) where

import Data.Array.Accelerate.AST.Exp
import Data.Array.Accelerate.AST.Idx
import Data.Array.Accelerate.AST.IdxSet (IdxSet)
import qualified Data.Array.Accelerate.AST.IdxSet as IdxSet
import Data.Array.Accelerate.AST.LeftHandSide
import Data.Array.Accelerate.AST.Var
import Data.Array.Accelerate.Analysis.Hash.TH
import Data.Array.Accelerate.Representation.Array
import Data.Array.Accelerate.Representation.Shape
import Data.Array.Accelerate.Representation.Slice
import Data.Array.Accelerate.Representation.Type
import Data.Array.Accelerate.Type
import Data.Primitive.Vec

import Crypto.Hash.XKCP
import Data.ByteString.Builder
import Data.ByteString.Builder.Extra
import Data.ByteString.Short.Internal                               ( ShortByteString(..) )
import qualified Data.Hashable                                      as Hashable
import Data.Monoid
import Prelude                                                      hiding ( exp )

-- Hashing
-- -------

type Hash = SHA3_256

data HashOptions = HashOptions
  { perfect :: Bool
    -- ^ Should the hash function include _all_ substructure, recursively?
    --
    -- Set to true (the default) if you want a truly unique fingerprint for
    -- the entire expression:
    --
    -- Example:
    --
    -- xs, ys :: Acc (Vector Float)
    -- xs = fill (constant (Z:.10)) 1.0
    -- ys = fill (constant (Z:.20)) 1.0
    --
    -- with perfect=True:
    --
    --   hash xs = 2e1f91aca4c476d13b36f22462e73c15bbdd9fcacb0d4996280f6004058e9732
    --   hash ys = 2fce5c849b6c652192b09aaeafdc8029e57b9f006c1ecd79ccf9114f349aaf9e
    --
    -- However, for a code generating backend the object code used to
    -- evaluate both of these expressions is likely to be identical.
    --
    -- Setting perfect=False results in:
    --
    --   hash xs = hash ys = f97944b0ec64ab8aa989fd60c8b50e7ec3eff759d22d2b340039d837d74dfc3c
    --
    -- Note that to be useful the provided 'EncodeAcc' function must also
    -- understand this option, and the consumer of the hash value must be
    -- agnostic to the elided details.
  }
  deriving Show

defaultHashOptions :: HashOptions
defaultHashOptions = HashOptions True


{-# INLINEABLE hashOpenFun #-}
hashOpenFun :: IsArrayInstr arr => PreOpenFun arr env f -> Hash
hashOpenFun
  = hashlazy
  . toLazyByteString
  . encodeOpenFun

-- {-# INLINEABLE hashOpenExp #-} throws warnings
hashOpenExp :: IsArrayInstr arr => PreOpenExp arr env t -> Hash
hashOpenExp
  = hashlazy
  . toLazyByteString
  . encodeOpenExp

encodeIdx :: Idx env t -> Builder
encodeIdx = intHost . idxToInt

encodeIdxSet :: IdxSet env -> Builder
encodeIdxSet set =
  intHost (length list)
  <> mconcat (map (\(Exists idx) -> encodeIdx idx) list)
  where
    list = IdxSet.toList set

encodeTupR :: (forall b. s b -> Builder) -> TupR s a -> Builder
encodeTupR _ TupRunit         = intHost $(hashQ ("TupRunit" :: String))
encodeTupR f (TupRpair r1 r2) = intHost $(hashQ ("TupRpair" :: String))   <> encodeTupR f r1 <> encodeTupR f r2
encodeTupR f (TupRsingle s)   = intHost $(hashQ ("TupRsingle" :: String)) <> f s

encodeLeftHandSide :: (forall b. s b -> Builder) -> LeftHandSide s a env env' -> Builder
encodeLeftHandSide f (LeftHandSideWildcard r) = intHost $(hashQ ("LeftHandSideWildcard" :: String)) <> encodeTupR f r
encodeLeftHandSide f (LeftHandSidePair r1 r2) = intHost $(hashQ ("LeftHandSidePair" :: String))     <> encodeLeftHandSide f r1 <> encodeLeftHandSide f r2
encodeLeftHandSide f (LeftHandSideSingle s)   = intHost $(hashQ ("LeftHandSideArray" :: String))    <> f s

encodeArrayType :: ArrayR a -> Builder
encodeArrayType (ArrayR shr tp) = encodeShapeR shr <> encodeTypeR tp

encodeArraysType :: ArraysR arrs -> Builder
encodeArraysType = encodeTupR encodeArrayType

encodeShapeR :: ShapeR sh -> Builder
encodeShapeR = intHost . rank

{-# INLINEABLE encodeOpenExp #-}
encodeOpenExp
    :: forall arr env exp.
       IsArrayInstr arr
    => PreOpenExp arr env exp
    -> Builder
encodeOpenExp exp =
  let
      travE :: forall env' e. PreOpenExp arr env' e -> Builder
      travE e = encodeOpenExp e

      travF :: PreOpenFun arr env' f -> Builder
      travF = encodeOpenFun
  in
  case exp of
    Let lhs bnd body            -> intHost $(hashQ ("Let" :: String))         <> encodeLeftHandSide encodeScalarType lhs <> travE bnd <> travE body
    Evar var                    -> intHost $(hashQ ("Evar" :: String))        <> encodeExpVar var
    Nil                         -> intHost $(hashQ ("Nil" :: String))
    Pair e1 e2                  -> intHost $(hashQ ("Pair" :: String))        <> travE e1 <> travE e2
    VecPack   _ e               -> intHost $(hashQ ("VecPack" :: String))     <> travE e
    VecUnpack _ e               -> intHost $(hashQ ("VecUnpack" :: String))   <> travE e
    Const tp c                  -> intHost $(hashQ ("Const" :: String))       <> encodeScalarConst tp c
    Undef tp                    -> intHost $(hashQ ("Undef" :: String))       <> encodeScalarType tp
    ToIndex _ sh i              -> intHost $(hashQ ("ToIndex" :: String))     <> travE sh <> travE i
    FromIndex _ sh i            -> intHost $(hashQ ("FromIndex" :: String))   <> travE sh <> travE i
    Case e rhs def              -> intHost $(hashQ ("Case" :: String))        <> travE e  <> mconcat [ word8 t <> travE c | (t,c) <- rhs ] <> encodeMaybe travE def
    Cond c t e                  -> intHost $(hashQ ("Cond" :: String))        <> travE c  <> travE t  <> travE e
    Select c t e                -> intHost $(hashQ ("Select" :: String))      <> travE c  <> travE t  <> travE e
    While p f x                 -> intHost $(hashQ ("While" :: String))       <> travF p  <> travF f  <> travE x
    PrimApp f x                 -> intHost $(hashQ ("PrimApp" :: String))     <> encodePrimFun f <> travE x
    ArrayInstr arr e            -> intHost $(hashQ ("ArrayInstr" :: String))  <> encodeArrayInstr arr <> travE e
    ShapeSize _ sh              -> intHost $(hashQ ("ShapeSize" :: String))   <> travE sh
    Foreign _ _ f e             -> intHost $(hashQ ("Foreign" :: String))     <> encodeOpenFun f <> travE e
    Coerce _ tp e               -> intHost $(hashQ ("Coerce" :: String))      <> encodeScalarType tp <> travE e
    Assert msg e1 e2            -> intHost $(hashQ ("Assert" :: String))      <> intHost (Hashable.hash msg) <> travE e1 <> travE e2
    Assume e1 e2                -> intHost $(hashQ ("Assume" :: String))      <> travE e1 <> travE e2

encodeExpVar :: ExpVar env t -> Builder
encodeExpVar (Var tp ix) = encodeScalarType tp <> encodeIdx ix

{-# INLINEABLE encodeOpenFun #-}
encodeOpenFun
    :: IsArrayInstr arr
    => PreOpenFun arr env f
    -> Builder
encodeOpenFun (Body b)    = intHost $(hashQ ("Body" :: String)) <> encodeOpenExp b
encodeOpenFun (Lam lhs l) = intHost $(hashQ ("Lam" :: String)) <> encodeLeftHandSide encodeScalarType lhs <> encodeOpenFun l

encodeScalarConst :: ScalarType t -> t -> Builder
encodeScalarConst (SingleScalarType t) = encodeSingleConst t
encodeScalarConst (VectorScalarType t) = encodeVectorConst t

encodeSingleConst :: SingleType t -> t -> Builder
encodeSingleConst (NumSingleType t) = encodeNumConst t

encodeVectorConst :: VectorType (Vec n t) -> Vec n t -> Builder
encodeVectorConst (VectorType n t) (Vec ba#) = intHost $(hashQ ("Vec" :: String)) <> intHost n <> encodeSingleType t <> shortByteString (SBS ba#)

encodeNumConst :: NumType t -> t -> Builder
encodeNumConst (IntegralNumType t) = encodeIntegralConst t
encodeNumConst (FloatingNumType t) = encodeFloatingConst t

encodeIntegralConst :: IntegralType t -> t -> Builder
encodeIntegralConst TypeInt{}    x = intHost $(hashQ ("Int" :: String))    <> intHost x
encodeIntegralConst TypeInt8{}   x = intHost $(hashQ ("Int8" :: String))   <> int8 x
encodeIntegralConst TypeInt16{}  x = intHost $(hashQ ("Int16" :: String))  <> int16Host x
encodeIntegralConst TypeInt32{}  x = intHost $(hashQ ("Int32" :: String))  <> int32Host x
encodeIntegralConst TypeInt64{}  x = intHost $(hashQ ("Int64" :: String))  <> int64Host x
encodeIntegralConst TypeWord{}   x = intHost $(hashQ ("Word" :: String))   <> wordHost x
encodeIntegralConst TypeWord8{}  x = intHost $(hashQ ("Word8" :: String))  <> word8 x
encodeIntegralConst TypeWord16{} x = intHost $(hashQ ("Word16" :: String)) <> word16Host x
encodeIntegralConst TypeWord32{} x = intHost $(hashQ ("Word32" :: String)) <> word32Host x
encodeIntegralConst TypeWord64{} x = intHost $(hashQ ("Word64" :: String)) <> word64Host x

encodeFloatingConst :: FloatingType t -> t -> Builder
encodeFloatingConst TypeHalf{}    (Half (CUShort x)) = intHost $(hashQ ("Half" :: String))    <> word16Host x
encodeFloatingConst TypeFloat{}   x                  = intHost $(hashQ ("Float" :: String))   <> floatHost x
encodeFloatingConst TypeDouble{}  x                  = intHost $(hashQ ("Double" :: String))  <> doubleHost x

encodePrimFun :: PrimFun f -> Builder
encodePrimFun (PrimAdd a)                = intHost $(hashQ ("PrimAdd" :: String))                <> encodeNumType a
encodePrimFun (PrimSub a)                = intHost $(hashQ ("PrimSub" :: String))                <> encodeNumType a
encodePrimFun (PrimMul a)                = intHost $(hashQ ("PrimMul" :: String))                <> encodeNumType a
encodePrimFun (PrimNeg a)                = intHost $(hashQ ("PrimNeg" :: String))                <> encodeNumType a
encodePrimFun (PrimAbs a)                = intHost $(hashQ ("PrimAbs" :: String))                <> encodeNumType a
encodePrimFun (PrimSig a)                = intHost $(hashQ ("PrimSig" :: String))                <> encodeNumType a
encodePrimFun (PrimQuot a)               = intHost $(hashQ ("PrimQuot" :: String))               <> encodeIntegralType a
encodePrimFun (PrimRem a)                = intHost $(hashQ ("PrimRem" :: String))                <> encodeIntegralType a
encodePrimFun (PrimQuotRem a)            = intHost $(hashQ ("PrimQuotRem" :: String))            <> encodeIntegralType a
encodePrimFun (PrimIDiv a)               = intHost $(hashQ ("PrimIDiv" :: String))               <> encodeIntegralType a
encodePrimFun (PrimMod a)                = intHost $(hashQ ("PrimMod" :: String))                <> encodeIntegralType a
encodePrimFun (PrimDivMod a)             = intHost $(hashQ ("PrimDivMod" :: String))             <> encodeIntegralType a
encodePrimFun (PrimBAnd a)               = intHost $(hashQ ("PrimBAnd" :: String))               <> encodeIntegralType a
encodePrimFun (PrimBOr a)                = intHost $(hashQ ("PrimBOr" :: String))                <> encodeIntegralType a
encodePrimFun (PrimBXor a)               = intHost $(hashQ ("PrimBXor" :: String))               <> encodeIntegralType a
encodePrimFun (PrimBNot a)               = intHost $(hashQ ("PrimBNot" :: String))               <> encodeIntegralType a
encodePrimFun (PrimBShiftL a)            = intHost $(hashQ ("PrimBShiftL" :: String))            <> encodeIntegralType a
encodePrimFun (PrimBShiftR a)            = intHost $(hashQ ("PrimBShiftR" :: String))            <> encodeIntegralType a
encodePrimFun (PrimBRotateL a)           = intHost $(hashQ ("PrimBRotateL" :: String))           <> encodeIntegralType a
encodePrimFun (PrimBRotateR a)           = intHost $(hashQ ("PrimBRotateR" :: String))           <> encodeIntegralType a
encodePrimFun (PrimPopCount a)           = intHost $(hashQ ("PrimPopCount" :: String))           <> encodeIntegralType a
encodePrimFun (PrimCountLeadingZeros a)  = intHost $(hashQ ("PrimCountLeadingZeros" :: String))  <> encodeIntegralType a
encodePrimFun (PrimCountTrailingZeros a) = intHost $(hashQ ("PrimCountTrailingZeros" :: String)) <> encodeIntegralType a
encodePrimFun (PrimFDiv a)               = intHost $(hashQ ("PrimFDiv" :: String))               <> encodeFloatingType a
encodePrimFun (PrimRecip a)              = intHost $(hashQ ("PrimRecip" :: String))              <> encodeFloatingType a
encodePrimFun (PrimSin a)                = intHost $(hashQ ("PrimSin" :: String))                <> encodeFloatingType a
encodePrimFun (PrimCos a)                = intHost $(hashQ ("PrimCos" :: String))                <> encodeFloatingType a
encodePrimFun (PrimTan a)                = intHost $(hashQ ("PrimTan" :: String))                <> encodeFloatingType a
encodePrimFun (PrimAsin a)               = intHost $(hashQ ("PrimAsin" :: String))               <> encodeFloatingType a
encodePrimFun (PrimAcos a)               = intHost $(hashQ ("PrimAcos" :: String))               <> encodeFloatingType a
encodePrimFun (PrimAtan a)               = intHost $(hashQ ("PrimAtan" :: String))               <> encodeFloatingType a
encodePrimFun (PrimSinh a)               = intHost $(hashQ ("PrimSinh" :: String))               <> encodeFloatingType a
encodePrimFun (PrimCosh a)               = intHost $(hashQ ("PrimCosh" :: String))               <> encodeFloatingType a
encodePrimFun (PrimTanh a)               = intHost $(hashQ ("PrimTanh" :: String))               <> encodeFloatingType a
encodePrimFun (PrimAsinh a)              = intHost $(hashQ ("PrimAsinh" :: String))              <> encodeFloatingType a
encodePrimFun (PrimAcosh a)              = intHost $(hashQ ("PrimAcosh" :: String))              <> encodeFloatingType a
encodePrimFun (PrimAtanh a)              = intHost $(hashQ ("PrimAtanh" :: String))              <> encodeFloatingType a
encodePrimFun (PrimExpFloating a)        = intHost $(hashQ ("PrimExpFloating" :: String))        <> encodeFloatingType a
encodePrimFun (PrimSqrt a)               = intHost $(hashQ ("PrimSqrt" :: String))               <> encodeFloatingType a
encodePrimFun (PrimLog a)                = intHost $(hashQ ("PrimLog" :: String))                <> encodeFloatingType a
encodePrimFun (PrimFPow a)               = intHost $(hashQ ("PrimFPow" :: String))               <> encodeFloatingType a
encodePrimFun (PrimLogBase a)            = intHost $(hashQ ("PrimLogBase" :: String))            <> encodeFloatingType a
encodePrimFun (PrimAtan2 a)              = intHost $(hashQ ("PrimAtan2" :: String))              <> encodeFloatingType a
encodePrimFun (PrimTruncate a b)         = intHost $(hashQ ("PrimTruncate" :: String))           <> encodeFloatingType a <> encodeIntegralType b
encodePrimFun (PrimRound a b)            = intHost $(hashQ ("PrimRound" :: String))              <> encodeFloatingType a <> encodeIntegralType b
encodePrimFun (PrimFloor a b)            = intHost $(hashQ ("PrimFloor" :: String))              <> encodeFloatingType a <> encodeIntegralType b
encodePrimFun (PrimCeiling a b)          = intHost $(hashQ ("PrimCeiling" :: String))            <> encodeFloatingType a <> encodeIntegralType b
encodePrimFun (PrimIsNaN a)              = intHost $(hashQ ("PrimIsNaN" :: String))              <> encodeFloatingType a
encodePrimFun (PrimIsInfinite a)         = intHost $(hashQ ("PrimIsInfinite" :: String))         <> encodeFloatingType a
encodePrimFun (PrimCmp a c)              = intHost $(hashQ ("PrimCmp" :: String))                <> encodeSingleType a <> encodeCmp c
encodePrimFun (PrimMax a)                = intHost $(hashQ ("PrimMax" :: String))                <> encodeSingleType a
encodePrimFun (PrimMin a)                = intHost $(hashQ ("PrimMin" :: String))                <> encodeSingleType a
encodePrimFun (PrimFromIntegral a b)     = intHost $(hashQ ("PrimFromIntegral" :: String))       <> encodeIntegralType a <> encodeNumType b
encodePrimFun (PrimToFloating a b)       = intHost $(hashQ ("PrimToFloating" :: String))         <> encodeNumType a      <> encodeFloatingType b
encodePrimFun PrimLAnd                   = intHost $(hashQ ("PrimLAnd" :: String))
encodePrimFun PrimLOr                    = intHost $(hashQ ("PrimLOr" :: String))
encodePrimFun PrimLNot                   = intHost $(hashQ ("PrimLNot" :: String))

encodeCmp :: Cmp -> Builder
encodeCmp CmpLt   = intHost $(hashQ ("CmpLt" :: String))
encodeCmp CmpGtEq = intHost $(hashQ ("CmpGtEq" :: String))
encodeCmp CmpEq   = intHost $(hashQ ("CmpEq" :: String))
encodeCmp CmpNEq  = intHost $(hashQ ("CmpNEq" :: String))

encodeTypeR :: TypeR t -> Builder
encodeTypeR TupRunit       = intHost $(hashQ ("TupRunit" :: String))
encodeTypeR (TupRsingle t) = intHost $(hashQ ("TupRsingle" :: String)) <> encodeScalarType t
encodeTypeR (TupRpair a b) = intHost $(hashQ ("TupRpair" :: String))   <> encodeTypeR a <> intHost (depthTypeR a)
                                                                       <> encodeTypeR b <> intHost (depthTypeR b)

depthTypeR :: TypeR t -> Int
depthTypeR TupRunit       = 0
depthTypeR TupRsingle{}   = 1
depthTypeR (TupRpair a b) = depthTypeR a + depthTypeR b

encodeScalarType :: ScalarType t -> Builder
encodeScalarType (SingleScalarType t) = intHost $(hashQ ("SingleScalarType" :: String)) <> encodeSingleType t
encodeScalarType (VectorScalarType t) = intHost $(hashQ ("VectorScalarType" :: String)) <> encodeVectorType t

encodeSingleType :: SingleType t -> Builder
encodeSingleType (NumSingleType t) = intHost $(hashQ ("NumSingleType" :: String))    <> encodeNumType t

encodeVectorType :: VectorType (Vec n t) -> Builder
encodeVectorType (VectorType n t) = intHost $(hashQ ("VectorType" :: String)) <> intHost n <> encodeSingleType t

encodeNumType :: NumType t -> Builder
encodeNumType (IntegralNumType t) = intHost $(hashQ ("IntegralNumType" :: String)) <> encodeIntegralType t
encodeNumType (FloatingNumType t) = intHost $(hashQ ("FloatingNumType" :: String)) <> encodeFloatingType t

encodeIntegralType :: IntegralType t -> Builder
encodeIntegralType TypeInt{}    = intHost $(hashQ ("Int" :: String))
encodeIntegralType TypeInt8{}   = intHost $(hashQ ("Int8" :: String))
encodeIntegralType TypeInt16{}  = intHost $(hashQ ("Int16" :: String))
encodeIntegralType TypeInt32{}  = intHost $(hashQ ("Int32" :: String))
encodeIntegralType TypeInt64{}  = intHost $(hashQ ("Int64" :: String))
encodeIntegralType TypeWord{}   = intHost $(hashQ ("Word" :: String))
encodeIntegralType TypeWord8{}  = intHost $(hashQ ("Word8" :: String))
encodeIntegralType TypeWord16{} = intHost $(hashQ ("Word16" :: String))
encodeIntegralType TypeWord32{} = intHost $(hashQ ("Word32" :: String))
encodeIntegralType TypeWord64{} = intHost $(hashQ ("Word64" :: String))

encodeFloatingType :: FloatingType t -> Builder
encodeFloatingType TypeHalf{}   = intHost $(hashQ ("Half" :: String))
encodeFloatingType TypeFloat{}  = intHost $(hashQ ("Float" :: String))
encodeFloatingType TypeDouble{} = intHost $(hashQ ("Double" :: String))

encodeSliceIndex :: SliceIndex slix sl co sh -> Builder
encodeSliceIndex SliceNil         = intHost $(hashQ ("SliceNil" :: String))
encodeSliceIndex (SliceAll r)     = intHost $(hashQ ("SliceAll" :: String))   <> encodeSliceIndex r
encodeSliceIndex (SliceFixed r)   = intHost $(hashQ ("sliceFixed" :: String)) <> encodeSliceIndex r

encodeMaybe :: (a -> Builder) -> Maybe a -> Builder
encodeMaybe _ Nothing  = intHost $(hashQ ("Nothing" :: String))
encodeMaybe f (Just x) = intHost $(hashQ ("Just" :: String)) <> f x
