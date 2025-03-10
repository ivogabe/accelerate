{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE MagicHash           #-}
{-# LANGUAGE PatternGuards       #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeApplications    #-}
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

module Data.Array.Accelerate.Analysis.Hash (

  -- hashing expressions
  Hash,
  HashOptions(..), defaultHashOptions,
  hashPreOpenAcc, hashPreOpenAccWith,
  hashOpenFun, hashOpenExp,

  -- auxiliary
  EncodeAcc,
  encodePreOpenAcc,
  encodeOpenExp,
  encodeOpenFun,
  encodeArraysType,
  hashQ,

) where

import Data.Array.Accelerate.AST
import Data.Array.Accelerate.AST.Var
import Data.Array.Accelerate.Analysis.Hash.TH
import Data.Array.Accelerate.Analysis.Hash.Exp
import Data.Array.Accelerate.Representation.Array
import Data.Array.Accelerate.Representation.Stencil
import Data.Array.Accelerate.Representation.Type
import Crypto.Hash.XKCP

import Data.ByteString.Builder
import Data.Monoid
import System.IO.Unsafe                                             ( unsafePerformIO )
import System.Mem.StableName                                        ( hashStableName, makeStableName )
import Prelude                                                      hiding ( exp )
import qualified Data.Hashable                                      as Hashable

{-# INLINEABLE hashPreOpenAcc #-}
hashPreOpenAcc :: HasArraysR acc => EncodeAcc acc -> PreOpenAcc acc aenv a -> Hash
hashPreOpenAcc = hashPreOpenAccWith defaultHashOptions

{-# INLINEABLE hashPreOpenAccWith #-}
hashPreOpenAccWith :: HasArraysR acc => HashOptions -> EncodeAcc acc -> PreOpenAcc acc aenv a -> Hash
hashPreOpenAccWith options encodeAcc
  = hashlazy
  . toLazyByteString
  . encodePreOpenAcc options encodeAcc


-- Array computations
-- ------------------

type EncodeAcc acc = forall aenv a. HashOptions -> acc aenv a -> Builder

{-# INLINEABLE encodePreOpenAcc #-}
encodePreOpenAcc
    :: forall acc aenv arrs. HasArraysR acc
    => HashOptions
    -> EncodeAcc acc
    -> PreOpenAcc acc aenv arrs
    -> Builder
encodePreOpenAcc options encodeAcc pacc =
  let
      travA :: forall aenv' a. acc aenv' a -> Builder
      travA = encodeAcc options

      travAF :: PreOpenAfun acc aenv' f -> Builder
      travAF = encodePreOpenAfun options encodeAcc

      travE :: OpenExp env' aenv' e -> Builder
      travE = encodeOpenExp

      travF :: OpenFun env' aenv' f -> Builder
      travF = encodeOpenFun

      travD :: Direction -> Builder
      travD LeftToRight = intHost $(hashQ "L")
      travD RightToLeft = intHost $(hashQ "R")

      deep :: Builder -> Builder
      deep | perfect options = id
           | otherwise       = const mempty

      deepE :: forall env' aenv' e. OpenExp env' aenv' e -> Builder
      deepE e
        | perfect options = travE e
        | otherwise       = encodeTypeR $ expType e
  in
  case pacc of
    Alet lhs bnd body               -> intHost $(hashQ "Alet")        <> encodeLeftHandSide encodeArrayType lhs <> travA bnd <> travA body
    Avar (Var repr v)               -> intHost $(hashQ "Avar")        <> encodeArrayType repr <> deep (encodeIdx v)
    Apair a1 a2                     -> intHost $(hashQ "Apair")       <> travA a1 <> travA a2
    Anil                            -> intHost $(hashQ "Anil")
    Atrace (Message _ _ msg) as bs  -> intHost $(hashQ "Atrace")      <> intHost (Hashable.hash msg) <> travA as <> travA bs
    Apply _ f a                     -> intHost $(hashQ "Apply")       <> travAF f <> travA a
    Aforeign _ _ f a                -> intHost $(hashQ "Aforeign")    <> travAF f <> travA a
    Use repr a                      -> intHost $(hashQ "Use")         <> encodeArrayType repr <> deep (encodeArray a)
    Awhile p f a                    -> intHost $(hashQ "Awhile")      <> travAF f <> travAF p <> travA a
    Unit _ e                        -> intHost $(hashQ "Unit")        <> travE e
    Generate _ e f                  -> intHost $(hashQ "Generate")    <> deepE e <> travF f
    -- We don't need to encode the type of 'e' when perfect is False, as 'e' is an expression of type Bool.
    -- We thus use `deep (travE e)` instead of `deepE e`.
    Acond e a1 a2                   -> intHost $(hashQ "Acond")       <> deep (travE e) <> travA a1 <> travA a2
    Reshape _ sh a                  -> intHost $(hashQ "Reshape")     <> deepE sh <> travA a
    Backpermute _ sh f a            -> intHost $(hashQ "Backpermute") <> deepE sh <> travF f  <> travA a
    Transform _ sh f1 f2 a          -> intHost $(hashQ "Transform")   <> deepE sh <> travF f1 <> travF f2 <> travA a
    Replicate spec ix a             -> intHost $(hashQ "Replicate")   <> deepE ix <> travA a  <> encodeSliceIndex spec
    Slice spec a ix                 -> intHost $(hashQ "Slice")       <> deepE ix <> travA a  <> encodeSliceIndex spec
    Map _ f a                       -> intHost $(hashQ "Map")         <> travF f  <> travA a
    ZipWith _ f a1 a2               -> intHost $(hashQ "ZipWith")     <> travF f  <> travA a1 <> travA a2
    Fold f e a                      -> intHost $(hashQ "Fold")        <> travF f  <> encodeMaybe travE e  <> travA a
    FoldSeg _ f e a s               -> intHost $(hashQ "FoldSeg")     <> travF f  <> encodeMaybe travE e  <> travA a <> travA s
    Scan  d f e a                   -> intHost $(hashQ "Scan")        <> encodeMaybe travD d  <> travF f  <> encodeMaybe travE e <> travA a
    Scan' d f e a                   -> intHost $(hashQ "Scan'")       <> encodeMaybe travD d  <> travF f  <>             travE e <> travA a
    Permute f a1 a2                 -> intHost $(hashQ "Permute")     <> foldMap travF f <> travA a1 <> travA a2
    Stencil s _ f b a               -> intHost $(hashQ "Stencil")     <> travF f  <> encodeBoundary (stencilEltR s) b   <> travA a
    Stencil2 s1 s2 _ f b1 a1 b2 a2  -> intHost $(hashQ "Stencil2")    <> travF f  <> encodeBoundary (stencilEltR s1) b1 <> travA a1 <> encodeBoundary (stencilEltR s2) b2 <> travA a2

{--
{-# INLINEABLE encodePreOpenSeq #-}
encodePreOpenSeq :: forall acc aenv senv arrs. EncodeAcc acc -> PreOpenSeq acc aenv senv arrs -> Int
encodePreOpenSeq encodeAcc s =
  let
      travA :: acc aenv' a -> Builder
      travA = encodeAcc -- XXX: plus type information?

      travE :: OpenExp env' aenv' e -> Builder
      travE = encodeOpenExp encodeAcc

      travAF :: PreOpenAfun acc aenv' f -> Builder
      travAF = encodePreOpenAfun encodeAcc

      travF :: OpenFun env' aenv' f -> Builder
      travF = encodeOpenFun encodeAcc

      travS :: PreOpenSeq acc aenv senv' arrs' -> Builder
      travS = encodePreOpenSeq encodeAcc

      travV :: forall a. Arrays a => Idx senv' a -> Builder
      travV v = encodeArraysType (arrays @a) <> encodeIdx v

      travP :: Producer acc aenv senv a -> Builder
      travP p =
        case p of
          StreamIn arrs       -> intHost . unsafePerformIO $! hashStableName `fmap` makeStableName arrs
          ToSeq spec _ acc    -> intHost $(hashQ "ToSeq")         <> travA  acc <> stringUtf8 (show spec)
          MapSeq f x          -> intHost $(hashQ "MapSeq")        <> travAF f   <> travV x
          ChunkedMapSeq f x   -> intHost $(hashQ "ChunkedMapSeq") <> travAF f   <> travV x
          ZipWithSeq f x y    -> intHost $(hashQ "ZipWithSeq")    <> travAF f   <> travV x <> travV y
          ScanSeq f e x       -> intHost $(hashQ "ScanSeq")       <> travF  f   <> travE e <> travV x

      travC :: Consumer acc aenv senv' a -> Builder
      travC c =
        case c of
          FoldSeq f e x          -> intHost $(hashQ "FoldSeq")        <> travF  f <> travE e   <> travV x
          FoldSeqFlatten f acc x -> intHost $(hashQ "FoldSeqFlatten") <> travAF f <> travA acc <> travV x
          Stuple t               -> intHost $(hashQ "Stuple")         <> encodeAtuple travC t
  in
  case s of
    Producer p s' -> intHost $(hashQ "Producer")   <> travP p <> travS s'
    Consumer c    -> intHost $(hashQ "Consumer")   <> travC c
    Reify ix      -> intHost $(hashQ "Reify")      <> travV ix
--}

encodeArray :: Array sh e -> Builder
encodeArray ad = intHost . unsafePerformIO $! hashStableName <$> makeStableName ad

encodePreOpenAfun
    :: forall acc aenv f.
       HashOptions
    -> EncodeAcc acc
    -> PreOpenAfun acc aenv f
    -> Builder
encodePreOpenAfun options travA afun =
  let
      travL :: forall aenv1 aenv2 a b. ALeftHandSide a aenv1 aenv2 -> PreOpenAfun acc aenv2 b -> Builder
      travL lhs l = encodeLeftHandSide encodeArrayType lhs <> encodePreOpenAfun options travA l
  in
  case afun of
    Abody b    -> intHost $(hashQ "Abody") <> travA options b
    Alam lhs l -> intHost $(hashQ "Alam")  <> travL lhs  l


encodeBoundary
    :: TypeR e
    -> Boundary aenv (Array sh e)
    -> Builder
encodeBoundary _  Wrap          = intHost $(hashQ "Wrap")
encodeBoundary _  Clamp         = intHost $(hashQ "Clamp")
encodeBoundary _  Mirror        = intHost $(hashQ "Mirror")
encodeBoundary tp (Constant c)  = intHost $(hashQ "Constant") <> encodeConst tp c
encodeBoundary _  (Function f)  = intHost $(hashQ "Function") <> encodeOpenFun f

encodeConst :: TypeR t -> t -> Builder
encodeConst TupRunit         ()    = intHost $(hashQ "nil")
encodeConst (TupRsingle t)   c     = encodeScalarConst t c
encodeConst (TupRpair ta tb) (a,b) = intHost $(hashQ "pair") <> encodeConst ta a <> encodeConst tb b
