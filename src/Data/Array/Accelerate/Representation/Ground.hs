{-# LANGUAGE EmptyCase            #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_HADDOCK hide #-}
-- |
-- Module      : Data.Array.Accelerate.Representation.Ground
-- Copyright   : [2008..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.Representation.Ground
  where

import Data.Array.Accelerate.Representation.Array
import Data.Array.Accelerate.Representation.Shape
import Data.Array.Accelerate.Representation.Type
import Data.Array.Accelerate.Type
import Data.Type.Equality

-- | Ground values are buffers or scalars.
--
data GroundR a where
  GroundRbuffer :: ScalarType e -> GroundR (Buffer e)
  GroundRscalar :: ScalarType e -> GroundR e

instance Distributes GroundR where
  reprIsSingle (GroundRbuffer _)  = Refl
  reprIsSingle (GroundRscalar tp) = reprIsSingle tp

  pairImpossible (GroundRscalar tp) = pairImpossible tp
  unitImpossible (GroundRscalar tp) = unitImpossible tp

-- | Tuples of ground values
--
type GroundsR = TupR GroundR

rnfGroundR :: GroundR t -> ()
rnfGroundR (GroundRscalar tp) = rnfScalarType tp
rnfGroundR (GroundRbuffer tp) = rnfScalarType tp

rnfGroundsR :: GroundsR t -> ()
rnfGroundsR = rnfTupR rnfGroundR

-- | Conversion from arrays representation to grounds representation
lowerArraysR :: ArraysR arr -> GroundsR (LoweredArrays arr)
lowerArraysR TupRunit          = TupRunit
lowerArraysR (TupRsingle repr) = lowerArrayR repr
lowerArraysR (TupRpair r1 r2)  = lowerArraysR r1 `TupRpair` lowerArraysR r2

lowerArrayR :: ArrayR arr -> GroundsR (LoweredArrays arr)
lowerArrayR (ArrayR shr tp) = mapTupR GroundRscalar (shapeType shr) `TupRpair` buffersR tp

buffersR :: forall e. TypeR e -> GroundsR (Buffers e)
buffersR TupRunit           = TupRunit
buffersR (TupRsingle tp)
  | Refl <- reprIsSingle @ScalarType @e @Buffer tp = TupRsingle (GroundRbuffer tp)
buffersR (TupRpair t1 t2)   = buffersR t1 `TupRpair` buffersR t2

-- | Utilities for working with GroundsR
typeRtoGroundsR :: TypeR t -> GroundsR t
typeRtoGroundsR = mapTupR GroundRscalar

bufferImpossible :: ScalarType (Buffer e) -> a
bufferImpossible (SingleScalarType (NumSingleType (IntegralNumType tp))) = case tp of {}
bufferImpossible (SingleScalarType (NumSingleType (FloatingNumType tp))) = case tp of {}

groundFunctionImpossible :: GroundsR (s -> t) -> a
groundFunctionImpossible (TupRsingle (GroundRscalar t)) = functionImpossible (TupRsingle t)

groundRelt :: GroundR (Buffer t) -> ScalarType t
groundRelt (GroundRbuffer tp) = tp
groundRelt (GroundRscalar tp) = bufferImpossible tp

type family LoweredArrays a where
  LoweredArrays ()           = ()
  LoweredArrays (a, b)       = (LoweredArrays a, LoweredArrays b)
  LoweredArrays (Array sh e) = (sh, Buffers e)

type family LoweredAfun a where
  LoweredAfun (a -> b) = LoweredArrays a -> LoweredAfun b
  LoweredAfun a        = LoweredArrays a

loweredAfunIsBody :: ArraysR a -> LoweredAfun a :~: LoweredArrays a
loweredAfunIsBody (TupRsingle ArrayR{}) = Refl
loweredAfunIsBody TupRunit              = Refl
loweredAfunIsBody (TupRpair _ _)        = Refl

lowerArrays :: ArraysR a -> a -> LoweredArrays a
lowerArrays TupRunit              ()                 = ()
lowerArrays (TupRpair r1 r2)      (a1, a2)           = (lowerArrays r1 a1, lowerArrays r2 a2)
lowerArrays (TupRsingle ArrayR{}) (Array sh buffers) = (sh, buffers)

sugarArrays :: ArraysR a -> LoweredArrays a -> a
sugarArrays TupRunit              ()            = ()
sugarArrays (TupRpair r1 r2)      (d1, d2)      = (sugarArrays r1 d1, sugarArrays r2 d2)
sugarArrays (TupRsingle ArrayR{}) (sh, buffers) = Array sh buffers

data GFunctionR t where
  GFunctionRlam  :: GroundsR t -> GFunctionR s -> GFunctionR (t -> s)
  GFunctionRbody :: GroundsR t                 -> GFunctionR t

