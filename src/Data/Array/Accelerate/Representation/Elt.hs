{-# LANGUAGE MagicHash             #-}
{-# LANGUAGE MonoLocalBinds        #-}
{-# LANGUAGE TemplateHaskellQuotes #-}
{-# OPTIONS_HADDOCK hide #-}
-- |
-- Module      : Data.Array.Accelerate.Representation.Elt
-- Copyright   : [2008..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.Representation.Elt
  where

import Data.Array.Accelerate.Representation.Type
import Data.Array.Accelerate.Type
import Data.Primitive.Vec

import Control.Monad.ST
import Data.List                                                    ( intercalate )
import Data.Primitive.ByteArray
import Foreign.Storable
import Language.Haskell.TH.Extra


undefElt :: TypeR t -> t
undefElt = tuple
  where
    tuple :: TypeR t -> t
    tuple TupRunit         = ()
    tuple (TupRpair ta tb) = (tuple ta, tuple tb)
    tuple (TupRsingle t)   = scalar t

    scalar :: ScalarType t -> t
    scalar (SingleScalarType t) = single t
    scalar (VectorScalarType t) = vector t

    vector :: VectorType t -> t
    vector (VectorType n t) = runST $ do
      mba           <- newByteArray (n * singleTypeSize t)
      ByteArray ba# <- unsafeFreezeByteArray mba
      return (Vec ba#)

    single :: SingleType t -> t
    single (NumSingleType t) = num t

    num :: NumType t -> t
    num (IntegralNumType t) = integral t
    num (FloatingNumType t) = floating t

    integral :: IntegralType t -> t
    integral TypeInt    = 0
    integral TypeInt8   = 0
    integral TypeInt16  = 0
    integral TypeInt32  = 0
    integral TypeInt64  = 0
    integral TypeWord   = 0
    integral TypeWord8  = 0
    integral TypeWord16 = 0
    integral TypeWord32 = 0
    integral TypeWord64 = 0

    floating :: FloatingType t -> t
    floating TypeHalf   = 0
    floating TypeFloat  = 0
    floating TypeDouble = 0

scalarTypeSize :: ScalarType e -> Int
scalarTypeSize = fst . scalarTypeSizeAlignment

scalarTypeAlignment :: ScalarType e -> Int
scalarTypeAlignment = snd . scalarTypeSizeAlignment

scalarTypeSizeAlignment :: ScalarType e -> (Int, Int)
scalarTypeSizeAlignment (SingleScalarType t) = (sz, sz)
  where sz = singleTypeSize t
scalarTypeSizeAlignment (VectorScalarType (VectorType n t)) = (n * sz, sz)
  where sz = singleTypeSize t

-- For all SingleTypes, the alignment is equal to the size
singleTypeSize :: SingleType e -> Int
singleTypeSize (NumSingleType (IntegralNumType tp)) = case tp of
  TypeInt    -> sizeOf (undefined::Int)
  TypeInt8   -> 1
  TypeInt16  -> 2
  TypeInt32  -> 4
  TypeInt64  -> 8
  TypeWord   -> sizeOf (undefined::Word)
  TypeWord8  -> 1
  TypeWord16 -> 2
  TypeWord32 -> 4
  TypeWord64 -> 8
singleTypeSize (NumSingleType (FloatingNumType tp)) = case tp of
  TypeHalf   -> 2
  TypeFloat  -> 4
  TypeDouble -> 8

showElt :: TypeR e -> e -> String
showElt t v = showsElt t v ""

showsElt :: TypeR e -> e -> ShowS
showsElt = tuple
  where
    tuple :: TypeR e -> e -> ShowS
    tuple TupRunit         ()       = showString "()"
    tuple (TupRpair t1 t2) (e1, e2) = showString "(" . tuple t1 e1 . showString ", " . tuple t2 e2 . showString ")"
    tuple (TupRsingle tp)  val      = scalar tp val

    scalar :: ScalarType e -> e -> ShowS
    scalar (SingleScalarType t) e = single t e
    scalar (VectorScalarType t) e = vector t e

    single :: SingleType e -> e -> ShowS
    single (NumSingleType t) = num t

    num :: NumType e -> e -> ShowS
    num (IntegralNumType t) = integral t
    num (FloatingNumType t) = floating t

    integral :: IntegralType e -> e -> ShowS
    integral TypeInt    = shows
    integral TypeInt8   = shows
    integral TypeInt16  = shows
    integral TypeInt32  = shows
    integral TypeInt64  = shows
    integral TypeWord   = shows
    integral TypeWord8  = shows
    integral TypeWord16 = shows
    integral TypeWord32 = shows
    integral TypeWord64 = shows

    floating :: FloatingType e -> e -> ShowS
    floating TypeHalf   = shows
    floating TypeFloat  = shows
    floating TypeDouble = shows

    vector :: VectorType (Vec n a) -> Vec n a -> ShowS
    vector (VectorType _ s) vec
      | SingleDict <- singleDict s
      = showString
      $ "<" ++ intercalate ", " ((\v -> single s v "") <$> listOfVec vec) ++ ">"

liftElt :: TypeR t -> t -> CodeQ t
liftElt TupRunit         ()    = [|| () ||]
liftElt (TupRsingle t)   x     = [|| $$(liftScalar t x) ||]
liftElt (TupRpair ta tb) (a,b) = [|| ($$(liftElt ta a), $$(liftElt tb b)) ||]

