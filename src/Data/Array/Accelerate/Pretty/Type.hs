{-# LANGUAGE CPP                 #-}
{-# LANGUAGE MonoLocalBinds      #-}
{-# LANGUAGE OverloadedStrings   #-}
-- |
-- Module      : Data.Array.Accelerate.Pretty.Type
-- Copyright   : [2008..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.Pretty.Type where

import Data.Array.Accelerate.Pretty.Exp
import Data.Array.Accelerate.Type
import Data.Array.Accelerate.Representation.Type

#if MIN_VERSION_prettyprinter (1,7,1)
import Prettyprinter
#else
import Data.Text.Prettyprint.Doc
#endif

prettyScalarType :: ScalarType t -> Adoc
prettyScalarType (SingleScalarType t) = prettySingleType t
prettyScalarType (VectorScalarType t) = prettyVectorType t

prettyVectorType :: VectorType t -> Adoc
prettyVectorType (VectorType n t) = prettySingleType t <> "x" <> pretty n

prettySingleType :: SingleType t -> Adoc
prettySingleType (NumSingleType (IntegralNumType tp)) = case tp of
  TypeInt    -> "Int"
  TypeInt8   -> "Int8"
  TypeInt16  -> "Int16"
  TypeInt32  -> "Int32"
  TypeInt64  -> "Int64"
  TypeWord   -> "Word"
  TypeWord8  -> "Word8"
  TypeWord16 -> "Word16"
  TypeWord32 -> "Word32"
  TypeWord64 -> "Word64"
prettySingleType (NumSingleType (FloatingNumType tp)) = case tp of
  TypeHalf   -> "Half"
  TypeFloat  -> "Float"
  TypeDouble -> "Double"

prettyType :: TypeR t -> Adoc
prettyType = prettyTupR (const prettyScalarType) 10
