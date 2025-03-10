{-# LANGUAGE MonoLocalBinds        #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE RebindableSyntax      #-}
-- |
-- Module      : Data.Array.Accelerate.Unsafe
-- Copyright   : [2009..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--
-- Operations which may be unsafe. Use with care.
--
-- @since 1.2.0.0
--

module Data.Array.Accelerate.Unsafe (

  -- ** Unsafe operations
  Coerce, coerce,
  undef,

  -- ** Unordered operations
  scanUnordered, scanUnordered', scanUnordered1,
  filterUnordered, compactUnordered,

) where

import qualified Prelude
import Data.Array.Accelerate
import Data.Array.Accelerate.Language
import Data.Array.Accelerate.Smart
import Data.Array.Accelerate.Sugar.Elt


-- | The function 'coerce' allows you to convert a value between any two types
-- whose underlying representations have the same bit size at each component.
--
-- For example:
--
-- > coerce (x :: Exp Double)         :: Exp Word64
-- > coerce (x :: Exp (Int64,Float))  :: Exp (Complex Float, Word32)
--
-- Furthermore, as we typically declare newtype wrappers similarly to:
--
-- > type instance EltR (Sum a) = ((), EltR a)
--
-- This can be used instead of the newtype constructor, to go from the newtype's
-- abstract type to the concrete type by dropping the extra @()@ from the
-- representation, and vice-versa.
--
-- The type class 'Coerce' assures that there is a coercion between the two
-- types.
--
-- @since 1.2.0.0
--
coerce :: Coerce (EltR a) (EltR b) => Exp a -> Exp b
coerce = mkCoerce

-- | Variant of 'filter' that does not guarantee that the order of elements in
-- the output is the same as the order in the input.
--
filterUnordered
  :: Elt e
  => (Exp e -> Exp Bool)
  -> Acc (Vector e)
  -> Acc (Vector e)
filterUnordered p arr = compactUnordered (map p arr) arr

-- | As 'filterUnordered', but with separate arrays for the data elements and
-- the flags indicating which elements of that array should be kept.
--
compactUnordered
  :: Elt e
  => Acc (Vector Bool)
  -> Acc (Vector e)
  -> Acc (Vector e)
compactUnordered keep arr
  = let
        T2 target len   = scanUnordered' (+) 0 (map boolToInt keep)
        f value k t =
          if k then
            Just_ $ T2 (I1 t) value
          else
            Nothing_
        -- Allocate an array with the size of the input, instead of 'the len'.
        -- We later shrink the array to 'the len'. This allows us to fuse the
        -- scan' with the permute. The backpermute to shrink the array might
        -- be fused with a later consumer of the output of compact, depending
        -- on the program.
        dummy           = fill (shape arr) undef -- fill (I1 (the len)) undef
        result          = permuteUnique' dummy $ zipWith3 f arr keep target
    in
      backpermute (I1 $ the len) Prelude.id result
