{-# LANGUAGE CPP                 #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE MonoLocalBinds      #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}
{-# LANGUAGE ViewPatterns        #-}
-- |
-- Module      : Data.Array.Accelerate.Language
-- Copyright   : [2008..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--
-- We use the dictionary view of overloaded operations (such as arithmetic and
-- bit manipulation) to reify such expressions.  With non-overloaded
-- operations (such as, the logical connectives) and partially overloaded
-- operations (such as comparisons), we use the standard operator names with a
-- \'*\' attached.  We keep the standard alphanumeric names as they can be
-- easily qualified.
--

module Data.Array.Accelerate.Language (

  -- * Array construction
  use, unit, replicate, generate,

  -- * Shape manipulation
  reshape,

  -- * Extraction of sub-arrays
  slice,

  -- * Map-like functions
  map, zipWith,

  -- -- * Sequence collection
  -- collect,

  -- -- * Sequence producers
  -- streamIn, toSeq,

  -- -- * Sequence transducers
  -- mapSeq, zipWithSeq, scanSeq,

  -- -- * Sequence consumers
  -- foldSeq, foldSeqFlatten,

  -- * Reductions
  fold, fold1, foldSeg', fold1Seg',

  -- * Scan functions
  scanl, scanl', scanl1, scanr, scanr', scanr1,

  -- * Permutations
  permute', permuteUnique', backpermute,

  -- * Stencil operations
  stencil, stencil2,

  -- ** Stencil specification
  Boundary, Stencil,
  clamp, mirror, wrap, function,


  -- ** Common stencil types
  Stencil3, Stencil5, Stencil7, Stencil9,
  Stencil3x3, Stencil5x3, Stencil3x5, Stencil5x5,
  Stencil3x3x3, Stencil5x3x3, Stencil3x5x3, Stencil3x3x5, Stencil5x5x3, Stencil5x3x5,
  Stencil3x5x5, Stencil5x5x5,

  -- * Foreign functions
  foreignAcc,
  foreignExp,

  -- * Controlling execution
  compute,

  -- * Index construction and destruction
  indexHead, indexTail, toIndex, fromIndex,
  intersect, union,

  -- * Flow-control
  acond, awhile,
  cond, select, while,
  Assert(..), assertBounds,

  -- * Utilities for bounds and shape checks
  inbounds, inboundsOf, shapeEq,

  -- * Array operations with a scalar result
  (!), (!!), shape, size, shapeSize, null,

  -- * Numeric functions
  subtract, even, odd, gcd, lcm, (^), (^^),

  -- * Conversions
  ord, chr, boolToInt, bitcast, isJust,

) where

import Data.Array.Accelerate.AST                                    ( PrimFun(..) )
import Data.Array.Accelerate.AST.Idx
import Data.Array.Accelerate.Pattern
import Data.Array.Accelerate.Representation.Array                   ( ArrayR(..) )
import Data.Array.Accelerate.Representation.Shape                   ( ShapeR(..) )
import Data.Array.Accelerate.Representation.Type
import Data.Array.Accelerate.Smart                                  hiding ( arraysR )
import Data.Array.Accelerate.Sugar.Array                            ( Arrays(..), Array, Scalar, Segments, arrayR )
import Data.Array.Accelerate.Sugar.Elt
import Data.Array.Accelerate.Sugar.Foreign
import Data.Array.Accelerate.Sugar.Shape                            ( Shape(..), Slice(..), (:.) )
import Data.Array.Accelerate.Type
import qualified Data.Array.Accelerate.Representation.Array         as R

import Data.Array.Accelerate.Classes.Eq
import Data.Array.Accelerate.Classes.Fractional
import Data.Array.Accelerate.Classes.Integral
import Data.Array.Accelerate.Classes.Num
import Data.Array.Accelerate.Classes.Ord
import Data.Text                                                    ( Text )
import GHC.Stack
import Data.String                                                  ( fromString )

import Prelude                                                      ( ($), (.), (<>), Maybe(..), Char )
#if __GLASGOW_HASKELL__ >= 904
import Data.Type.Equality
#endif

import Prelude ()

-- $setup
-- >>> :seti -XFlexibleContexts
-- >>> :seti -XScopedTypeVariables
-- >>> :seti -XTypeApplications
-- >>> :seti -XTypeOperators
-- >>> :seti -XViewPatterns
-- >>> import Data.Array.Accelerate
-- >>> import Data.Array.Accelerate.Data.Maybe
-- >>> import Data.Array.Accelerate.Interpreter
-- >>> :{
--   let runExp :: Elt e => Exp e -> e
--       runExp e = indexArray (run (unit e)) Z
-- :}

-- Array introduction
-- ------------------

-- | Make an array from vanilla Haskell available for processing within embedded
-- Accelerate computations.
--
-- Depending upon which backend is used to eventually execute array
-- computations, 'use' may entail data transfer (e.g. to a GPU).
--
-- 'use' is overloaded so that it can accept tuples of 'Arrays':
--
-- >>> let vec = fromList (Z:.10) [0..] :: Vector Int
-- >>> vec
-- Vector (Z :. 10) [0,1,2,3,4,5,6,7,8,9]
--
-- >>> let mat = fromList (Z:.5:.10) [0..] :: Matrix Int
-- >>> mat
-- Matrix (Z :. 5 :. 10)
--   [  0,  1,  2,  3,  4,  5,  6,  7,  8,  9,
--     10, 11, 12, 13, 14, 15, 16, 17, 18, 19,
--     20, 21, 22, 23, 24, 25, 26, 27, 28, 29,
--     30, 31, 32, 33, 34, 35, 36, 37, 38, 39,
--     40, 41, 42, 43, 44, 45, 46, 47, 48, 49]
--
-- >>> let vec' = use vec         :: Acc (Vector Int)
-- >>> let mat' = use mat         :: Acc (Matrix Int)
-- >>> let tup  = use (vec, mat)  :: Acc (Vector Int, Matrix Int)
--
use :: forall arrays. Arrays arrays => arrays -> Acc arrays
use = Acc . use' (arraysR @arrays) . fromArr
  where
    use' :: R.ArraysR a -> a -> SmartAcc a
    use' TupRunit                   ()       = SmartAcc $ Anil
    use' (TupRsingle repr@ArrayR{}) a        = SmartAcc $ Use repr a
    use' (TupRpair r1 r2)           (a1, a2) = SmartAcc $ use' r1 a1 `Apair` use' r2 a2

-- | Construct a singleton (one element) array from a scalar value (or tuple of
-- scalar values).
--
unit :: forall e. Elt e => Exp e -> Acc (Scalar e)
unit (Exp e) = Acc $ SmartAcc $ Unit (eltR @e) e

-- | Replicate an array across one or more dimensions as specified by the
-- /generalised/ array index provided as the first argument.
--
-- For example, given the following vector:
--
-- >>> let vec = fromList (Z:.10) [0..] :: Vector Int
-- >>> vec
-- Vector (Z :. 10) [0,1,2,3,4,5,6,7,8,9]
--
-- ...we can replicate these elements to form a two-dimensional array either by
-- replicating those elements as new rows:
--
-- >>> run $ replicate (constant (Z :. (4::Int) :. All)) (use vec)
-- Matrix (Z :. 4 :. 10)
--   [ 0, 1, 2, 3, 4, 5, 6, 7, 8, 9,
--     0, 1, 2, 3, 4, 5, 6, 7, 8, 9,
--     0, 1, 2, 3, 4, 5, 6, 7, 8, 9,
--     0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
--
-- ...or as columns:
--
-- >>> run $ replicate (lift (Z :. All :. (4::Int))) (use vec)
-- Matrix (Z :. 10 :. 4)
--   [ 0, 0, 0, 0,
--     1, 1, 1, 1,
--     2, 2, 2, 2,
--     3, 3, 3, 3,
--     4, 4, 4, 4,
--     5, 5, 5, 5,
--     6, 6, 6, 6,
--     7, 7, 7, 7,
--     8, 8, 8, 8,
--     9, 9, 9, 9]
--
-- Replication along more than one dimension is also possible. Here we replicate
-- twice across the first dimension and three times across the third dimension:
--
-- >>> run $ replicate (constant (Z :. (2::Int) :. All :. (3::Int))) (use vec)
-- Array (Z :. 2 :. 10 :. 3) [0,0,0,1,1,1,2,2,2,3,3,3,4,4,4,5,5,5,6,6,6,7,7,7,8,8,8,9,9,9,0,0,0,1,1,1,2,2,2,3,3,3,4,4,4,5,5,5,6,6,6,7,7,7,8,8,8,9,9,9]
--
-- The marker 'Any' can be used in the slice specification to match against some
-- arbitrary dimension. For example, here 'Any' matches against whatever shape
-- type variable @sh@ takes.
--
-- >>> :{
--   let rep0 :: forall sh e. (Shape sh, Elt e) => Exp Int -> Acc (Array sh e) -> Acc (Array (sh :. Int) e)
--       rep0 n a = replicate (lift (Any @sh :. n)) a
-- :}
--
-- >>> let x = unit 42 :: Acc (Scalar Int)
-- >>> run $ rep0 10 x
-- Vector (Z :. 10) [42,42,42,42,42,42,42,42,42,42]
--
-- >>> run $ rep0 5 (use vec)
-- Matrix (Z :. 10 :. 5)
--   [ 0, 0, 0, 0, 0,
--     1, 1, 1, 1, 1,
--     2, 2, 2, 2, 2,
--     3, 3, 3, 3, 3,
--     4, 4, 4, 4, 4,
--     5, 5, 5, 5, 5,
--     6, 6, 6, 6, 6,
--     7, 7, 7, 7, 7,
--     8, 8, 8, 8, 8,
--     9, 9, 9, 9, 9]
--
-- Of course, 'Any' and 'All' can be used together.
--
-- >>> :{
--   let rep1 :: forall sh e. (Shape sh, Elt e) => Exp Int -> Acc (Array (sh :. Int) e) -> Acc (Array (sh :. Int :. Int) e)
--       rep1 n a = replicate (lift (Any @sh :. n :. All)) a
-- :}
--
-- >>> run $ rep1 5 (use vec)
-- Matrix (Z :. 5 :. 10)
--   [ 0, 1, 2, 3, 4, 5, 6, 7, 8, 9,
--     0, 1, 2, 3, 4, 5, 6, 7, 8, 9,
--     0, 1, 2, 3, 4, 5, 6, 7, 8, 9,
--     0, 1, 2, 3, 4, 5, 6, 7, 8, 9,
--     0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
--
replicate
    :: forall slix e.
       (Slice slix, Elt e)
    => Exp slix
    -> Acc (Array (SliceShape slix) e)
    -> Acc (Array (FullShape  slix) e)
replicate = Acc $$ applyAcc (Replicate $ sliceIndex @slix)

-- | Construct a new array by applying a function to each index.
--
-- For example, the following will generate a one-dimensional array
-- (`Vector`) of three floating point numbers:
--
-- >>> run $ generate (I1 3) (\_ -> 1.2) :: Vector Float
-- Vector (Z :. 3) [1.2,1.2,1.2]
--
-- Or equivalently:
--
-- >>> run $ fill (constant (Z :. 3)) 1.2 :: Vector Float
-- Vector (Z :. 3) [1.2,1.2,1.2]
--
-- The following will create a vector with the elements @[1..10]@:
--
-- >>> run $ generate (I1 10) (\(I1 i) -> i + 1) :: Vector Int
-- Vector (Z :. 10) [1,2,3,4,5,6,7,8,9,10]
--
-- [/NOTE:/]
--
-- Using 'generate', it is possible to introduce nested data parallelism, which
-- will cause the program to fail.
--
-- If the index given by the scalar function is then used to dispatch further
-- parallel work, whose result is returned into 'Exp' terms by array indexing
-- operations such as ('!') or 'Data.Array.Accelerate.Prelude.the', the program
-- will fail with the error:
-- @.\/Data\/Array\/Accelerate\/Trafo\/Sharing.hs:447 (convertSharingExp): inconsistent valuation \@ shared \'Exp\' tree ...@.
--
generate
    :: forall sh a.
       (HasCallStack, Shape sh, Elt a)
    => Exp sh
    -> (Exp sh -> Exp a)
    -> Acc (Array sh a)
generate sh fun = Acc $ applyAcc (Generate $ arrayR @sh @a) (assertBounds "Shape in generate should be non-negative" isNonNegative sh) fun

-- Shape manipulation
-- ------------------

-- | Change the shape of an array without altering its contents. The 'size' of
-- the source and result arrays must be identical.
--
-- > precondition: shapeSize sh == shapeSize sh'
--
-- If the argument array is manifest in memory, 'reshape' is a no-op. If the
-- argument is to be fused into a subsequent operation, 'reshape' corresponds to
-- an index transformation in the fused code.
--
reshape
    :: forall sh sh' e.
       (HasCallStack, Shape sh, Shape sh', Elt e)
    => Exp sh
    -> Acc (Array sh' e)
    -> Acc (Array sh e)
reshape sh as = Acc $ applyAcc (Reshape $ shapeR @sh) (assertBounds "Reshape should preserve the size" (\s -> shapeSize s == size as) sh) as

-- Extraction of sub-arrays
-- ------------------------

-- | Index an array with a /generalised/ array index, supplied as the second
-- argument. The result is a new array (possibly a singleton) containing the
-- selected dimensions ('All's) in their entirety.
--
-- 'slice' is the opposite of 'replicate', and can be used to /cut out/ entire
-- dimensions. For example, for the two dimensional array 'mat':
--
-- >>> let mat = fromList (Z:.5:.10) [0..] :: Matrix Int
-- >>> mat
-- Matrix (Z :. 5 :. 10)
--   [  0,  1,  2,  3,  4,  5,  6,  7,  8,  9,
--     10, 11, 12, 13, 14, 15, 16, 17, 18, 19,
--     20, 21, 22, 23, 24, 25, 26, 27, 28, 29,
--     30, 31, 32, 33, 34, 35, 36, 37, 38, 39,
--     40, 41, 42, 43, 44, 45, 46, 47, 48, 49]
--
-- ...will can select a specific row to yield a one dimensional result by fixing
-- the row index (2) while allowing the column index to vary (via 'All'):
--
-- >>> run $ slice (use mat) (constant (Z :. (2::Int) :. All))
-- Vector (Z :. 10) [20,21,22,23,24,25,26,27,28,29]
--
-- A fully specified index (with no 'All's) returns a single element (zero
-- dimensional array).
--
-- >>> run $ slice (use mat) (constant (Z :. 4 :. 2 :: DIM2))
-- Scalar Z [42]
--
-- The marker 'Any' can be used in the slice specification to match against some
-- arbitrary (lower) dimension. Here 'Any' matches whatever shape type variable
-- @sh@ takes:
--
-- >>> :{
--   let
--       sl0 :: forall sh e. (Shape sh, Elt e) => Acc (Array (sh:.Int) e) -> Exp Int -> Acc (Array sh e)
--       sl0 a n = slice a (lift (Any @sh :. n))
-- :}
--
-- >>> let vec = fromList (Z:.10) [0..] :: Vector Int
-- >>> run $ sl0 (use vec) 4
-- Scalar Z [4]
--
-- >>> run $ sl0 (use mat) 4
-- Vector (Z :. 5) [4,14,24,34,44]
--
-- Of course, 'Any' and 'All' can be used together.
--
-- >>> :{
--   let sl1 :: forall sh e. (Shape sh, Elt e) => Acc (Array (sh:.Int:.Int) e) -> Exp Int -> Acc (Array (sh:.Int) e)
--       sl1 a n = slice a (lift (Any @sh :. n :. All))
-- :}
--
-- >>> run $ sl1 (use mat) 4
-- Vector (Z :. 10) [40,41,42,43,44,45,46,47,48,49]
--
-- >>> let cube = fromList (Z:.3:.4:.5) [0..] :: Array DIM3 Int
-- >>> cube
-- Array (Z :. 3 :. 4 :. 5) [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59]
--
-- >>> run $ sl1 (use cube) 2
-- Matrix (Z :. 3 :. 5)
--   [ 10, 11, 12, 13, 14,
--     30, 31, 32, 33, 34,
--     50, 51, 52, 53, 54]
--
slice :: forall slix e.
         (Slice slix, Elt e)
      => Acc (Array (FullShape slix) e)
      -> Exp slix
      -> Acc (Array (SliceShape slix) e)
slice = Acc $$ applyAcc (Slice $ sliceIndex @slix)

-- Map-like functions
-- ------------------

-- | Apply the given function element-wise to an array. Denotationally we have:
--
-- > map f [x1, x2, ... xn] = [f x1, f x2, ... f xn]
--
-- >>> let xs = fromList (Z:.10) [0..] :: Vector Int
-- >>> xs
-- Vector (Z :. 10) [0,1,2,3,4,5,6,7,8,9]
--
-- >>> run $ map (+1) (use xs)
-- Vector (Z :. 10) [1,2,3,4,5,6,7,8,9,10]
--
map :: forall sh a b.
       (Shape sh, Elt a, Elt b)
    => (Exp a -> Exp b)
    -> Acc (Array sh a)
    -> Acc (Array sh b)
map = Acc $$ applyAcc (Map (eltR @a) (eltR @b))

-- | Apply the given binary function element-wise to the two arrays. The extent
-- of the resulting array is the intersection of the extents of the two source
-- arrays.
--
-- >>> let xs = fromList (Z:.3:.5) [0..] :: Matrix Int
-- >>> xs
-- Matrix (Z :. 3 :. 5)
--   [  0,  1,  2,  3,  4,
--      5,  6,  7,  8,  9,
--     10, 11, 12, 13, 14]
--
-- >>> let ys = fromList (Z:.5:.10) [1..] :: Matrix Int
-- >>> ys
-- Matrix (Z :. 5 :. 10)
--   [  1,  2,  3,  4,  5,  6,  7,  8,  9, 10,
--     11, 12, 13, 14, 15, 16, 17, 18, 19, 20,
--     21, 22, 23, 24, 25, 26, 27, 28, 29, 30,
--     31, 32, 33, 34, 35, 36, 37, 38, 39, 40,
--     41, 42, 43, 44, 45, 46, 47, 48, 49, 50]
--
-- >>> run $ zipWith (+) (use xs) (use ys)
-- Matrix (Z :. 3 :. 5)
--   [  1,  3,  5,  7,  9,
--     16, 18, 20, 22, 24,
--     31, 33, 35, 37, 39]
--
-- If the input arrays are expected to have the same shape, use
-- 'zipWithChecked'.
--
zipWith :: forall sh a b c.
           (Shape sh, Elt a, Elt b, Elt c)
        => (Exp a -> Exp b -> Exp c)
        -> Acc (Array sh a)
        -> Acc (Array sh b)
        -> Acc (Array sh c)
zipWith = Acc $$$ applyAcc (ZipWith (eltR @a) (eltR @b) (eltR @c))

-- Reductions
-- ----------

-- | Reduction of the innermost dimension of an array of arbitrary rank.
--
-- The shape of the result obeys the property:
--
-- > shape (fold f z xs) == indexTail (shape xs)
--
-- The first argument needs to be an /associative/ function to enable an
-- efficient parallel implementation. The initial element does not need to be an
-- identity element of the combination function.
--
-- >>> let mat = fromList (Z:.5:.10) [0..] :: Matrix Int
-- >>> mat
-- Matrix (Z :. 5 :. 10)
--   [  0,  1,  2,  3,  4,  5,  6,  7,  8,  9,
--     10, 11, 12, 13, 14, 15, 16, 17, 18, 19,
--     20, 21, 22, 23, 24, 25, 26, 27, 28, 29,
--     30, 31, 32, 33, 34, 35, 36, 37, 38, 39,
--     40, 41, 42, 43, 44, 45, 46, 47, 48, 49]
--
-- >>> run $ fold (+) 42 (use mat)
-- Vector (Z :. 5) [87,187,287,387,487]
--
-- Reductions with non-commutative operators are supported. For example, the
-- following computes the maximum segment sum problem along each innermost
-- dimension of the array.
--
-- <https://en.wikipedia.org/wiki/Maximum_subarray_problem>
--
-- >>> :{
--   let maximumSegmentSum
--           :: forall sh e. (Shape sh, Num e, Ord e)
--           => Acc (Array (sh :. Int) e)
--           -> Acc (Array sh e)
--       maximumSegmentSum
--         = map (\(T4 x _ _ _) -> x)
--         . fold1 f
--         . map g
--         where
--           f :: (Num a, Ord a) => Exp (a,a,a,a) -> Exp (a,a,a,a) -> Exp (a,a,a,a)
--           f x y =
--             let T4 mssx misx mcsx tsx = x
--                 T4 mssy misy mcsy tsy = y
--             in
--             T4 (mssx `max` (mssy `max` (mcsx+misy)))
--                (misx `max` (tsx+misy))
--                (mcsy `max` (mcsx+tsy))
--                (tsx+tsy)
--           --
--           g :: (Num a, Ord a) => Exp a -> Exp (a,a,a,a)
--           g x = let y = max x 0
--                  in T4 y y y x
-- :}
--
-- >>> let vec = fromList (Z:.10) [-2,1,-3,4,-1,2,1,-5,4,0] :: Vector Int
-- >>> run $ maximumSegmentSum (use vec)
-- Scalar Z [6]
--
-- See also 'Data.Array.Accelerate.Data.Fold.Fold', which can be a useful way to
-- compute multiple results from a single reduction.
--
fold :: forall sh a.
        (Shape sh, Elt a)
     => (Exp a -> Exp a -> Exp a)
     -> Exp a
     -> Acc (Array (sh:.Int) a)
     -> Acc (Array sh a)
fold f (Exp x) = Acc . applyAcc (Fold (eltR @a) (unExpBinaryFunction f) (Just x))

-- | Variant of 'fold' that requires the innermost dimension of the array to be
-- non-empty and doesn't need an default value.
--
-- The shape of the result obeys the property:
--
-- > shape (fold f z xs) == indexTail (shape xs)
--
-- The first argument needs to be an /associative/ function to enable an
-- efficient parallel implementation, but does not need to be commutative.
--
fold1 :: forall sh a.
         (HasCallStack, Shape sh, Elt a)
      => (Exp a -> Exp a -> Exp a)
      -> Acc (Array (sh:.Int) a)
      -> Acc (Array sh a)
fold1 f =
  Acc . applyAcc (Fold (eltR @a) (unExpBinaryFunction f) Nothing)
  . assertBounds "Input of fold1 should be non-empty" (\xs -> let Exp sh = shape xs in innerNonEmpty (shapeR @sh) sh)

-- | Segmented reduction along the innermost dimension of an array. The
-- segment descriptor specifies the starting index (offset) along the
-- innermost dimension to the beginning of each logical sub-array.
--
-- The value in the output array at index i is the reduction of values
-- between the indices of the segment descriptor at index i and (i+1).
--
-- We have that:
--
-- > foldSeg f z xs seg  ==  foldSeg' f z xs (scanl (+) 0 seg)
--
-- @since 1.3.0.0
--
foldSeg'
    :: forall sh a i.
       (Shape sh, Elt a, Elt i, IsIntegral i, i ~ EltR i)
    => (Exp a -> Exp a -> Exp a)
    -> Exp a
    -> Acc (Array (sh:.Int) a)
    -> Acc (Segments i)
    -> Acc (Array (sh:.Int) a)
foldSeg' f (Exp x) = Acc $$ applyAcc (FoldSeg (integralType @i) (eltR @a) (unExpBinaryFunction f) (Just x))
-- TODO: Add assertion that segment offsets are monotone increasing (if it doesn't add too much overhead)

-- | Variant of 'foldSeg'' that requires /all/ segments of the reduced
-- array to be non-empty, and doesn't need a default value. The segment
-- descriptor specifies the offset to the beginning of each of the logical
-- sub-arrays.
--
-- @since 1.3.0.0
--
fold1Seg'
    :: forall sh a i.
       (Shape sh, Elt a, Elt i, IsIntegral i, i ~ EltR i)
    => (Exp a -> Exp a -> Exp a)
    -> Acc (Array (sh:.Int) a)
    -> Acc (Segments i)
    -> Acc (Array (sh:.Int) a)
fold1Seg' f = Acc $$ applyAcc (FoldSeg (integralType @i) (eltR @a) (unExpBinaryFunction f) Nothing)
-- TODO: Add assertion that segment offsets are *strictly* monotone increasing (if it doesn't add too much overhead)

-- Scan functions
-- --------------

-- | Data.List style left-to-right scan along the innermost dimension of an
-- arbitrary rank array. The first argument needs to be an /associative/
-- function to enable efficient parallel implementation. The initial value
-- (second argument) may be arbitrary.
--
-- >>> let vec = fromList (Z :. 10) [0..] :: Vector Int
-- >>> run $ scanl (+) 10 (use vec)
-- Vector (Z :. 11) [10,10,11,13,16,20,25,31,38,46,55]
--
-- >>> let mat = fromList (Z :. 4 :. 10) [0..] :: Matrix Int
-- >>> run $ scanl (+) 0 (use mat)
-- Matrix (Z :. 4 :. 11)
--   [ 0,  0,  1,  3,   6,  10,  15,  21,  28,  36,  45,
--     0, 10, 21, 33,  46,  60,  75,  91, 108, 126, 145,
--     0, 20, 41, 63,  86, 110, 135, 161, 188, 216, 245,
--     0, 30, 61, 93, 126, 160, 195, 231, 268, 306, 345]
--
scanl :: forall sh a.
         (Shape sh, Elt a)
      => (Exp a -> Exp a -> Exp a)
      -> Exp a
      -> Acc (Array (sh:.Int) a)
      -> Acc (Array (sh:.Int) a)
scanl f (Exp x) (Acc a) = Acc $ SmartAcc $ Scan LeftToRight (eltR @a) (unExpBinaryFunction f) (Just x) a

-- | Variant of 'scanl', where the last element (final reduction result) along
-- each dimension is returned separately. Denotationally we have:
--
-- > scanl' f e arr = (init res, unit (res!len))
-- >   where
-- >     len = shape arr
-- >     res = scanl f e arr
--
-- >>> let vec       = fromList (Z:.10) [0..] :: Vector Int
-- >>> let (res,sum) = run $ scanl' (+) 0 (use vec)
-- >>> res
-- Vector (Z :. 10) [0,0,1,3,6,10,15,21,28,36]
-- >>> sum
-- Scalar Z [45]
--
-- >>> let mat        = fromList (Z:.4:.10) [0..] :: Matrix Int
-- >>> let (res,sums) = run $ scanl' (+) 0 (use mat)
-- >>> res
-- Matrix (Z :. 4 :. 10)
--   [ 0,  0,  1,  3,   6,  10,  15,  21,  28,  36,
--     0, 10, 21, 33,  46,  60,  75,  91, 108, 126,
--     0, 20, 41, 63,  86, 110, 135, 161, 188, 216,
--     0, 30, 61, 93, 126, 160, 195, 231, 268, 306]
-- >>> sums
-- Vector (Z :. 4) [45,145,245,345]
--
scanl' :: forall sh a.
          (Shape sh, Elt a)
       => (Exp a -> Exp a -> Exp a)
       -> Exp a
       -> Acc (Array (sh:.Int) a)
       -> Acc (Array (sh:.Int) a, Array sh a)
scanl' = Acc . mkPairToTuple $$$ applyAcc (Scan' LeftToRight $ eltR @a)

-- | Data.List style left-to-right scan along the innermost dimension without an
-- initial value (aka inclusive scan). The innermost dimension of the array must
-- not be empty. The first argument must be an /associative/ function.
--
-- >>> let mat = fromList (Z:.4:.10) [0..] :: Matrix Int
-- >>> run $ scanl1 (+) (use mat)
-- Matrix (Z :. 4 :. 10)
--   [  0,  1,  3,   6,  10,  15,  21,  28,  36,  45,
--     10, 21, 33,  46,  60,  75,  91, 108, 126, 145,
--     20, 41, 63,  86, 110, 135, 161, 188, 216, 245,
--     30, 61, 93, 126, 160, 195, 231, 268, 306, 345]
--
scanl1 :: forall sh a.
          (Shape sh, Elt a)
       => (Exp a -> Exp a -> Exp a)
       -> Acc (Array (sh:.Int) a)
       -> Acc (Array (sh:.Int) a)
scanl1 f (Acc a) = Acc $ SmartAcc $ Scan LeftToRight (eltR @a) (unExpBinaryFunction f) Nothing a

-- | Right-to-left variant of 'scanl'.
--
scanr :: forall sh a.
         (Shape sh, Elt a)
      => (Exp a -> Exp a -> Exp a)
      -> Exp a
      -> Acc (Array (sh:.Int) a)
      -> Acc (Array (sh:.Int) a)
scanr f (Exp x) (Acc a) = Acc $ SmartAcc $ Scan RightToLeft (eltR @a) (unExpBinaryFunction f) (Just x) a

-- | Right-to-left variant of 'scanl''.
--
scanr' :: forall sh a.
          (Shape sh, Elt a)
       => (Exp a -> Exp a -> Exp a)
       -> Exp a
       -> Acc (Array (sh:.Int) a)
       -> Acc (Array (sh:.Int) a, Array sh a)
scanr' = Acc . mkPairToTuple $$$ applyAcc (Scan' RightToLeft $ eltR @a)

-- | Right-to-left variant of 'scanl1'.
--
scanr1 :: forall sh a.
          (Shape sh, Elt a)
       => (Exp a -> Exp a -> Exp a)
       -> Acc (Array (sh:.Int) a)
       -> Acc (Array (sh:.Int) a)
scanr1 f (Acc a) = Acc $ SmartAcc $ Scan RightToLeft (eltR @a) (unExpBinaryFunction f) Nothing a

permute'
    :: forall sh sh' a. (HasCallStack, Shape sh, Shape sh', Elt a)
    => (Exp a -> Exp a -> Exp a)        -- ^ combination function
    -> Acc (Array sh' a)                -- ^ array of default values
    -> Acc (Array sh  (Maybe (sh', a))) -- ^ array of source values to be permuted, alongside their target index
    -> Acc (Array sh' a)
permute' f def src = Acc $ applyAcc
  (Permute (arrayR @sh @a) $ Just $ unExpBinaryFunction f)
  def
  $ map (assertBounds "Write indices in permute should be in bounds of the defaults array" (\s@(Exp s') -> not (isJust s) ||! inboundsOf def (Exp $ prj1 $ prj0 $ prj0 s'))) src

permuteUnique'
    :: forall sh sh' a. (HasCallStack, Shape sh, Shape sh', Elt a)
    => Acc (Array sh' a)                -- ^ array of default values
    -> Acc (Array sh  (Maybe (sh', a))) -- ^ array of source values to be permuted, alongside their target index
    -> Acc (Array sh' a)
permuteUnique' def src = Acc $ applyAcc
  (Permute (arrayR @sh @a) Nothing)
  def
  $ map (assertBounds "Write indices in permute should be in bounds of the defaults array" (\s@(Exp s') -> not (isJust s) ||! inboundsOf def (Exp $ prj1 $ prj0 $ prj0 s'))) src

-- | Generalised backward permutation operation (array gather).
--
-- Backward permutation specified by a function mapping indices in the
-- destination array to indices in the source array. Elements of the output
-- array are thus generated by reading from the corresponding index in the
-- source array.
--
-- For example, backpermute can be used to
-- 'Data.Array.Accelerate.Prelude.transpose' a matrix; at every index @Z:.y:.x@
-- in the result array, we get the value at that index by reading from the
-- source array at index @Z:.x:.y@:
--
-- >>> :{
--   let swap :: Exp DIM2 -> Exp DIM2
--       swap = lift1 f
--         where
--           f :: Z :. Exp Int :. Exp Int -> Z :. Exp Int :. Exp Int
--           f (Z:.y:.x) = Z :. x :. y
-- :}
--
-- >>> let mat = fromList (Z:.5:.10) [0..] :: Matrix Int
-- >>> mat
-- Matrix (Z :. 5 :. 10)
--   [  0,  1,  2,  3,  4,  5,  6,  7,  8,  9,
--     10, 11, 12, 13, 14, 15, 16, 17, 18, 19,
--     20, 21, 22, 23, 24, 25, 26, 27, 28, 29,
--     30, 31, 32, 33, 34, 35, 36, 37, 38, 39,
--     40, 41, 42, 43, 44, 45, 46, 47, 48, 49]
--
-- >>> let mat' = use mat
-- >>> run $ backpermute (swap (shape mat')) swap mat'
-- Matrix (Z :. 10 :. 5)
--   [ 0, 10, 20, 30, 40,
--     1, 11, 21, 31, 41,
--     2, 12, 22, 32, 42,
--     3, 13, 23, 33, 43,
--     4, 14, 24, 34, 44,
--     5, 15, 25, 35, 45,
--     6, 16, 26, 36, 46,
--     7, 17, 27, 37, 47,
--     8, 18, 28, 38, 48,
--     9, 19, 29, 39, 49]
--
backpermute
    :: forall sh sh' a. (HasCallStack, Shape sh, Shape sh', Elt a)
    => Exp sh'                          -- ^ shape of the result array
    -> (Exp sh' -> Exp sh)              -- ^ index permutation function
    -> Acc (Array sh  a)                -- ^ source array
    -> Acc (Array sh' a)
backpermute sz f as =
  Acc $ applyAcc (Backpermute $ shapeR @sh') (assertBounds "Shape of backpermute should be non-negative" isNonNegative sz) f' as
  where
    f' ix = assertBounds "Indices in backpermute should be in bounds of the source array" (inboundsOf as) $ f ix

-- Stencil operations
-- ------------------

-- Common stencil types
--

-- DIM1 stencil type
type Stencil3 a = (Exp a, Exp a, Exp a)
type Stencil5 a = (Exp a, Exp a, Exp a, Exp a, Exp a)
type Stencil7 a = (Exp a, Exp a, Exp a, Exp a, Exp a, Exp a, Exp a)
type Stencil9 a = (Exp a, Exp a, Exp a, Exp a, Exp a, Exp a, Exp a, Exp a, Exp a)

-- DIM2 stencil type
type Stencil3x3 a = (Stencil3 a, Stencil3 a, Stencil3 a)
type Stencil5x3 a = (Stencil5 a, Stencil5 a, Stencil5 a)
type Stencil3x5 a = (Stencil3 a, Stencil3 a, Stencil3 a, Stencil3 a, Stencil3 a)
type Stencil5x5 a = (Stencil5 a, Stencil5 a, Stencil5 a, Stencil5 a, Stencil5 a)

-- DIM3 stencil type
type Stencil3x3x3 a = (Stencil3x3 a, Stencil3x3 a, Stencil3x3 a)
type Stencil5x3x3 a = (Stencil5x3 a, Stencil5x3 a, Stencil5x3 a)
type Stencil3x5x3 a = (Stencil3x5 a, Stencil3x5 a, Stencil3x5 a)
type Stencil3x3x5 a = (Stencil3x3 a, Stencil3x3 a, Stencil3x3 a, Stencil3x3 a, Stencil3x3 a)
type Stencil5x5x3 a = (Stencil5x5 a, Stencil5x5 a, Stencil5x5 a)
type Stencil5x3x5 a = (Stencil5x3 a, Stencil5x3 a, Stencil5x3 a, Stencil5x3 a, Stencil5x3 a)
type Stencil3x5x5 a = (Stencil3x5 a, Stencil3x5 a, Stencil3x5 a, Stencil3x5 a, Stencil3x5 a)
type Stencil5x5x5 a = (Stencil5x5 a, Stencil5x5 a, Stencil5x5 a, Stencil5x5 a, Stencil5x5 a)


-- | Map a stencil over an array. In contrast to 'map', the domain of a stencil
-- function is an entire /neighbourhood/ of each array element. Neighbourhoods
-- are sub-arrays centred around a focal point. They are not necessarily
-- rectangular, but they are symmetric and have an extent of at least three
-- along each axis. Due to the symmetry requirement the extent is necessarily
-- odd. The focal point is the array position that is determined by the stencil.
--
-- For those array positions where the neighbourhood extends past the boundaries
-- of the source array, a boundary condition determines the contents of the
-- out-of-bounds neighbourhood positions.
--
-- Stencil neighbourhoods are specified via nested tuples, where the nesting
-- depth is equal to the dimensionality of the array. For example, a 3x1 stencil
-- for a one-dimensional array:
--
-- > s31 :: Stencil3 a -> Exp a
-- > s31 (l,c,r) = ...
--
-- ...where @c@ is the focal point of the stencil, and @l@ and @r@ represent the
-- elements to the left and right of the focal point, respectively. Similarly,
-- a 3x3 stencil for a two-dimensional array:
--
-- > s33 :: Stencil3x3 a -> Exp a
-- > s33 ((_,t,_)
-- >     ,(l,c,r)
-- >     ,(_,b,_)) = ...
--
-- ...where @c@ is again the focal point and @t@, @b@, @l@ and @r@ are the
-- elements to the top, bottom, left, and right of the focal point, respectively
-- (the diagonal elements have been elided).
--
-- For example, the following computes a 5x5
-- <https://en.wikipedia.org/wiki/Gaussian_blur Gaussian blur> as a separable
-- 2-pass operation.
--
-- > type Stencil5x1 a = (Stencil3 a, Stencil5 a, Stencil3 a)
-- > type Stencil1x5 a = (Stencil3 a, Stencil3 a, Stencil3 a, Stencil3 a, Stencil3 a)
-- >
-- > convolve5x1 :: Num a => [Exp a] -> Stencil5x1 a -> Exp a
-- > convolve5x1 kernel (_, (a,b,c,d,e), _)
-- >   = Prelude.sum $ Prelude.zipWith (*) kernel [a,b,c,d,e]
-- >
-- > convolve1x5 :: Num a => [Exp a] -> Stencil1x5 a -> Exp a
-- > convolve1x5 kernel ((_,a,_), (_,b,_), (_,c,_), (_,d,_), (_,e,_))
-- >   = Prelude.sum $ Prelude.zipWith (*) kernel [a,b,c,d,e]
-- >
-- > gaussian = [0.06136,0.24477,0.38774,0.24477,0.06136]
-- >
-- > blur :: Num a => Acc (Matrix a) -> Acc (Matrix a)
-- > blur = stencil (convolve5x1 gaussian) clamp
-- >      . stencil (convolve1x5 gaussian) clamp
--
-- [/Note:/]
--
-- Since accelerate-1.3.0.0, we allow the source array to fuse into the stencil
-- operation. However, since a stencil computation (typically) requires multiple
-- values from the source array, this means that the work of the fused operation
-- will be duplicated for each element in the stencil pattern.
--
-- For example, suppose we write:
--
-- > blur . map f
--
-- The operation `f` will be fused into each element of the first Gaussian blur
-- kernel, resulting in a stencil equivalent to:
--
-- > f_and_convolve1x5 :: Num a => (Exp a -> Exp b) -> [Exp b] -> Stencil1x5 a -> Exp b
-- > f_and_convolve1x5 f kernel ((_,a,_), (_,b,_), (_,c,_), (_,d,_), (_,e,_))
-- >   = Prelude.sum $ Prelude.zipWith (*) kernel [f a, f b, f c, f d, f e]
--
-- This duplication is often beneficial, however you may choose to instead force
-- the array to be evaluated first, preventing fusion, using the
-- `Data.Array.Accelerate.Prelude.compute` operation. Benchmarking should reveal
-- which approach is best for your application.
--
stencil
    :: forall sh stencil a b.
       (Stencil sh a stencil, Elt b)
    => (stencil -> Exp b)                     -- ^ stencil function
    -> Boundary (Array sh a)                  -- ^ boundary condition
    -> Acc (Array sh a)                       -- ^ source array
    -> Acc (Array sh b)                       -- ^ destination array
stencil f (Boundary b) (Acc a)
-- TODO: Do boundary conditions put requirements on the input size?
-- We should add an 'assert' to check whether the size is large enough for the
-- chosen boundary condition.
  = Acc $ SmartAcc $ Stencil
      (stencilR @sh @a @stencil)
      (eltR @b)
      (unExp . f . stencilPrj @sh @a @stencil)
      b
      a

-- | Map a binary stencil of an array. The extent of the resulting array is the
-- intersection of the extents of the two source arrays. This is the stencil
-- equivalent of 'zipWith'.
--
stencil2
    :: forall sh stencil1 stencil2 a b c.
       (Stencil sh a stencil1, Stencil sh b stencil2, Elt c)
    => (stencil1 -> stencil2 -> Exp c)        -- ^ binary stencil function
    -> Boundary (Array sh a)                  -- ^ boundary condition #1
    -> Acc (Array sh a)                       -- ^ source array #1
    -> Boundary (Array sh b)                  -- ^ boundary condition #2
    -> Acc (Array sh b)                       -- ^ source array #2
    -> Acc (Array sh c)                       -- ^ destination array
stencil2 f (Boundary b1) (Acc a1) (Boundary b2) (Acc a2)
  = Acc $ SmartAcc $ Stencil2
      (stencilR @sh @a @stencil1)
      (stencilR @sh @b @stencil2)
      (eltR @c)
      (\x y -> unExp $ f (stencilPrj @sh @a @stencil1 x) (stencilPrj @sh @b @stencil2 y))
      b1
      a1
      b2
      a2

-- | Boundary condition where elements of the stencil which would be
-- out-of-bounds are instead clamped to the edges of the array.
--
-- In the following 3x3 stencil, the out-of-bounds element @b@ will instead
-- return the value at position @c@:
--
-- >   +------------+
-- >   |a           |
-- >  b|cd          |
-- >   |e           |
-- >   +------------+
--
clamp :: Boundary (Array sh e)
clamp = Boundary Clamp

-- | Stencil boundary condition where coordinates beyond the array extent are
-- instead mirrored
--
-- In the following 5x3 stencil, the out-of-bounds element @c@ will instead
-- return the value at position @d@, and similarly the element at @b@ will
-- return the value at @e@:
--
-- >   +------------+
-- >   |a           |
-- > bc|def         |
-- >   |g           |
-- >   +------------+
--
mirror :: Boundary (Array sh e)
mirror = Boundary Mirror

-- | Stencil boundary condition where coordinates beyond the array extent
-- instead wrap around the array (circular boundary conditions).
--
-- In the following 3x3 stencil, the out of bounds elements will be read as in
-- the pattern on the right.
--
-- >  a bc
-- >   +------------+      +------------+
-- >  d|ef          |      |ef         d|
-- >  g|hi          |  ->  |hi         g|
-- >   |            |      |bc         a|
-- >   +------------+      +------------+
--
wrap :: Boundary (Array sh e)
wrap = Boundary Wrap

-- | Stencil boundary condition where the given function is applied to any
-- outlying coordinates.
--
-- The function is passed the out-of-bounds index, so you can use it to specify
-- different boundary conditions at each side. For example, the following would
-- clamp out-of-bounds elements in the y-direction to zero, while having
-- circular boundary conditions in the x-direction.
--
-- > ring :: Acc (Matrix Float) -> Acc (Matrix Float)
-- > ring xs = stencil f boundary xs
-- >   where
-- >     boundary :: Boundary (Matrix Float)
-- >     boundary = function $ \(unlift -> Z :. y :. x) ->
-- >       if y < 0 || y >= height
-- >         then 0
-- >         else if x < 0
-- >                then xs ! index2 y (width+x)
-- >                else xs ! index2 y (x-width)
-- >
-- >     f :: Stencil3x3 Float -> Exp Float
-- >     f = ...
-- >
-- >     Z :. height :. width = unlift (shape xs)
--
function
    :: forall sh e. (Shape sh, Elt e)
    => (Exp sh -> Exp e)
    -> Boundary (Array sh e)
function f = Boundary $ Function (f')
  where
    f' :: SmartExp (EltR sh) -> SmartExp (EltR e)
    f' = unExp . f . Exp


{--
-- Sequence operations
-- ------------------

-- Common sequence types
--

streamIn :: Arrays a
         => [a]
         -> Seq [a]
streamIn arrs = Seq (StreamIn arrs)

-- | Convert the given array to a sequence by dividing the array up into subarrays.
-- The first argument captures how to the division should be performed. The
-- presence of `All` in the division descriptor indicates that elements in the
-- corresponding dimension should be retained in the subarrays, whereas `Split`
-- indicates that the input array should divided along this dimension.
--
toSeq :: (Division slsix, Elt a)
      => slsix
      -> Acc (Array (FullShape (DivisionSlice slsix)) a)
      -> Seq [Array (SliceShape (DivisionSlice slsix)) a]
toSeq spec acc = Seq (ToSeq spec acc)

-- | Apply the given array function element-wise to the given sequence.
--
mapSeq :: (Arrays a, Arrays b)
       => (Acc a -> Acc b)
       -> Seq [a]
       -> Seq [b]
mapSeq = Seq $$ MapSeq

-- | Apply the given binary function element-wise to the two sequences.  The length of the resulting
-- sequence is the minumum of the lengths of the two source sequences.
--
zipWithSeq :: (Arrays a, Arrays b, Arrays c)
           => (Acc a -> Acc b -> Acc c)
           -> Seq [a]
           -> Seq [b]
           -> Seq [c]
zipWithSeq = Seq $$$ ZipWithSeq

-- | scanSeq (+) a0 x seq. Scan a sequence x by combining each
-- element using the given binary operation (+). (+) must be
-- associative:
--
--   Forall a b c. (a + b) + c = a + (b + c),
--
-- and a0 must be the identity element for (+):
--
--   Forall a. a0 + a = a = a + a0.
--
scanSeq :: Elt a
        => (Exp a -> Exp a -> Exp a)
        -> Exp a
        -> Seq [Scalar a]
        -> Seq [Scalar a]
scanSeq = Seq $$$ ScanSeq

-- | foldSeq (+) a0 x seq. Fold a sequence x by combining each
-- element using the given binary operation (+). (+) must be
-- associative:
--
--   Forall a b c. (a + b) + c = a + (b + c),
--
-- and a0 must be the identity element for (+):
--
--   Forall a. a0 + a = a = a + a0.
--
foldSeq :: Elt a
        => (Exp a -> Exp a -> Exp a)
        -> Exp a
        -> Seq [Scalar a]
        -> Seq (Scalar a)
foldSeq = Seq $$$ FoldSeq

-- | foldSeqFlatten f a0 x seq. A specialized version of
-- FoldSeqAct where reduction with the companion operator
-- corresponds to flattening. f must be semi-associative, with vecotor
-- append (++) as the companion operator:
--
--   Forall b sh1 a1 sh2 a2.
--     f (f b sh1 a1) sh2 a2 = f b (sh1 ++ sh2) (a1 ++ a2).
--
-- It is common to ignore the shape vectors, yielding the usual
-- semi-associativity law:
--
--   f b a _ = b + a,
--
-- for some (+) satisfying:
--
--   Forall b a1 a2. (b + a1) + a2 = b + (a1 ++ a2).
--
foldSeqFlatten :: (Arrays a, Shape jx, Elt b)
               => (Acc a -> Acc (Vector jx) -> Acc (Vector b) -> Acc a)
               -> Acc a
               -> Seq [Array jx b]
               -> Seq a
foldSeqFlatten = Seq $$$ FoldSeqFlatten

collect :: Arrays arrs => Seq arrs -> Acc arrs
collect = Acc . Collect
--}


-- Foreign function calling
-- ------------------------

-- | Call a foreign array function.
--
-- The form the first argument takes is dependent on the backend being targeted.
-- Note that the foreign function only has access to the input array(s) passed
-- in as its argument.
--
-- In case the operation is being executed on a backend which does not support
-- this foreign implementation, the fallback implementation is used instead,
-- which itself could be a foreign implementation for a (presumably) different
-- backend, or an implementation in pure Accelerate. In this way, multiple
-- foreign implementations can be supplied, and will be tested for suitability
-- against the target backend in sequence.
--
-- For an example see the <https://hackage.haskell.org/package/accelerate-fft accelerate-fft> package.
--
foreignAcc
    :: forall as bs asm. (Arrays as, Arrays bs, Foreign asm)
    => asm (ArraysR as -> ArraysR bs)
    -> (Acc as -> Acc bs)
    -> Acc as
    -> Acc bs
foreignAcc asm f (Acc as) = Acc $ SmartAcc $ Aforeign (arraysR @bs) asm (unAccFunction f) as

-- | Call a foreign scalar expression.
--
-- The form of the first argument is dependent on the backend being targeted.
-- Note that the foreign function only has access to the input element(s) passed
-- in as its first argument.
--
-- As with 'foreignAcc', the fallback implementation itself may be a (sequence
-- of) foreign implementation(s) for a different backend(s), or implemented
-- purely in Accelerate.
--
foreignExp
    :: forall x y asm. (Elt x, Elt y, Foreign asm)
    => asm (EltR x -> EltR y)
    -> (Exp x -> Exp y)
    -> Exp x
    -> Exp y
foreignExp asm f (Exp x) = mkExp $ Foreign (eltR @y) asm (unExpFunction f) x


-- Controlling execution
-- ---------------------

-- | Force an array expression to be evaluated, preventing it from fusing with
-- other operations. Forcing operations to be computed to memory, rather than
-- being fused into their consuming function, can sometimes improve performance.
-- For example, computing a matrix 'transpose' could provide better memory
-- locality for the subsequent operation. Preventing fusion to split large
-- operations into several simpler steps could also help by reducing register
-- pressure.
--
-- Preventing fusion also means that the individual operations are available to
-- be executed concurrently with other kernels. In particular, consider using
-- this if you have a series of operations that are compute bound rather than
-- memory bound.
--
-- Here is the synthetic example:
--
-- > loop :: Exp Int -> Exp Int
-- > loop ticks =
-- >   let clockRate = 900000   -- kHz
-- >   in  while (\i -> i < clockRate * ticks) (+1) 0
-- >
-- > test :: Acc (Vector Int)
-- > test =
-- >   zip3
-- >     (compute $ map loop (use $ fromList (Z:.1) [10]))
-- >     (compute $ map loop (use $ fromList (Z:.1) [10]))
-- >     (compute $ map loop (use $ fromList (Z:.1) [10]))
-- >
--
-- Without the use of 'compute', the operations are fused together and the three
-- long-running loops are executed sequentially in a single kernel. Instead, the
-- individual operations can now be executed concurrently, potentially reducing
-- overall runtime.
--
compute :: Arrays a => Acc a -> Acc a
compute (Acc a) = Acc $ SmartAcc $ Manifest a


-- Flow control constructs
-- -----------------------

-- | An array-level if-then-else construct.
--
-- Enabling the @RebindableSyntax@ extension will allow you to use the standard
-- if-then-else syntax instead.
--
acond :: Arrays a
      => Exp Bool               -- ^ if-condition
      -> Acc a                  -- ^ then-array
      -> Acc a                  -- ^ else-array
      -> Acc a
acond (Exp p) = Acc $$ applyAcc $ Acond (mkCoerce' p)

-- | An array-level 'while' construct. Continue to apply the given function,
-- starting with the initial value, until the test function evaluates to
-- 'False'.
--
awhile :: forall a. Arrays a
       => (Acc a -> Acc (Scalar Bool))    -- ^ keep evaluating while this returns 'True'
       -> (Acc a -> Acc a)                -- ^ function to apply
       -> Acc a                           -- ^ initial value
       -> Acc a
awhile f = Acc $$ applyAcc $ Awhile (arraysR @a) (unAccFunction g)
  where
    -- FIXME: This should be a no-op!
    g :: Acc a -> Acc (Scalar PrimBool)
    g = map mkCoerce . f


-- Shapes and indices
-- ------------------

-- | Map a multi-dimensional index into a linear, row-major representation of an
-- array.
--
toIndex
    :: forall sh. (HasCallStack, Shape sh)
    => Exp sh                     -- ^ extent of the array
    -> Exp sh                     -- ^ index to remap
    -> Exp Int
toIndex sh@(Exp sh') ix = mkExp $ ToIndex (shapeR @sh) sh' ix'
  where Exp ix' = assertBounds "Index in toIndex should be in bounds of the given shape" (inbounds sh) ix

-- | Inverse of 'toIndex'
--
fromIndex :: forall sh. (HasCallStack, Shape sh) => Exp sh -> Exp Int -> Exp sh
fromIndex sh@(Exp sh') e = mkExp $ FromIndex (shapeR @sh) sh' e'
  where Exp e' = assertBounds "Integer in fromIndex should be in bounds of the given shape" (\s -> s >= 0 &&! s < shapeSize sh) e

-- | Intersection of two shapes
--
intersect :: forall sh. Shape sh => Exp sh -> Exp sh -> Exp sh
intersect (Exp shx) (Exp shy) = Exp $ intersect' (shapeR @sh) shx shy
  where
    intersect' :: ShapeR t -> SmartExp t -> SmartExp t -> SmartExp t
    intersect' ShapeRz _ _ = SmartExp Nil
    intersect' (ShapeRsnoc shR) (unPair -> (xs, x)) (unPair -> (ys, y))
      = SmartExp
      $ intersect' shR xs ys `Pair`
        SmartExp (PrimApp (PrimMin singleType) $ SmartExp $ Pair x y)


-- | Union of two shapes
--
union :: forall sh. Shape sh => Exp sh -> Exp sh -> Exp sh
union (Exp shx) (Exp shy) = Exp $ union' (shapeR @sh) shx shy
  where
    union' :: ShapeR t -> SmartExp t -> SmartExp t -> SmartExp t
    union' ShapeRz _ _ = SmartExp Nil
    union' (ShapeRsnoc shR) (unPair -> (xs, x)) (unPair -> (ys, y))
      = SmartExp
      $ union' shR xs ys `Pair`
        SmartExp (PrimApp (PrimMax singleType) $ SmartExp $ Pair x y)


-- Flow-control
-- ------------

-- | A scalar-level if-then-else construct.
--
-- Enabling the @RebindableSyntax@ extension will allow you to use the standard
-- if-then-else syntax instead.
--
cond :: Elt t
     => Exp Bool                -- ^ condition
     -> Exp t                   -- ^ then-expression
     -> Exp t                   -- ^ else-expression
     -> Exp t
cond (Exp c) (Exp x) (Exp y) = mkExp $ Cond (mkCoerce' c) x y

-- | A scalar-level conditional expression
-- that chooses one value based on the condition without branching.
select :: (Elt t)
       => Exp Bool                -- ^ condition
       -> Exp t                   -- ^ then-expression
       -> Exp t                   -- ^ else-expression
       -> Exp t
select (Exp c) (Exp x) (Exp y) = mkExp $ Select (mkCoerce' c) x y

-- | While construct. Continue to apply the given function, starting with the
-- initial value, until the test function evaluates to 'False'.
--
while :: forall e. Elt e
      => (Exp e -> Exp Bool)    -- ^ keep evaluating while this returns 'True'
      -> (Exp e -> Exp e)       -- ^ function to apply
      -> Exp e                  -- ^ initial value
      -> Exp e
while c f (Exp e) =
  mkExp $ While @(EltR e) (eltR @e)
            (mkCoerce' . unExp . c . Exp)
            (unExp . f . Exp) e

class Assert a where
  -- | Verifies whether a predicate holds. The predicate is evaluated before
  -- the result of this function is used, and the program will crash if the
  -- predicate returns false.
  --
  -- Note that the predicate is only guaranteed to run if the result of this
  -- function is used. If the result is not used, it may (or may not) be
  -- removed from the program.
  --
  assert :: HasCallStack => (a -> Exp Bool) -> a -> a

  -- | Verifies whether a predicate holds. Similar to 'assert', but this
  -- function also takes a message, which is printed when the assertion
  -- fails.
  --
  assertMessage :: HasCallStack => Text -> (a -> Exp Bool) -> a -> a
  
  -- | Informs the compiler that a certain property holds on the given value.
  -- The compiler may use this information to optimize the program.
  --
  assume :: (a -> Exp Bool) -> a -> a

-- | Variant of 'assert' that only adds an assertion when bounds checks are
-- enabled via the flag bounds-checks.
--
-- This function may be removed in the future and replaced by the regular
-- 'assert', if we decide to turn bounds checks on by default.
--
assertBounds :: (HasCallStack, Assert a) => Text -> (a -> Exp Bool) -> a -> a
#ifdef ACCELERATE_BOUNDS_CHECKS
assertBounds = withFrozenCallStack assertMessage
#else
assertBounds _ _ a = a
#endif

instance Elt t => Assert (Exp t) where
  assert f (Exp e) = mkExp $ Assert (fromString (prettyCallStack callStack)) (mkCoerce' g) e
    where Exp g = f $ Exp e
  assertMessage msg f (Exp e) = mkExp $ Assert (msg <> "\n" <> fromString (prettyCallStack callStack)) (mkCoerce' g) e
    where Exp g = f $ Exp e
  assume f (Exp e) = mkExp $ Assume (mkCoerce' g) e
    where Exp g = f $ Exp e

instance Arrays t => Assert (Acc t) where
  assert f (Acc a) = Acc $ SmartAcc $ Aassert (fromString (prettyCallStack callStack)) (mkCoerce' g) a
    where Exp g = f $ Acc a
  assertMessage msg f (Acc a) = Acc $ SmartAcc $ Aassert (msg <> "\n" <> fromString (prettyCallStack callStack)) (mkCoerce' g) a
    where Exp g = f $ Acc a
  assume f (Acc a) = Acc $ SmartAcc $ Aassume (mkCoerce' g) a
    where Exp g = f $ Acc a

-- Some conditions for assertions that we use for the built-in functions of Accelerate

-- | Checks whether the innermost dimension is non-empty,
-- or if the other dimensions are empty. fold1 requires this:
-- It folds per row, so the rows must be non-empty.
-- However, if there are no rows, the size of rows is irrelevant,
-- hence we also check for that.
innerNonEmpty :: ShapeR sh -> SmartExp (sh, Int) -> Exp Bool
innerNonEmpty shr sh = isEmpty shr (prjTail sh) ||! (Exp (prj0 sh) :: Exp Int) > 0

isEmpty :: ShapeR sh -> SmartExp sh -> Exp Bool
isEmpty ShapeRz _ = False_
isEmpty (ShapeRsnoc shr) sh = isEmpty shr (prjTail sh) ||! (Exp (prj0 sh) :: Exp Int) == 0

isNonNegative :: forall sh. Shape sh => Exp sh -> Exp Bool
isNonNegative (Exp sh) = isNonNegative' (shapeR @sh) sh

isNonNegative' :: ShapeR sh -> SmartExp sh -> Exp Bool
isNonNegative' ShapeRz _ = True_
isNonNegative' (ShapeRsnoc shr) sh = isNonNegative' shr (prjTail sh) &&! (Exp (prj0 sh) :: Exp Int) >= 0

-- | Given the size (of an array), checks whether an index is in bounds.
--
inbounds :: forall sh. Shape sh => Exp sh -> Exp sh -> Exp Bool
inbounds (Exp shape') (Exp index) = go (shapeR @sh) shape' index
  where
    go :: ShapeR s -> SmartExp s -> SmartExp s -> Exp Bool
    go ShapeRz _ _ = True_
    go (ShapeRsnoc shr) sh ix =
      go shr (prjTail sh) (prjTail ix) &&! 0 <= (Exp (prj0 ix) :: Exp Int) &&! (Exp (prj0 ix) :: Exp Int) < Exp (prj0 sh)

-- | Given an array, checks whether an index is in bounds of that array.
--
inboundsOf :: (Shape sh, Elt e) => Acc (Array sh e) -> Exp sh -> Exp Bool
inboundsOf = inbounds . shape

-- | Checks whether two shapes are equal.
-- This function is equal to (==), but has a Shape constraint instead of an Eq
-- constraint.
--
shapeEq :: forall sh. Shape sh => Exp sh -> Exp sh -> Exp Bool
shapeEq (Exp sh1) (Exp sh2) = shapeEq' (shapeR @sh) sh1 sh2

shapeEq' :: ShapeR sh -> SmartExp sh -> SmartExp sh -> Exp Bool
shapeEq' ShapeRz _ _ = True_
shapeEq' (ShapeRsnoc shr) sh1 sh2 =
  shapeEq' shr (prjTail sh1) (prjTail sh2) &&! (Exp (prj0 sh1) :: Exp Int) == (Exp (prj0 sh2) :: Exp Int)

-- Array operations with a scalar result
-- -------------------------------------

-- | Multidimensional array indexing. Extract the value from an array at the
-- specified zero-based index.
--
-- >>> let mat = fromList (Z:.5:.10) [0..] :: Matrix Int
-- >>> mat
-- Matrix (Z :. 5 :. 10)
--   [  0,  1,  2,  3,  4,  5,  6,  7,  8,  9,
--     10, 11, 12, 13, 14, 15, 16, 17, 18, 19,
--     20, 21, 22, 23, 24, 25, 26, 27, 28, 29,
--     30, 31, 32, 33, 34, 35, 36, 37, 38, 39,
--     40, 41, 42, 43, 44, 45, 46, 47, 48, 49]
--
-- >>> runExp $ use mat ! constant (Z:.1:.2)
-- 12
--
infixl 9 !
(!) :: forall sh e. (HasCallStack, Shape sh, Elt e) => Acc (Array sh e) -> Exp sh -> Exp e
a@(Acc a') ! ix = mkExp $ Index (eltR @e) a' ix'
  where Exp ix' = assertBounds "Index in (!) should be in bounds of the array" (inboundsOf a) ix

-- | Extract the value from an array at the specified linear index.
-- Multidimensional arrays in Accelerate are stored in row-major order with
-- zero-based indexing.
--
-- >>> let mat = fromList (Z:.5:.10) [0..] :: Matrix Int
-- >>> mat
-- Matrix (Z :. 5 :. 10)
--   [  0,  1,  2,  3,  4,  5,  6,  7,  8,  9,
--     10, 11, 12, 13, 14, 15, 16, 17, 18, 19,
--     20, 21, 22, 23, 24, 25, 26, 27, 28, 29,
--     30, 31, 32, 33, 34, 35, 36, 37, 38, 39,
--     40, 41, 42, 43, 44, 45, 46, 47, 48, 49]
--
-- >>> runExp $ use mat !! 12
-- 12
--
infixl 9 !!
(!!) :: forall sh e. (HasCallStack, Shape sh, Elt e) => Acc (Array sh e) -> Exp Int -> Exp e
a@(Acc a') !! ix = mkExp $ LinearIndex (eltR @e) a' ix'
  where Exp ix' = assertBounds "Index in (!!) should be in bounds of the array" (\i -> 0 <= i &&! i < size a) ix

-- | Extract the shape (extent) of an array.
--
shape :: forall sh e. (Shape sh, Elt e) => Acc (Array sh e) -> Exp sh
shape = mkExp . Shape (shapeR @sh) . unAcc

-- | The number of elements in the array
--
size :: (Shape sh, Elt e) => Acc (Array sh e) -> Exp Int
size = shapeSize . shape

-- | The number of elements that would be held by an array of the given shape.
--
shapeSize :: forall sh. Shape sh => Exp sh -> Exp Int
shapeSize (Exp sh) = mkExp $ ShapeSize (shapeR @sh) sh

-- | Test whether an array is empty.
--
null :: forall sh e. (Shape sh, Elt e) => Acc (Array sh e) -> Exp Bool
null arr = isEmpty (shapeR @sh) sh
  where
    Exp sh = shape arr

-- Numeric functions
-- -----------------

-- | 'subtract' is the same as @'flip' ('-')@.
--
subtract :: Num a => Exp a -> Exp a -> Exp a
subtract x y = y - x

-- | Determine if a number is even
--
even :: Integral a => Exp a -> Exp Bool
even n = n `rem` 2 == 0

-- | Determine if a number is odd
--
odd :: Integral a => Exp a -> Exp Bool
odd n = n `rem` 2 /= 0

-- | @'gcd' x y@ is the non-negative factor of both @x@ and @y@ of which every
-- common factor of both @x@ and @y@ is also a factor; for example:
--
-- > gcd 4 2 = 2
-- > gcd (-4) 6 = 2
-- > gcd 0 4 = 4
-- > gcd 0 0 = 0
--
-- That is, the common divisor that is \"greatest\" in the divisibility
-- preordering.
--
gcd :: Integral a => Exp a -> Exp a -> Exp a
gcd x y = gcd' (abs x) (abs y)
  where
    gcd' :: Integral a => Exp a -> Exp a -> Exp a
    gcd' u v =
      let T2 r _ = while (\(T2 _ b) -> b /= 0)
                         (\(T2 a b) -> T2 b (a `rem` b))
                         (T2 u v)
      in r


-- | @'lcm' x y@ is the smallest positive integer that both @x@ and @y@ divide.
--
lcm :: Integral a => Exp a -> Exp a -> Exp a
lcm x y
  = cond (x == 0 || y == 0) 0
  $ abs ((x `quot` (gcd x y)) * y)


-- | Raise a number to a non-negative integral power
--
infixr 8 ^
(^) :: forall a b. (Num a, Integral b) => Exp a -> Exp b -> Exp a
x0 ^ y0 = cond (y0 <= 0) 1 (f x0 y0)
  where
    f :: Exp a -> Exp b -> Exp a
    f x y =
      let T2 x' y' = while (\(T2 _ v) -> even v)
                           (\(T2 u v) -> T2 (u * u) (v `quot` 2))
                           (T2 x y)
      in
      cond (y' == 1) x' (g (x'*x') ((y'-1) `quot` 2) x')

    g :: Exp a -> Exp b -> Exp a -> Exp a
    g x y z =
      let T3 x' _ z' = while (\(T3 _ v _) -> v /= 1)
                             (\(T3 u v w) ->
                               cond (even v) (T3 (u*u) (v     `quot` 2) w)
                                             (T3 (u*u) ((v-1) `quot` 2) (w*u)))
                             (T3 x y z)
      in
      x' * z'

-- | Raise a number to an integral power
--
infixr 8 ^^
(^^) :: (Fractional a, Integral b) => Exp a -> Exp b -> Exp a
x ^^ n
  = cond (n >= 0)
  {- then -} (x ^ n)
  {- else -} (recip (x ^ (negate n)))


-- Conversions
-- -----------

-- |Convert a character to an 'Int'.
--
ord :: Exp Char -> Exp Int
ord = mkFromIntegral

-- |Convert an 'Int' into a character.
--
chr :: Exp Int -> Exp Char
chr = mkFromIntegral

-- |Convert a Boolean value to an 'Int', where 'False' turns into '0' and 'True'
-- into '1'.
--
boolToInt :: Exp Bool -> Exp Int
boolToInt = mkFromIntegral . mkCoerce @_ @Word8

-- |Reinterpret a value as another type. The two representations must have the
-- same bit size.
--
bitcast
    :: (Elt a, Elt b, IsScalar (EltR a), IsScalar (EltR b), BitSizeEq (EltR a) (EltR b))
    => Exp a
    -> Exp b
bitcast = mkBitcast

-- | Returns 'True' if the argument is of the form @Just _@
--
isJust :: Elt a => Exp (Maybe a) -> Exp Bool
isJust (Exp x) = Exp $ SmartExp $ (SmartExp $ Prj PairIdxLeft x) `Pair` SmartExp Nil
  -- TLM: This is a sneaky hack because we know that the tag bits for Just
  -- and True are identical.

