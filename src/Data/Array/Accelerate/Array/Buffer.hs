{-# LANGUAGE BangPatterns         #-}
{-# LANGUAGE CPP                  #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE MagicHash            #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UnboxedTuples        #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_HADDOCK hide #-}
-- |
-- Module      : Data.Array.Accelerate.Array.Buffer
-- Copyright   : [2008..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--
-- This module fixes the concrete representation of Accelerate arrays.  We
-- allocate all arrays using pinned memory to enable safe direct-access by
-- non-Haskell code in multi-threaded code.  In particular, we can safely pass
-- pointers to an array's payload to foreign code.
--

module Data.Array.Accelerate.Array.Buffer (

  -- * Array operations and representations
  Buffers, Buffer(..), MutableBuffers, MutableBuffer(..), ScalarArrayDataR,
  runBuffers,
  newBuffers, newBuffer,
  indexBuffers, indexBuffers', indexBuffer, readBuffers, readBuffer, writeBuffers, writeBuffer,
  touchBuffers, touchBuffer, touchMutableBuffers, touchMutableBuffer,
  rnfBuffers, rnfBuffer, unsafeFreezeBuffer, unsafeFreezeBuffers,
  veryUnsafeUnfreezeBuffers, bufferToList,

  -- * Type macros
  HTYPE_INT, HTYPE_WORD, HTYPE_CLONG, HTYPE_CULONG, HTYPE_CCHAR,

  -- * Allocator internals
  registerForeignPtrAllocator,

  -- * Utilities for type classes
  SingleArrayDict(..), singleArrayDict,
  ScalarArrayDict(..), scalarArrayDict,

  -- * TemplateHaskell
  liftBuffers, liftBuffer,
) where

import Data.Array.Accelerate.Array.Unique
import Data.Array.Accelerate.Error
import Data.Array.Accelerate.Representation.Type
import Data.Array.Accelerate.Type
import Data.Primitive.Vec
#ifdef ACCELERATE_DEBUG
import Data.Array.Accelerate.Lifetime
#endif

import Data.Array.Accelerate.Debug.Internal.Flags
import Data.Array.Accelerate.Debug.Internal.Profile
import Data.Array.Accelerate.Debug.Internal.Trace

import Control.Applicative
import Control.DeepSeq
import Control.Monad                                                ( (<=<) )
import Data.Bits
import Data.IORef
import Data.Primitive                                               ( sizeOf# )
import Data.Typeable                                                ( (:~:)(..) )
import Foreign.ForeignPtr
import Foreign.Storable
import Formatting                                                   hiding ( bytes )
import Language.Haskell.TH.Extra                                    hiding ( Type )
import System.IO.Unsafe
import Prelude                                                      hiding ( mapM )

import GHC.Exts                                                     hiding ( build )
import GHC.ForeignPtr
import GHC.Types

-- | A buffer is a piece of memory representing one of the fields
-- of the SoA of an array. It does not have a multi-dimensional size,
-- e.g. the shape of the array should be stored elsewhere.
-- Replaces the former 'ScalarArrayData' type synonym.
--
data Buffer e = Buffer Int (UniqueArray (ScalarArrayDataR e))

-- | A structure of buffers represents an array, corresponding to the SoA conversion.
-- NOTE: We use a standard (non-strict) pair to enable lazy device-host data transfers.
-- Replaces the old 'ArrayData' and 'MutableArrayData' type aliasses and the
-- 'GArrayDataR' type family.
--
type Buffers e = Distribute Buffer e

data MutableBuffer e = MutableBuffer Int (UniqueArray (ScalarArrayDataR e))

type MutableBuffers e = Distribute MutableBuffer e

-- | Mapping from scalar type to the type as represented in memory in an
-- array.
--
type family ScalarArrayDataR t where
  {- ScalarArrayDataR Int       = Int
  ScalarArrayDataR Int8      = Int8
  ScalarArrayDataR Int16     = Int16
  ScalarArrayDataR Int32     = Int32
  ScalarArrayDataR Int64     = Int64
  ScalarArrayDataR Word      = Word
  ScalarArrayDataR Word8     = Word8
  ScalarArrayDataR Word16    = Word16
  ScalarArrayDataR Word32    = Word32
  ScalarArrayDataR Word64    = Word64
  ScalarArrayDataR Half      = Half
  ScalarArrayDataR Float     = Float
  ScalarArrayDataR Double    = Double -}
  ScalarArrayDataR (Vec n t) = t
  ScalarArrayDataR t         = t


data ScalarArrayDict a where
  ScalarArrayDict :: ( Buffers a ~ Buffer a, ScalarArrayDataR a ~ ScalarArrayDataR b, Storable b, Buffers b ~ Buffer b )
                  => {-# UNPACK #-} !Int    -- vector width
                  -> SingleType b           -- base type
                  -> ScalarArrayDict a 

data SingleArrayDict a where
  SingleArrayDict :: ( Buffers a ~ Buffer a, ScalarArrayDataR a ~ a, Storable a )
                  => SingleArrayDict a


scalarArrayDict :: ScalarType a -> ScalarArrayDict a
scalarArrayDict = scalar
  where
    scalar :: ScalarType a -> ScalarArrayDict a
    scalar (VectorScalarType t) = vector t
    scalar (SingleScalarType t)
      | SingleArrayDict <- singleArrayDict t
      = ScalarArrayDict 1 t

    vector :: VectorType a -> ScalarArrayDict a
    vector (VectorType w s)
      | SingleArrayDict <- singleArrayDict s
      = ScalarArrayDict w s 

singleArrayDict :: SingleType a -> SingleArrayDict a
singleArrayDict = single
  where
    single :: SingleType a -> SingleArrayDict a
    single (NumSingleType t) = num t

    num :: NumType a -> SingleArrayDict a
    num (IntegralNumType t) = integral t
    num (FloatingNumType t) = floating t

    integral :: IntegralType a -> SingleArrayDict a
    integral TypeInt    = SingleArrayDict
    integral TypeInt8   = SingleArrayDict
    integral TypeInt16  = SingleArrayDict
    integral TypeInt32  = SingleArrayDict
    integral TypeInt64  = SingleArrayDict
    integral TypeWord   = SingleArrayDict
    integral TypeWord8  = SingleArrayDict
    integral TypeWord16 = SingleArrayDict
    integral TypeWord32 = SingleArrayDict
    integral TypeWord64 = SingleArrayDict

    floating :: FloatingType a -> SingleArrayDict a
    floating TypeHalf   = SingleArrayDict
    floating TypeFloat  = SingleArrayDict
    floating TypeDouble = SingleArrayDict


-- Array operations
-- ----------------

newBuffers :: forall e. HasCallStack => TypeR e -> Int -> IO (MutableBuffers e)
newBuffers TupRunit         !_    = return ()
newBuffers (TupRpair t1 t2) !size = (,) <$> newBuffers t1 size <*> newBuffers t2 size
newBuffers (TupRsingle t)   !size
  | Refl <- reprIsSingle @ScalarType @e @MutableBuffer t = newBuffer t size

newBuffer :: HasCallStack => ScalarType e -> Int -> IO (MutableBuffer e)
newBuffer (SingleScalarType s) !size
  | SingleDict      <- singleDict s
  , SingleArrayDict <- singleArrayDict s
  = MutableBuffer size <$> allocateArray size
newBuffer (VectorScalarType v) !size
  | VectorType w s  <- v
  , SingleDict      <- singleDict s
  , SingleArrayDict <- singleArrayDict s
  = MutableBuffer (w * size) <$> allocateArray (w * size)

indexBuffers :: TypeR e -> Buffers e -> Int -> e
indexBuffers tR arr ix = unsafePerformIO $ indexBuffers' tR arr ix

indexBuffers' :: TypeR e -> Buffers e -> Int -> IO e
indexBuffers' tR arr = readBuffers tR (veryUnsafeUnfreezeBuffers tR arr)

indexBuffer :: ScalarType e -> Buffer e -> Int -> e
indexBuffer tR (Buffer n arr) ix = unsafePerformIO $ readBuffer tR (MutableBuffer n arr) ix

readBuffers :: forall e. TypeR e -> MutableBuffers e -> Int -> IO e
readBuffers TupRunit         ()       !_  = return ()
readBuffers (TupRpair t1 t2) (a1, a2) !ix = (,) <$> readBuffers t1 a1 ix <*> readBuffers t2 a2 ix
readBuffers (TupRsingle t)   !buffer  !ix
  | Refl <- reprIsSingle @ScalarType @e @MutableBuffer t = readBuffer t buffer ix

readBuffer :: forall e. ScalarType e -> MutableBuffer e -> Int -> IO e
readBuffer (SingleScalarType s) !(MutableBuffer _ array) !ix
  | SingleDict      <- singleDict s
  , SingleArrayDict <- singleArrayDict s
  = unsafeReadArray array ix
readBuffer (VectorScalarType v) !(MutableBuffer _ array) (I# ix#)
  | VectorType (I# w#) s <- v
  , SingleDict           <- singleDict s
  , SingleArrayDict      <- singleArrayDict s
  = let
        !bytes# = w# *# sizeOf# (undefined :: ScalarArrayDataR e)
        !addr#  = unPtr# (unsafeUniqueArrayPtr array) `plusAddr#` (ix# *# bytes#)
     in
     IO $ \s0 ->
       case newAlignedPinnedByteArray# bytes# 16# s0     of { (# s1, mba# #) ->
       case copyAddrToByteArray# addr# mba# 0# bytes# s1 of { s2             ->
       case unsafeFreezeByteArray# mba# s2               of { (# s3, ba# #)  ->
         (# s3, Vec ba# #)
       }}}

writeBuffers :: forall e. TypeR e -> MutableBuffers e -> Int -> e -> IO ()
writeBuffers TupRunit         ()       !_  ()       = return ()
writeBuffers (TupRpair t1 t2) (a1, a2) !ix (v1, v2) = writeBuffers t1 a1 ix v1 >> writeBuffers t2 a2 ix v2
writeBuffers (TupRsingle t)   arr      !ix !val
  | Refl <- reprIsSingle @ScalarType @e @MutableBuffer t = writeBuffer t arr ix val

writeBuffer :: forall e. ScalarType e -> MutableBuffer e -> Int -> e -> IO ()
writeBuffer (SingleScalarType s) (MutableBuffer _ arr) !ix !val
  | SingleDict <- singleDict s
  , SingleArrayDict <- singleArrayDict s
  = unsafeWriteArray arr ix val
writeBuffer (VectorScalarType v) (MutableBuffer _ arr) (I# ix#) (Vec ba#)
  | VectorType (I# w#) s <- v
  , SingleDict           <- singleDict s
  , SingleArrayDict      <- singleArrayDict s
  = let
       !bytes# = w# *# sizeOf# (undefined :: ScalarArrayDataR e)
       !addr#  = unPtr# (unsafeUniqueArrayPtr arr) `plusAddr#` (ix# *# bytes#)
     in
     IO $ \s0 -> case copyByteArrayToAddr# ba# 0# addr# bytes# s0 of
                   s1 -> (# s1, () #)
{-
unsafeArrayDataPtr :: ScalarType e -> ArrayData e -> Ptr (ScalarArrayDataR e)
unsafeArrayDataPtr t arr
  | ScalarArrayDict{} <- scalarArrayDict t
  = unsafeUniqueArrayPtr arr-}

touchBuffers :: forall e. TypeR e -> Buffers e -> IO ()
touchBuffers TupRunit         ()       = return()
touchBuffers (TupRpair t1 t2) (b1, b2) = touchBuffers t1 b1 >> touchBuffers t2 b2
touchBuffers (TupRsingle t)   buffer
  | Refl <- reprIsSingle @ScalarType @e @Buffer t = touchBuffer buffer

touchMutableBuffers :: forall e. TypeR e -> MutableBuffers e -> IO ()
touchMutableBuffers TupRunit         ()       = return()
touchMutableBuffers (TupRpair t1 t2) (b1, b2) = touchMutableBuffers t1 b1 >> touchMutableBuffers t2 b2
touchMutableBuffers (TupRsingle t)   buffer
  | Refl <- reprIsSingle @ScalarType @e @MutableBuffer t = touchMutableBuffer buffer

touchBuffer :: Buffer e -> IO ()
touchBuffer (Buffer _ arr) = touchUniqueArray arr

touchMutableBuffer :: MutableBuffer e -> IO ()
touchMutableBuffer (MutableBuffer _ arr) = touchUniqueArray arr

rnfBuffers :: forall e. TypeR e -> Buffers e -> ()
rnfBuffers TupRunit         ()       = ()
rnfBuffers (TupRpair t1 t2) (a1, a2) = rnfBuffers t1 a1 `seq` rnfBuffers t2 a2
rnfBuffers (TupRsingle t)   arr
  | Refl <- reprIsSingle @ScalarType @e @Buffer t = rnfBuffer arr

rnfBuffer :: Buffer e -> ()
rnfBuffer (Buffer _ arr) = rnf (unsafeUniqueArrayPtr arr)

unPtr# :: Ptr a -> Addr#
unPtr# (Ptr addr#) = addr#

-- | Safe combination of creating and fast freezing of array data.
--
runBuffers
    :: TypeR e
    -> IO (MutableBuffers e, e)
    -> (Buffers e, e)
runBuffers tp st = unsafePerformIO $ do
  (mbuffer, r) <- st
  let buffer = unsafeFreezeBuffers tp mbuffer
  return (buffer, r)

unsafeFreezeBuffers :: forall e. TypeR e -> MutableBuffers e -> Buffers e
unsafeFreezeBuffers TupRunit         ()       = ()
unsafeFreezeBuffers (TupRpair t1 t2) (b1, b2) = (unsafeFreezeBuffers t1 b1, unsafeFreezeBuffers t2 b2)
unsafeFreezeBuffers (TupRsingle t)   buffer
  | Refl <- reprIsSingle @ScalarType @e @MutableBuffer t
  , Refl <- reprIsSingle @ScalarType @e @Buffer t = unsafeFreezeBuffer buffer

unsafeFreezeBuffer :: MutableBuffer e -> Buffer e
unsafeFreezeBuffer (MutableBuffer n arr) = Buffer n arr

veryUnsafeUnfreezeBuffers :: forall e. TypeR e -> Buffers e -> MutableBuffers e
veryUnsafeUnfreezeBuffers TupRunit         ()       = ()
veryUnsafeUnfreezeBuffers (TupRpair t1 t2) (b1, b2) = (veryUnsafeUnfreezeBuffers t1 b1, veryUnsafeUnfreezeBuffers t2 b2)
veryUnsafeUnfreezeBuffers (TupRsingle t)   buffer
  | Refl <- reprIsSingle @ScalarType @e @MutableBuffer t
  , Refl <- reprIsSingle @ScalarType @e @Buffer t = veryUnsafeUnfreezeBuffer buffer

veryUnsafeUnfreezeBuffer :: Buffer e -> MutableBuffer e
veryUnsafeUnfreezeBuffer (Buffer n arr) = MutableBuffer n arr

-- Allocate a new buffer with enough storage to hold the given number of
-- elements.
--
-- The buffer is uninitialised and, in particular, allocated lazily. The latter
-- is important because it means that for backends that have discrete memory
-- spaces (e.g. GPUs), we will not increase host memory pressure simply to track
-- intermediate buffers that contain meaningful data only on the device.
--
allocateArray :: forall e. (HasCallStack, Storable e) => Int -> IO (UniqueArray e)
allocateArray !size = internalCheck "size must be >= 0" (size >= 0) $ do
  arr <- newUniqueArray <=< unsafeInterleaveIO $ do
           let bytes = size * sizeOf (undefined :: e)
           new <- readIORef __mallocForeignPtrBytes
           ptr <- new bytes
           traceM dump_gc ("gc: allocated new host array (size=" % int % ", ptr=" % build % ")") bytes (unsafeForeignPtrToPtr ptr)
           local_memory_alloc (unsafeForeignPtrToPtr ptr) bytes
           return (castForeignPtr ptr)
#ifdef ACCELERATE_DEBUG
  addFinalizer (uniqueArrayData arr) (local_memory_free (unsafeUniqueArrayPtr arr))
#endif
  return arr

-- | Register the given function as the callback to use to allocate new array
-- data on the host containing the specified number of bytes. The returned array
-- must be pinned (with respect to Haskell's GC), so that it can be passed to
-- foreign code.
--
registerForeignPtrAllocator
    :: (Int -> IO (ForeignPtr Word8))
    -> IO ()
registerForeignPtrAllocator new = do
  traceM dump_gc "registering new array allocator"
  atomicWriteIORef __mallocForeignPtrBytes new

bufferToList :: ScalarType e -> Int -> Buffer e -> [e]
bufferToList tp n buffer = go 0
  where
    go !i | i >= n    = []
          | otherwise = indexBuffer tp buffer i : go (i + 1)

{-# NOINLINE __mallocForeignPtrBytes #-}
__mallocForeignPtrBytes :: IORef (Int -> IO (ForeignPtr Word8))
__mallocForeignPtrBytes = unsafePerformIO $! newIORef mallocPlainForeignPtrBytesAligned

-- | Allocate the given number of bytes with 64-byte (cache line)
-- alignment. This is essential for SIMD instructions.
--
-- Additionally, we return a plain ForeignPtr, which unlike a regular ForeignPtr
-- created with 'mallocForeignPtr' carries no finalisers. It is an error to try
-- to add a finaliser to the plain ForeignPtr. For our purposes this is fine,
-- since in Accelerate finalisers are handled using Lifetime
--
mallocPlainForeignPtrBytesAligned :: Int -> IO (ForeignPtr a)
mallocPlainForeignPtrBytesAligned (I# size#) = IO $ \s0 ->
  case newAlignedPinnedByteArray# size# 64# s0 of
    (# s1, mbarr# #) -> (# s1, ForeignPtr (byteArrayContents# (unsafeCoerce# mbarr#)) (PlainPtr mbarr#) #)


liftBuffers :: forall e. Int -> TypeR e -> Buffers e -> CodeQ (Buffers e)
liftBuffers _ TupRunit         ()       = [|| () ||]
liftBuffers n (TupRpair t1 t2) (b1, b2) = [|| ($$(liftBuffers n t1 b1), $$(liftBuffers n t2 b2)) ||]
liftBuffers n (TupRsingle s)   buffer
  | Refl <- reprIsSingle @ScalarType @e @Buffer s = liftBuffer n s buffer

liftBuffer :: forall e. Int -> ScalarType e -> Buffer e -> CodeQ (Buffer e)
liftBuffer n (VectorScalarType (VectorType w t)) (Buffer _ arr)
  | SingleArrayDict <- singleArrayDict t = [|| Buffer (n * w) $$(liftUniqueArray (n * w) arr) ||]
liftBuffer n (SingleScalarType t)                (Buffer _ arr)
  | SingleArrayDict <- singleArrayDict t = [|| Buffer n $$(liftUniqueArray n arr) ||]

-- Determine the underlying type of a Haskell CLong or CULong.
--
runQ [d| type HTYPE_INT = $(
              case finiteBitSize (undefined::Int) of
                32 -> [t| Int32 |]
                64 -> [t| Int64 |]
                _  -> error "I don't know what architecture I am" ) |]

runQ [d| type HTYPE_WORD = $(
              case finiteBitSize (undefined::Word) of
                32 -> [t| Word32 |]
                64 -> [t| Word64 |]
                _  -> error "I don't know what architecture I am" ) |]

runQ [d| type HTYPE_CLONG = $(
              case finiteBitSize (undefined::CLong) of
                32 -> [t| Int32 |]
                64 -> [t| Int64 |]
                _  -> error "I don't know what architecture I am" ) |]

runQ [d| type HTYPE_CULONG = $(
              case finiteBitSize (undefined::CULong) of
                32 -> [t| Word32 |]
                64 -> [t| Word64 |]
                _  -> error "I don't know what architecture I am" ) |]

runQ [d| type HTYPE_CCHAR = $(
              if isSigned (undefined::CChar)
                then [t| Int8  |]
                else [t| Word8 |] ) |]
