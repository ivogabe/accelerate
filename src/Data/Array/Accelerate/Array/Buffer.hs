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
-- This module fixes the concrete representation of Accelerate arrays.
-- We allocate memory via foreign function calls, outside of the Haskell heap.
-- This gives us flexibility to manage memory ourselves, and prevents the
-- Haskell GC to move arrays around (which would break in our foreign function
-- calls).
-- These arrays are reclaimed via reference counting. A Haskell-side reference
-- to an array has a finalizer which will decrement the reference count.
-- C or our generated LLVM code working with references to arrays will
-- manually increment and decrement the reference count.
--

module Data.Array.Accelerate.Array.Buffer (

  -- * Array operations and representations
  Buffers, Buffer(..), MutableBuffers, MutableBuffer(..), ScalarArrayDataR,
  runBuffers,
  newBuffers, newBuffer,
  indexBuffers, indexBuffers', indexBuffer, readBuffers, readBuffer, writeBuffers, writeBuffer,
  touchBuffers, touchBuffer, touchMutableBuffers, touchMutableBuffer,
  rnfBuffers, rnfBuffer, unsafeFreezeBuffer, unsafeFreezeBuffers,
  veryUnsafeUnfreezeBuffers, bufferToList, bufferRetainAndGetRef, bufferRelease, bufferFromPtr,

  -- * Type macros
  HTYPE_INT, HTYPE_WORD, HTYPE_CLONG, HTYPE_CULONG, HTYPE_CCHAR,

  -- * Utilities for type classes
  SingleArrayDict(..), singleArrayDict,
  ScalarArrayDict(..), scalarArrayDict,
  scalarArrayDataR,

  -- * TemplateHaskell
  liftBuffers, liftBuffer,
) where

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
import Foreign.Ptr
import Foreign.ForeignPtr
import Foreign.Storable
import Foreign.Marshal.Array                                        ( copyArray, peekArray )
import Formatting                                                   hiding ( bytes )
import Language.Haskell.TH.Extra                                    hiding ( Type )
import Language.Haskell.TH.Syntax
import System.IO.Unsafe
import Prelude                                                      hiding ( mapM )

import GHC.Exts                                                     hiding ( build )
import GHC.ForeignPtr
import GHC.Types

import System.Mem

-- | A buffer is a piece of memory representing one of the fields
-- of the SoA of an array. It does not have a multi-dimensional size,
-- e.g. the shape of the array should be stored elsewhere.
-- Replaces the former 'ScalarArrayData' type synonym.
--
newtype Buffer e = Buffer (ForeignPtr (ScalarArrayDataR e))

-- | A structure of buffers represents an array, corresponding to the SoA conversion.
-- Replaces the old 'ArrayData' and 'MutableArrayData' type aliasses and the
-- 'GArrayDataR' type family.
--
type Buffers e = Distribute Buffer e

newtype MutableBuffer e = MutableBuffer (ForeignPtr (ScalarArrayDataR e))
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

-- SEE: [HLS and GHC IDE]
--
#ifndef __GHCIDE__

foreign import ccall unsafe "accelerate_buffer_alloc" memoryAlloc :: Word64 -> IO (Ptr ())
foreign import ccall unsafe "accelerate_buffer_byte_size" memoryByteSize :: Ptr () -> IO Word64
foreign import ccall unsafe "accelerate_buffer_retain" memoryRetain :: Ptr () -> IO ()
foreign import ccall unsafe "accelerate_buffer_release" memoryRelease :: Ptr () -> IO ()
foreign import ccall unsafe "&accelerate_buffer_release" memoryReleaseRef :: FunPtr (Ptr () -> IO ())

#else

memoryAlloc :: Word64 -> IO (Ptr ())
memoryAlloc = undefined

memoryRetain :: Ptr () -> IO ()
memoryRetain = undefined

memoryRelease :: Ptr () -> IO ()
memoryRelease = undefined

#endif

-- SEE: [linking to .c files]
--
runQ $ do
  addForeignFilePath LangC "cbits/memory.c"
  return []

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

scalarArrayDataR :: ScalarType t -> SingleType (ScalarArrayDataR t)
scalarArrayDataR (VectorScalarType (VectorType _ t)) = t
scalarArrayDataR (SingleScalarType t)
  | SingleArrayDict <- singleArrayDict t = t

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
  = MutableBuffer <$> allocateArray size
newBuffer (VectorScalarType v) !size
  | VectorType w s  <- v
  , SingleDict      <- singleDict s
  , SingleArrayDict <- singleArrayDict s
  = MutableBuffer <$> allocateArray (w * size)

indexBuffers :: TypeR e -> Buffers e -> Int -> e
indexBuffers tR arr ix = unsafePerformIO $ indexBuffers' tR arr ix

indexBuffers' :: TypeR e -> Buffers e -> Int -> IO e
indexBuffers' tR arr = readBuffers tR (veryUnsafeUnfreezeBuffers tR arr)

indexBuffer :: ScalarType e -> Buffer e -> Int -> e
indexBuffer tR (Buffer arr) ix = unsafePerformIO $ readBuffer tR (MutableBuffer arr) ix

readBuffers :: forall e. TypeR e -> MutableBuffers e -> Int -> IO e
readBuffers TupRunit         ()       !_  = return ()
readBuffers (TupRpair t1 t2) (a1, a2) !ix = (,) <$> readBuffers t1 a1 ix <*> readBuffers t2 a2 ix
readBuffers (TupRsingle t)   !buffer  !ix
  | Refl <- reprIsSingle @ScalarType @e @MutableBuffer t = readBuffer t buffer ix

readBuffer :: forall e. ScalarType e -> MutableBuffer e -> Int -> IO e
readBuffer (SingleScalarType s) !(MutableBuffer buffer) !ix
  | SingleDict      <- singleDict s
  , SingleArrayDict <- singleArrayDict s
  = withForeignPtr buffer $ \ptr -> peekElemOff ptr ix
readBuffer (VectorScalarType v) !(MutableBuffer buffer) (I# ix#)
  | VectorType (I# w#) s <- v
  , SingleDict           <- singleDict s
  , SingleArrayDict      <- singleArrayDict s
  = withForeignPtr buffer $ \ptr ->
    let
        !bytes# = w# *# sizeOf# (undefined :: ScalarArrayDataR e)
        !addr#  = unPtr# ptr `plusAddr#` (ix# *# bytes#)
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
writeBuffer (SingleScalarType s) (MutableBuffer buffer) !ix !val
  | SingleDict <- singleDict s
  , SingleArrayDict <- singleArrayDict s
  = withForeignPtr buffer $ \ptr -> pokeElemOff ptr ix val
writeBuffer (VectorScalarType v) (MutableBuffer buffer) (I# ix#) (Vec ba#)
  | VectorType (I# w#) s <- v
  , SingleDict           <- singleDict s
  , SingleArrayDict      <- singleArrayDict s
  = withForeignPtr buffer $ \ptr ->
    let
       !bytes# = w# *# sizeOf# (undefined :: ScalarArrayDataR e)
       !addr#  = unPtr# ptr `plusAddr#` (ix# *# bytes#)
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
touchBuffer (Buffer buffer) = touchForeignPtr buffer

touchMutableBuffer :: MutableBuffer e -> IO ()
touchMutableBuffer (MutableBuffer buffer) = touchForeignPtr buffer

rnfBuffers :: forall e. TypeR e -> Buffers e -> ()
rnfBuffers TupRunit         ()       = ()
rnfBuffers (TupRpair t1 t2) (a1, a2) = rnfBuffers t1 a1 `seq` rnfBuffers t2 a2
rnfBuffers (TupRsingle t)   arr
  | Refl <- reprIsSingle @ScalarType @e @Buffer t = rnfBuffer arr

rnfBuffer :: Buffer e -> ()
rnfBuffer !_ = ()

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
unsafeFreezeBuffer (MutableBuffer arr) = Buffer arr

veryUnsafeUnfreezeBuffers :: forall e. TypeR e -> Buffers e -> MutableBuffers e
veryUnsafeUnfreezeBuffers TupRunit         ()       = ()
veryUnsafeUnfreezeBuffers (TupRpair t1 t2) (b1, b2) = (veryUnsafeUnfreezeBuffers t1 b1, veryUnsafeUnfreezeBuffers t2 b2)
veryUnsafeUnfreezeBuffers (TupRsingle t)   buffer
  | Refl <- reprIsSingle @ScalarType @e @MutableBuffer t
  , Refl <- reprIsSingle @ScalarType @e @Buffer t = veryUnsafeUnfreezeBuffer buffer

veryUnsafeUnfreezeBuffer :: Buffer e -> MutableBuffer e
veryUnsafeUnfreezeBuffer (Buffer arr) = MutableBuffer arr

-- Allocate a new buffer with enough storage to hold the given number of
-- elements.
--
-- The buffer is uninitialised.
--
allocateArray :: forall e. (HasCallStack, Storable e) => Int -> IO (ForeignPtr e)
allocateArray !size = internalCheck "size must be >= 0" (size >= 0) $ do
  let bytes = size * sizeOf (undefined :: e)

  hintGCAlloc bytes

  ptr <- memoryAlloc $ fromIntegral bytes
  foreignPtr <- newForeignPtr memoryReleaseRef ptr
  traceM dump_gc ("gc: allocated new host array (size=" % int % ", ptr=" % build % ")") bytes ptr
  return $ castForeignPtr foreignPtr

-- Once per 1GB of allocations, perform garbage collection.
-- Buffers are allocated outside of the Haskell world, so we have to force
-- GC to deallocate them indirectly.
hintGCAlloc :: Int -> IO ()
hintGCAlloc bytes = do
  let maxSize = 1024 * 1024 * 1024
  gc <- atomicModifyIORef' bytesAllocatedSinceGC $ \sz ->
    let newSize = sz + bytes
    in if newSize < maxSize then (newSize, False) else (newSize `mod` maxSize, True)
  if gc then performGC else return ()

{-# NOINLINE bytesAllocatedSinceGC #-}
bytesAllocatedSinceGC :: IORef Int
bytesAllocatedSinceGC = unsafePerformIO $ newIORef 0

bufferToList :: ScalarType e -> Int -> Buffer e -> [e]
bufferToList tp n buffer = go 0
  where
    go !i | i >= n    = []
          | otherwise = indexBuffer tp buffer i : go (i + 1)

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

bufferRetainAndGetRef :: Buffer e -> IO (Ptr (ScalarArrayDataR e))
bufferRetainAndGetRef (Buffer foreignPtr) = withForeignPtr foreignPtr $ \ptr -> do
  memoryRetain $ castPtr ptr
  return $ castPtr ptr

-- Ptr should originate from bufferRetainAndGetRef
bufferRelease :: Ptr e -> IO ()
bufferRelease = memoryRelease . castPtr

bufferFromPtr :: Ptr e -> IO (Buffer e)
bufferFromPtr ptr = do
  byteSize <- fromIntegral <$> memoryByteSize (castPtr ptr)
  hintGCAlloc byteSize
  fp <- newForeignPtr memoryReleaseRef $ castPtr ptr
  return $ Buffer $ castForeignPtr fp

liftBuffers :: forall e. TypeR e -> Buffers e -> CodeQ (Buffers e)
liftBuffers TupRunit         ()       = [|| () ||]
liftBuffers (TupRpair t1 t2) (b1, b2) = [|| ($$(liftBuffers t1 b1), $$(liftBuffers t2 b2)) ||]
liftBuffers (TupRsingle s)   buffer
  | Refl <- reprIsSingle @ScalarType @e @Buffer s = liftBuffer s buffer

liftBuffer :: forall e. ScalarType e -> Buffer e -> CodeQ (Buffer e)
liftBuffer (VectorScalarType (VectorType w t)) (Buffer arr)
  | SingleArrayDict <- singleArrayDict t = [|| Buffer $$(liftBufferData arr) ||]
liftBuffer (SingleScalarType t)                (Buffer arr)
  | SingleArrayDict <- singleArrayDict t = [|| Buffer $$(liftBufferData arr) ||]

liftBufferData :: forall a. Storable a => ForeignPtr a -> CodeQ (ForeignPtr a)
liftBufferData buffer = unsafePerformIO $ withForeignPtr buffer $ \ptr -> do
  byteSize <- fromIntegral <$> memoryByteSize (castPtr ptr)
  let size = byteSize `div` sizeOf (undefined::a)
  bytes <- peekArray byteSize (castPtr ptr :: Ptr Word8)

  return [||
    unsafePerformIO $ do
      let ptrData = Ptr $$(unsafeCodeCoerce $ litE (StringPrimL bytes)) :: Ptr Word8
      result <- allocateArray size
      withForeignPtr result $ \p ->
        copyArray (castPtr p) ptrData byteSize
      return result
   ||]

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
