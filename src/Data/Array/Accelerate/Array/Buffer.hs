{-# LANGUAGE BangPatterns        #-}
{-# LANGUAGE CPP                 #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}
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
  Buffers, Buffer(..), MutableBuffers, MutableBuffer(..),
  runBuffers,
  newBuffers, newBuffer,
  indexBuffers, indexBuffers', indexBuffer, readBuffers, readBuffer, writeBuffers, writeBuffer,
  touchBuffers, touchBuffer, touchMutableBuffers, touchMutableBuffer,
  rnfBuffers, rnfBuffer, unsafeFreezeBuffer, unsafeFreezeBuffers,
  veryUnsafeUnfreezeBuffers, bufferToList, bufferRetainAndGetRef, bufferRelease, bufferFromPtr,
  memoryByteSize,

  -- * Type macros
  HTYPE_INT, HTYPE_WORD, HTYPE_CLONG, HTYPE_CULONG, HTYPE_CCHAR,

  -- * Utilities for type classes
  ScalarArrayDict(..),

  -- * TemplateHaskell
  liftBuffers, liftBuffer,

  -- * Memory tracking
  memoryCounterReset, memoryCounterReport,
) where


import Data.Array.Accelerate.Error
import Data.Array.Accelerate.Representation.Type
import Data.Array.Accelerate.Type

import Data.Array.Accelerate.Debug.Internal.Flags
import Data.Array.Accelerate.Debug.Internal.Trace

import Control.Applicative
import Data.Bits
import Data.IORef
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

import System.Mem

-- | A buffer is a piece of memory representing one of the fields
-- of the SoA of an array. It does not have a multi-dimensional size,
-- e.g. the shape of the array should be stored elsewhere.
-- Replaces the former 'ScalarArrayData' type synonym.
--
newtype Buffer e = Buffer (ForeignPtr e)

-- | A structure of buffers represents an array, corresponding to the SoA conversion.
-- Replaces the old 'ArrayData' and 'MutableArrayData' type aliasses and the
-- 'GArrayDataR' type family.
--
type Buffers e = Distribute Buffer e

newtype MutableBuffer e = MutableBuffer (ForeignPtr e)
type MutableBuffers e = Distribute MutableBuffer e

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

memoryByteSize :: Ptr () -> IO Word64
memoryByteSize = undefined

memoryRetain :: Ptr () -> IO ()
memoryRetain = undefined

memoryRelease :: Ptr () -> IO ()
memoryRelease = undefined

memoryReleaseRef :: FunPtr (Ptr () -> IO ())
memoryReleaseRef = undefined

#endif


#if defined(ACCELERATE_MEMORY_COUNTER) && !defined(__GHCIDE__)

foreign import ccall unsafe "accelerate_memory_counter_reset" memoryCounterReset :: IO ()
foreign import ccall unsafe "accelerate_memory_counter_total" memoryCounterTotal :: IO Word64
foreign import ccall unsafe "accelerate_memory_counter_init" memoryCounterInit :: IO Word64
foreign import ccall unsafe "accelerate_memory_counter_max" memoryCounterMax :: IO Word64

#else

memoryCounterReset :: IO ()
memoryCounterReset = return ()

#endif

#if defined(__GHCIDE__)

memoryCounterTotal :: IO Word64
memoryCounterTotal = return 0

memoryCounterInit :: IO Word64
memoryCounterInit = return 0

memoryCounterMax :: IO Word64
memoryCounterMax = return 0

#endif

#if defined(ACCELERATE_MEMORY_COUNTER) || defined(__GHCIDE__)

memoryCounterReport :: IO ()
memoryCounterReport = do
  totalAlloc <- memoryCounterTotal
  initAlloc  <- memoryCounterInit
  maxAlloc   <- memoryCounterMax
  putStrLn $ "Total memory allocated:   " ++ show totalAlloc ++ " bytes"
  putStrLn $ "Initial memory allocated: " ++ show initAlloc ++ " bytes"
  putStrLn $ "Maximum memory allocated: " ++ show maxAlloc ++ " bytes"

#else

memoryCounterReport :: IO ()
memoryCounterReport = putStrLn "MEMORY COUNTER DISABLED"

#endif

--
-- SEE: [linking to .c files]
--
runQ $ do
  addForeignFilePath LangC "cbits/memory.c"
  addForeignFilePath LangCxx "cbits/alloc.cpp"
  return []

data ScalarArrayDict a where
  ScalarArrayDict :: ( Buffers a ~ Buffer a, Storable a )
                  => ScalarArrayDict a


scalarArrayDict :: ScalarType a -> ScalarArrayDict a
scalarArrayDict = scalar
  where
    scalar :: ScalarType a -> ScalarArrayDict a
    scalar (VectorScalarType t) = vector t
    scalar (SingleScalarType t)
      | ScalarArrayDict <- singleArrayDict t
      = ScalarArrayDict

    vector :: VectorType a -> ScalarArrayDict a
    vector (VectorType _ s)
      | ScalarArrayDict <- singleArrayDict s
      , SingleDict <- singleDict s
      = ScalarArrayDict

singleArrayDict :: SingleType a -> ScalarArrayDict a
singleArrayDict = single
  where
    single :: SingleType a -> ScalarArrayDict a
    single (NumSingleType t) = num t

    num :: NumType a -> ScalarArrayDict a
    num (IntegralNumType t) = integral t
    num (FloatingNumType t) = floating t

    integral :: IntegralType a -> ScalarArrayDict a
    integral TypeInt    = ScalarArrayDict
    integral TypeInt8   = ScalarArrayDict
    integral TypeInt16  = ScalarArrayDict
    integral TypeInt32  = ScalarArrayDict
    integral TypeInt64  = ScalarArrayDict
    integral TypeWord   = ScalarArrayDict
    integral TypeWord8  = ScalarArrayDict
    integral TypeWord16 = ScalarArrayDict
    integral TypeWord32 = ScalarArrayDict
    integral TypeWord64 = ScalarArrayDict

    floating :: FloatingType a -> ScalarArrayDict a
    floating TypeHalf   = ScalarArrayDict
    floating TypeFloat  = ScalarArrayDict
    floating TypeDouble = ScalarArrayDict

-- Array operations
-- ----------------

newBuffers :: forall e. HasCallStack => TypeR e -> Int -> IO (MutableBuffers e)
newBuffers TupRunit         !_    = return ()
newBuffers (TupRpair t1 t2) !size = (,) <$> newBuffers t1 size <*> newBuffers t2 size
newBuffers (TupRsingle t)   !size
  | Refl <- reprIsSingle @ScalarType @e @MutableBuffer t = newBuffer t size

newBuffer :: HasCallStack => ScalarType e -> Int -> IO (MutableBuffer e)
newBuffer tp !size
  | ScalarArrayDict <- scalarArrayDict tp
  = MutableBuffer <$> allocateArray size

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
readBuffer tp !(MutableBuffer buffer) !ix
  | ScalarArrayDict <- scalarArrayDict tp
  = withForeignPtr buffer $ \ptr -> peekElemOff ptr ix

writeBuffers :: forall e. TypeR e -> MutableBuffers e -> Int -> e -> IO ()
writeBuffers TupRunit         ()       !_  ()       = return ()
writeBuffers (TupRpair t1 t2) (a1, a2) !ix (v1, v2) = writeBuffers t1 a1 ix v1 >> writeBuffers t2 a2 ix v2
writeBuffers (TupRsingle t)   arr      !ix !val
  | Refl <- reprIsSingle @ScalarType @e @MutableBuffer t = writeBuffer t arr ix val

writeBuffer :: forall e. ScalarType e -> MutableBuffer e -> Int -> e -> IO ()
writeBuffer tp (MutableBuffer buffer) !ix !val
  | ScalarArrayDict <- scalarArrayDict tp
  = withForeignPtr buffer $ \ptr -> pokeElemOff ptr ix val

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


bufferRetainAndGetRef :: Buffer e -> IO (Ptr e)
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
liftBuffer tp (Buffer arr)
  | ScalarArrayDict <- scalarArrayDict tp = [|| Buffer $$(liftBufferData arr) ||]

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
