{-# LANGUAGE CApiFFI #-}
{-# LANGUAGE CPP     #-}
-- |
-- Module      : Data.Array.Accelerate.FFI.Memory
-- Copyright   : [2008..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--
-- This module is used by @Data.Array.Accelerate.Array.Buffer@.

module Data.Array.Accelerate.FFI.Memory (

  -- * Memory counter
  memoryCounterReset, memoryCounterTotal, memoryCounterInit, memoryCounterMax,

  -- * Buffers
  memoryAlloc, memoryByteSize, memoryRetain, memoryRelease, memoryReleaseRef,

) where

import Data.Word (Word64)
import Foreign.Ptr (FunPtr, Ptr)


#if defined(ACCELERATE_MEMORY_COUNTER)

foreign import capi unsafe "memory.h accelerate_memory_counter_reset"
  memoryCounterReset :: IO ()

foreign import capi unsafe "memory.h accelerate_memory_counter_total"
  memoryCounterTotal :: IO Word64

foreign import capi unsafe "memory.h accelerate_memory_counter_init"
  memoryCounterInit :: IO Word64

foreign import capi unsafe "memory.h accelerate_memory_counter_max"
  memoryCounterMax :: IO Word64

#else

memoryCounterReset :: IO ()
memoryCounterReset = return ()

memoryCounterTotal :: IO Word64
memoryCounterTotal = return 0

memoryCounterInit :: IO Word64
memoryCounterInit = return 0

memoryCounterMax :: IO Word64
memoryCounterMax = return 0

#endif


foreign import capi unsafe "memory.h accelerate_buffer_alloc"
  memoryAlloc :: Word64 -> IO (Ptr ())

foreign import capi unsafe "memory.h accelerate_buffer_byte_size"
  memoryByteSize :: Ptr () -> IO Word64

foreign import capi unsafe "memory.h accelerate_buffer_retain"
  memoryRetain :: Ptr () -> IO ()

foreign import capi unsafe "memory.h accelerate_buffer_release"
  memoryRelease :: Ptr () -> IO ()

foreign import capi unsafe "memory.h &accelerate_buffer_release"
  memoryReleaseRef :: FunPtr (Ptr () -> IO ())
