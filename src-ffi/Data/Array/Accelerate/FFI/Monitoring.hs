-- |
-- Module      : Data.Array.Accelerate.FFI.Monitoring
-- Copyright   : [2016..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--
-- This module is used by @Data.Array.Accelerate.Debug.Internal.Profile@.

module Data.Array.Accelerate.FFI.Monitoring (

  __total_bytes_allocated_local, __total_bytes_allocated_remote,
  __total_bytes_copied_to_remote, __total_bytes_copied_from_remote,
  __total_bytes_evicted_from_remote, __num_remote_gcs, __num_evictions,

) where

import Data.Array.Accelerate.FFI.Atomic


-- bytes allocated in the local (CPU) memory space
foreign import ccall "&__total_bytes_allocated_local"
  __total_bytes_allocated_local :: Atomic

-- bytes allocated in the remote memory space (if it is separate, e.g. GPU)
foreign import ccall "&__total_bytes_allocated_remote"
  __total_bytes_allocated_remote :: Atomic

-- bytes copied to the remote memory space
foreign import ccall "&__total_bytes_copied_to_remote"
  __total_bytes_copied_to_remote :: Atomic

-- bytes copied from the remote memory space
foreign import ccall "&__total_bytes_copied_from_remote"
  __total_bytes_copied_from_remote :: Atomic

-- total bytes copied from the remote due to evictions
foreign import ccall "&__total_bytes_evicted_from_remote"
  __total_bytes_evicted_from_remote :: Atomic

-- number of times the remote memory space was forcibly garbage collected
foreign import ccall "&__num_remote_gcs"
  __num_remote_gcs :: Atomic

-- number of LRU eviction events
foreign import ccall "&__num_evictions"
  __num_evictions :: Atomic
