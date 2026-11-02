{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_HADDOCK hide #-}
-- |
-- Module      : Data.Array.Accelerate.Debug.Internal.Profile
-- Copyright   : [2016..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.Debug.Internal.Profile (

  local_memory_alloc,
  local_memory_free,

  remote_memory_alloc, remote_memory_alloc_nursery,
  remote_memory_free,  remote_memory_free_nursery,
  remote_memory_evict,

  memcpy_to_remote,
  memcpy_from_remote,

  emit_remote_gc,

) where

import Control.Monad
import qualified Data.Array.Accelerate.FFI.Atomic                   as Atomic
import qualified Data.Array.Accelerate.FFI.Monitoring               as Mon
import qualified Data.Array.Accelerate.Tracy                        as Tracy

import Data.Char
import Foreign.C.String
import Foreign.Ptr
import Language.Haskell.TH

import GHC.Ptr


-- Embed some string data into the constant section and grab a pointer
-- directly to it.
--
-- XXX: This only allows us to track a single nursery, but in reality it is
-- one per remote memory space. May or may not be useful to separate this.
--
runQ $ sequence
  [ sigD (mkName "___nursery") (conT ''CString)
  , valD (varP (mkName "___nursery")) (normalB (conE 'Ptr `appE` litE (stringPrimL (map (fromIntegral . ord) "nursery\0")))) []
  ]

{-------------------------------------------------------------------------------
  Allocations in the local memory space
-------------------------------------------------------------------------------}

{-# INLINE local_memory_alloc #-}
local_memory_alloc :: Ptr a -> Int -> IO ()
local_memory_alloc ptr n
  | Tracy.tracyIsEnabled = do
      Tracy.emitMemoryAlloc ptr (fromIntegral n)
      void $ Atomic.add Mon.__total_bytes_allocated_local (fromIntegral n)
  | otherwise            = return ()

{-# INLINE local_memory_free  #-}
local_memory_free :: Ptr a -> IO ()
local_memory_free ptr
  | Tracy.tracyIsEnabled = Tracy.emitMemoryFree ptr
  | otherwise            = return ()

{-------------------------------------------------------------------------------
  Allocations in the remote memory space
-------------------------------------------------------------------------------}

{-# INLINE remote_memory_alloc #-}
remote_memory_alloc :: CString -> Ptr a -> Int -> IO ()
remote_memory_alloc name ptr bytes
  | Tracy.tracyIsEnabled = do
      Tracy.emitMemoryAllocNamed ptr (fromIntegral bytes) name
      void $ Atomic.add Mon.__total_bytes_allocated_remote (fromIntegral bytes)
  | otherwise            = return ()

{-# INLINE remote_memory_free  #-}
remote_memory_free :: CString -> Ptr a -> IO ()
remote_memory_free name ptr
  | Tracy.tracyIsEnabled = Tracy.emitMemoryFreeNamed ptr name
  | otherwise            = return ()

{-# INLINE remote_memory_evict #-}
remote_memory_evict :: CString -> Ptr a -> Int -> IO ()
remote_memory_evict name ptr bytes
  | Tracy.tracyIsEnabled = do
      void $ Atomic.add Mon.__num_evictions 1
      void $ Atomic.add Mon.__total_bytes_evicted_from_remote (fromIntegral bytes)
      remote_memory_free name ptr
      memcpy_from_remote bytes
  | otherwise            = return ()

remote_memory_alloc_nursery :: Ptr a -> Int -> IO ()
remote_memory_alloc_nursery p n
  | Tracy.tracyIsEnabled =
      Tracy.emitMemoryAllocNamed p (fromIntegral n) ___nursery
  | otherwise            = return ()

remote_memory_free_nursery :: Ptr a -> IO ()
remote_memory_free_nursery p
  | Tracy.tracyIsEnabled = Tracy.emitMemoryFreeNamed p ___nursery
  | otherwise            = return ()

{-------------------------------------------------------------------------------
  Data transfer between memory spaces
-------------------------------------------------------------------------------}

{-# INLINE memcpy_to_remote #-}
memcpy_to_remote :: Int -> IO ()
memcpy_to_remote n
  | Tracy.tracyIsEnabled =
      void $ Atomic.add Mon.__total_bytes_copied_to_remote (fromIntegral n)
  | otherwise            = return ()

{-# INLINE memcpy_from_remote #-}
memcpy_from_remote :: Int -> IO ()
memcpy_from_remote n
  | Tracy.tracyIsEnabled =
      void $ Atomic.add Mon.__total_bytes_copied_from_remote (fromIntegral n)
  | otherwise            = return ()

{-------------------------------------------------------------------------------
  Performed a major GC of the remote memory space
-------------------------------------------------------------------------------}

{-# INLINE emit_remote_gc #-}
emit_remote_gc :: IO ()
emit_remote_gc
  | Tracy.tracyIsEnabled = void $ Atomic.add Mon.__num_remote_gcs 1
  | otherwise            = return ()
