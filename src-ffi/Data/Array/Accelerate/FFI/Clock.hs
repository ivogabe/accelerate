{-# LANGUAGE CApiFFI #-}
-- |
-- Module      : Data.Array.Accelerate.FFI.Clock
-- Copyright   : [2016..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.FFI.Clock (

  getMonotonicTime, getProgramTime,

) where

foreign import capi unsafe "clock.h clock_gettime_monotonic_seconds"
  getMonotonicTime :: IO Double

foreign import capi unsafe "clock.h clock_gettime_elapsed_seconds"
  getProgramTime :: IO Double
