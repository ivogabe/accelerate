{-# LANGUAGE CApiFFI #-}
{-# LANGUAGE CPP     #-}
-- |
-- Module      : Data.Array.Accelerate.FFI.Tracy
-- Copyright   : [2016..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.FFI.Tracy
  where

import Data.Int
import Data.Word
import Foreign.C.String
import Foreign.C.Types
import Foreign.Ptr

type Zone   = Word64
type SrcLoc = Word64

#if defined(ACCELERATE_TRACY)

#ifdef TRACY_MANUAL_LIFETIME

foreign import capi unsafe "tracy/public/tracy/TracyC.h ___tracy_startup_profiler"
  startup_profiler :: IO ()

foreign import capi unsafe "tracy/public/tracy/TracyC.h ___tracy_shutdown_profiler"
  shutdown_profiler :: IO ()

#else

startup_profiler :: IO ()
startup_profiler = return ()

shutdown_profiler :: IO ()
shutdown_profiler = return ()

#endif

foreign import capi unsafe "tracy/public/tracy/TracyC.h ___tracy_connected"
  tracy_connected :: IO Int32

foreign import capi unsafe "tracy/public/tracy/TracyC.h ___tracy_alloc_srcloc"
  alloc_srcloc
    :: Word32   -- line
    -> CString  -- source
    -> CSize    -- sourceSz
    -> CString  -- function
    -> CSize    -- functionSz
    -> Word32   -- color
    -> IO SrcLoc

foreign import capi unsafe "tracy/public/tracy/TracyC.h ___tracy_alloc_srcloc_name"
  alloc_srcloc_name
    :: Word32   -- line
    -> CString  -- source
    -> CSize    -- sourceSz
    -> CString  -- function
    -> CSize    -- functionSz
    -> CString  -- name
    -> CSize    -- nameSz
    -> Word32   -- color
    -> IO SrcLoc

-- NOTE We cannot use @capi@ when dealing with 'Zone' because 'Zone' is an
-- unsafe hack.  The C functions pass/return @TracyCZoneCtx@
-- (@struct ___tracy_c_zone_context@) by value, and the Haskell API treats the
-- values as 'Word64'.  The layout of a C @struct@ depends on the compiler and
-- system, so this works on some systems but is not cross-platform-safe.  We
-- should not do this.  @TracyCZoneCtx@ is changed in later versions of Tracy,
-- so we will need to remove this from the Haskell API or refactor regardless.

foreign import ccall unsafe "___tracy_emit_zone_begin_alloc"
  emit_zone_begin
    :: SrcLoc  -- srcloc
    -> Int32   -- active
    -> IO Zone

foreign import ccall unsafe "___tracy_emit_zone_end"
  emit_zone_end
    :: Zone  -- ctx
    -> IO ()

foreign import ccall unsafe "___tracy_emit_zone_text"
  emit_zone_text
    :: Zone     -- ctx
    -> CString  -- txt
    -> CSize    -- size
    -> IO ()

foreign import ccall unsafe "___tracy_emit_zone_name"
  emit_zone_name
    :: Zone     -- ctx
    -> CString  -- txt
    -> CSize    -- size
    -> IO ()

foreign import ccall unsafe "___tracy_emit_zone_color"
  emit_zone_color
    :: Zone    -- ctx
    -> Word32  -- color
    -> IO ()

foreign import ccall unsafe "___tracy_emit_zone_value"
  emit_zone_value
    :: Zone    -- ctx
    -> Word64  -- value
    -> IO ()

foreign import capi unsafe "tracy/public/tracy/TracyC.h ___tracy_emit_memory_alloc"
  emit_memory_alloc
    :: Ptr a  -- ptr
    -> CSize  -- size
    -> Int32  -- secure
    -> IO ()

foreign import capi unsafe "tracy/public/tracy/TracyC.h ___tracy_emit_memory_free"
  emit_memory_free
    :: Ptr a  -- ptr
    -> Int32  -- size
    -> IO ()

foreign import capi unsafe "tracy/public/tracy/TracyC.h ___tracy_emit_memory_alloc_named"
  emit_memory_alloc_named
    :: Ptr a    -- ptr
    -> CSize    -- size
    -> Int32    -- secure
    -> CString  -- name
    -> IO ()

foreign import capi unsafe "tracy/public/tracy/TracyC.h ___tracy_emit_memory_free_named"
  emit_memory_free_named
    :: Ptr a    -- ptr
    -> Int32    -- secure
    -> CString  -- name
    -> IO ()

foreign import capi unsafe "tracy/public/tracy/TracyC.h ___tracy_emit_message"
  emit_message
    :: CString  -- txt
    -> CSize    -- size
    -> Int32    -- callstack_depth
    -> IO ()

foreign import capi unsafe "tracy/public/tracy/TracyC.h ___tracy_emit_messageC"
  emit_message_colour
    :: CString  -- txt
    -> CSize    -- size
    -> Word32   -- color
    -> Int32    -- callstack_depth
    -> IO ()

foreign import capi unsafe "tracy/public/tracy/TracyC.h ___tracy_emit_messageL"
  emit_message_literal
    :: CString  -- txt
    -> Int32    -- callstack_depth
    -> IO ()

foreign import capi unsafe "tracy/public/tracy/TracyC.h ___tracy_emit_messageLC"
  emit_message_literal_colour
    :: CString  -- txt
    -> Word32   -- color
    -> Int32    -- callstack_depth
    -> IO ()

foreign import capi unsafe "tracy/public/tracy/TracyC.h ___tracy_emit_frame_mark"
  emit_frame_mark
    :: CString  -- name
    -> IO ()

foreign import capi unsafe "tracy/public/tracy/TracyC.h ___tracy_emit_frame_mark_start"
  emit_frame_mark_start
    :: CString  -- name
    -> IO ()

foreign import capi unsafe "tracy/public/tracy/TracyC.h ___tracy_emit_frame_mark_end"
  emit_frame_mark_end
    :: CString  -- name
    -> IO ()

foreign import capi unsafe "tracy/public/tracy/TracyC.h ___tracy_emit_frame_image"
  emit_frame_image
    :: Ptr Word32  -- image
    -> Word16      -- w (width, must be divisible by 4)
    -> Word16      -- h (height, must be divisible by 4)
    -> Word8       -- offset
    -> Int32       -- flip
    -> IO ()

foreign import capi unsafe "tracy/public/tracy/TracyC.h ___tracy_emit_plot"
  emit_plot
    :: CString  -- name
    -> Double   -- val
    -> IO ()

foreign import capi unsafe "tracy/public/tracy/TracyC.h ___tracy_emit_message_appinfo"
  emit_message_appinfo
    :: CString  -- txt
    -> CSize    -- size
    -> IO ()

#ifdef TRACY_FIBERS

foreign import capi unsafe "tracy/public/tracy/TracyC.h ___tracy_fiber_enter"
  fiber_enter
    :: CString  -- fiber
    -> IO ()

foreign import capi unsafe "tracy/public/tracy/TracyC.h ___tracy_fiber_leave"
  fiber_leave :: IO ()

#else

fiber_enter
  :: CString  -- fiber
  -> IO ()
fiber_enter _ = return ()

fiber_leave :: IO ()
fiber_leave   = return ()

#endif

#else

startup_profiler :: IO ()
startup_profiler = return ()

shutdown_profiler :: IO ()
shutdown_profiler = return ()

tracy_connected :: IO Int32
tracy_connected = return 0

alloc_srcloc
  :: Word32   -- line
  -> CString  -- source
  -> CSize    -- sourceSz
  -> CString  -- function
  -> CSize    -- functionSz
  -> Word32   -- color
  -> IO SrcLoc
alloc_srcloc _ _ _ _ _ _ = return 0

alloc_srcloc_name
  :: Word32   -- line
  -> CString  -- source
  -> CSize    -- sourceSz
  -> CString  -- function
  -> CSize    -- functionSz
  -> CString  -- name
  -> CSize    -- nameSz
  -> Word32   -- color
  -> IO SrcLoc
alloc_srcloc_name _ _ _ _ _ _ _ _ = return 0

emit_zone_begin
  :: SrcLoc  -- srcloc
  -> Int32   -- active
  -> IO Zone
emit_zone_begin _ _ = return 0

emit_zone_end
  :: Zone  -- ctx
  -> IO ()
emit_zone_end _ = return ()

emit_zone_text
  :: Zone     -- ctx
  -> CString  -- txt
  -> CSize    -- size
  -> IO ()
emit_zone_text _ _ _ = return ()

emit_zone_name
  :: Zone     -- ctx
  -> CString  -- txt
  -> CSize    -- size
  -> IO ()
emit_zone_name _ _ _ = return ()

emit_zone_color
  :: Zone    -- ctx
  -> Word32  -- color
  -> IO ()
emit_zone_color _ _ = return ()

emit_zone_value
  :: Zone    -- ctx
  -> Word64  -- value
  -> IO ()
emit_zone_value _ _ = return ()

emit_memory_alloc
  :: Ptr a  -- ptr
  -> CSize  -- size
  -> Int32  -- secure
  -> IO ()
emit_memory_alloc _ _ _ = return ()

emit_memory_free
  :: Ptr a  -- ptr
  -> Int32  -- size
  -> IO ()
emit_memory_free _ _ = return ()

emit_memory_alloc_named
  :: Ptr a    -- ptr
  -> CSize    -- size
  -> Int32    -- secure
  -> CString  -- name
  -> IO ()
emit_memory_alloc_named _ _ _ _ = return ()

emit_memory_free_named
  :: Ptr a    -- ptr
  -> Int32    -- secure
  -> CString  -- name
  -> IO ()
emit_memory_free_named _ _ _ = return ()

emit_message
  :: CString  -- txt
  -> CSize    -- size
  -> Int32    -- callstack_depth
  -> IO ()
emit_message _ _ _ = return ()

emit_message_colour
  :: CString  -- txt
  -> CSize    -- size
  -> Word32   -- color
  -> Int32    -- callstack_depth
  -> IO ()
emit_message_colour _ _ _ _ = return ()

emit_message_literal
  :: CString  -- txt
  -> Int32    -- callstack_depth
  -> IO ()
emit_message_literal _ _ = return ()

emit_message_literal_colour
  :: CString  -- txt
  -> Word32   -- color
  -> Int32    -- callstack_depth
  -> IO ()
emit_message_literal_colour _ _ _ = return ()

emit_frame_mark
  :: CString  -- name
  -> IO ()
emit_frame_mark _ = return ()

emit_frame_mark_start
  :: CString  -- name
  -> IO ()
emit_frame_mark_start _ = return ()

emit_frame_mark_end
  :: CString  -- name
  -> IO ()
emit_frame_mark_end _ = return ()

emit_frame_image
  :: Ptr Word32  -- image
  -> Word16      -- w (must be divisible by 4)
  -> Word16      -- h (must be divisible by 4)
  -> Word8       -- offset
  -> Int32       -- flip
  -> IO ()
emit_frame_image _ _ _ _ _ = return ()

emit_plot
  :: CString  -- name
  -> Double   -- val
  -> IO ()
emit_plot _ _ = return ()

emit_message_appinfo
  :: CString  -- txt
  -> CSize    -- size
  -> IO ()
emit_message_appinfo _ _ = return ()

fiber_enter
  :: CString  -- fiber
  -> IO ()
fiber_enter _ = return ()

fiber_leave :: IO ()
fiber_leave = return ()

#endif
