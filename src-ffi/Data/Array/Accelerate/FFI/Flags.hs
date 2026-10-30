{-# LANGUAGE CPP #-}
-- |
-- Module      : Data.Array.Accelerate.FFI.Flags
-- Copyright   : [2008..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--
-- Option parsing for debug flags
--

module Data.Array.Accelerate.FFI.Flags (

  Flag(..),
  seq_sharing, acc_sharing, exp_sharing, array_fusion, inplace, force_recomp,
  fast_math, debug, verbose, dump_phases, dump_sharing, dump_fusion,
  dump_simpl_stats, dump_simpl_iterations, dump_vectorisation, dump_dot,
  dump_simpl_dot, dump_gc, dump_gc_stats, dump_cc, dump_ld, dump_asm, dump_exec,
  dump_sched,

  getFlag,
  setFlag, setFlags,
  clearFlag, clearFlags,

  when,
  unless,

  peekFlags,

) where

#ifdef ACCELERATE_DEBUG
import qualified Control.Monad                                      as M
import qualified Control.Monad.IO.Class                             as MIO
#endif

import Control.Monad.IO.Class                                       ( MonadIO )
import Data.Bits
import Data.Word                                                    ( Word32 )
import Foreign.Ptr                                                  ( Ptr )
import Foreign.Storable


newtype Flag = Flag Int

-- We aren't using a "real" enum so that we can make use of the unused top
-- bits for other configuration options, not controlled by the command line
-- flags.
--
-- However, as there are currently no such special configuration options, the
-- bit hack complexity here is unnecessary. It's kept as an easter egg for
-- future maintainers.
--
instance Enum Flag where
  toEnum            = Flag
  fromEnum (Flag x) = x

-- SEE: [layout of command line options bitfield]
instance Show Flag where
  show (Flag x) =
    case x of
      0  -> "seq-sharing"
      1  -> "acc-sharing"
      2  -> "exp-sharing"
      3  -> "fusion"
      4  -> "inplace"
      5  -> "fast-math"
      6  -> "force-recomp"
      7  -> "debug"
      8  -> "verbose"
      9  -> "dump-phases"
      10 -> "dump-sharing"
      11 -> "dump-fusion"
      12 -> "dump-simpl-stats"
      13 -> "dump-simpl-iterations"
      14 -> "dump-vectorisation"
      15 -> "dump-dot"
      16 -> "dump-simpl-dot"
      17 -> "dump-gc"
      18 -> "dump-gc-stats"
      19 -> "dump-cc"
      20 -> "dump-ld"
      21 -> "dump-asm"
      22 -> "dump-exec"
      23 -> "dump-sched"
      _  -> show x

-- These @-f<blah>@ flags can be reversed with @-fno-<blah>@
--
-- SEE: [layout of command line options bitfield]
seq_sharing, acc_sharing, exp_sharing, array_fusion, inplace, fast_math,
  force_recomp :: Flag
seq_sharing           = Flag  0 -- recover sharing of sequence expressions
acc_sharing           = Flag  1 -- recover sharing of array computations
exp_sharing           = Flag  2 -- recover sharing of scalar expressions
array_fusion          = Flag  3 -- fuse array expressions
inplace               = Flag  4 -- allow (safe) in-place array updates
fast_math             = Flag  5 -- use faster, less precise math library operations
force_recomp          = Flag  6 -- force recompilation of array programs

-- These debugging flags are disable by default and are enabled with @-d<blah>@
debug, verbose, dump_phases, dump_sharing, dump_fusion, dump_simpl_stats,
  dump_simpl_iterations, dump_vectorisation, dump_dot, dump_simpl_dot, dump_gc,
  dump_gc_stats, dump_cc, dump_ld, dump_asm, dump_exec, dump_sched :: Flag
debug                 = Flag  7 -- compile code with debugging symbols (-g)
verbose               = Flag  8 -- be very chatty
dump_phases           = Flag  9 -- print information about each phase of the compiler
dump_sharing          = Flag 10 -- sharing recovery phase
dump_fusion           = Flag 11 -- array fusion phase
dump_simpl_stats      = Flag 12 -- statistics form fusion/simplification
dump_simpl_iterations = Flag 13 -- output from each simplifier iteration
dump_vectorisation    = Flag 14 -- output from the vectoriser
dump_dot              = Flag 15 -- generate dot output of the program
dump_simpl_dot        = Flag 16 -- generate simplified dot output
dump_gc               = Flag 17 -- trace garbage collector
dump_gc_stats         = Flag 18 -- print final GC statistics
dump_cc               = Flag 19 -- trace code generation & compilation
dump_ld               = Flag 20 -- trace runtime linker
dump_asm              = Flag 21 -- trace assembler
dump_exec             = Flag 22 -- trace execution
dump_sched            = Flag 23 -- trace scheduler


getFlag :: Flag -> IO Bool
getFlag (Flag i) = do
  flags  <- peekFlags
  return $! testBit flags i

setFlag :: Flag -> IO ()
setFlag (Flag i) = do
  flags <- peekFlags
  pokeFlags  (setBit flags i)

setFlags :: [Flag] -> IO ()
setFlags = mapM_ setFlag

clearFlag :: Flag -> IO ()
clearFlag (Flag i) = do
  flags <- peekFlags
  pokeFlags (clearBit flags i)

clearFlags :: [Flag] -> IO ()
clearFlags = mapM_ clearFlag


-- | Conditional execution of a monadic debugging expression.
--
-- This does nothing unless the program is compiled in debug mode.
--
{-# INLINEABLE when #-}
when :: MonadIO m => Flag -> m () -> m ()
#if ACCELERATE_DEBUG
when f action = do
  yes <- MIO.liftIO $ getFlag f
  M.when yes action
#else
when _ _ = return ()
#endif

-- | The opposite of 'when'.
--
-- This does nothing unless the program is compiled in debug mode.
--
{-# INLINEABLE unless #-}
unless :: MonadIO m => Flag -> m () -> m ()
#ifdef ACCELERATE_DEBUG
unless f action = do
  yes <- MIO.liftIO $ getFlag f
  M.unless yes action
#else
unless _ _ = return ()
#endif


foreign import ccall "&__cmd_line_flags"
  __cmd_line_flags :: Ptr Word32

peekFlags :: IO Word32
peekFlags = peek __cmd_line_flags

pokeFlags :: Word32 -> IO ()
pokeFlags = poke __cmd_line_flags
