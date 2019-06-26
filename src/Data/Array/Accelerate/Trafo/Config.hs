{-# LANGUAGE RecordWildCards #-}
{-# OPTIONS_GHC -fno-warn-missing-signatures #-}
-- |
-- Module      : Data.Array.Accelerate.Trafo.Config
-- Copyright   : [2008..2019] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.Trafo.Config (

  Config(..),
  Flag(..),
  defaultOptions,

  -- Other options not controlled by the command line flags
  convert_segment_offset,
  float_out_acc,

) where

import Data.Bits
import Data.BitSet
import Data.Array.Accelerate.Debug.Flags                  as F

import Data.Word
import System.IO.Unsafe
import Foreign.Storable


data Config = Config
  { options                   :: {-# UNPACK #-} !(BitSet Word32 Flag)
  , unfolding_use_threshold   :: {-# UNPACK #-} !Int
  , max_simplifier_iterations :: {-# UNPACK #-} !Int
  }
  deriving Show

{-# NOINLINE defaultOptions #-}
defaultOptions :: Config
defaultOptions = unsafePerformIO $!
  Config <$> (BitSet . (0x80000000 .|.)) <$> peek F.__cmd_line_flags
         <*> F.getValue F.unfolding_use_threshold
         <*> F.getValue F.max_simplifier_iterations

-- Extra options not covered by command line flags
--
convert_segment_offset = Flag 30  -- TLM: let's remove the need for this
float_out_acc          = Flag 31
