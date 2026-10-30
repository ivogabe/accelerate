{-# LANGUAGE CPP             #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ViewPatterns    #-}
-- |
-- Module      : Data.Array.Accelerate.Pattern.Ordering
-- Copyright   : [2018..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.Pattern.Ordering (

  Ordering,
#if __GLASGOW_HASKELL__ >= 914
  data LT_, data EQ_, data GT_,
#else
  pattern LT_, pattern EQ_, pattern GT_,
#endif

) where

import Data.Array.Accelerate.Pattern.TH

mkPattern ''Ordering

