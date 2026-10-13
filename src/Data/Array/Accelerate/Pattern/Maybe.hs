{-# LANGUAGE CPP             #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ViewPatterns    #-}
-- |
-- Module      : Data.Array.Accelerate.Pattern.Maybe
-- Copyright   : [2018..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.Pattern.Maybe (

  Maybe,
#if __GLASGOW_HASKELL__ >= 914
  data Nothing_, data Just_,
#else
  pattern Nothing_, pattern Just_,
#endif

) where

import Data.Array.Accelerate.Pattern.TH

mkPattern ''Maybe

