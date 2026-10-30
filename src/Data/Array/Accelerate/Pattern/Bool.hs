{-# LANGUAGE CPP             #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ViewPatterns    #-}
-- |
-- Module      : Data.Array.Accelerate.Pattern.Bool
-- Copyright   : [2018..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.Pattern.Bool (

  Bool,
#if __GLASGOW_HASKELL__ >= 914
  data True_, data False_,
#else
  pattern True_, pattern False_,
#endif

) where

import Data.Array.Accelerate.Pattern.TH

mkPattern ''Bool

