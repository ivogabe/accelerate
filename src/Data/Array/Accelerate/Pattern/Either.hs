{-# LANGUAGE CPP             #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ViewPatterns    #-}
-- |
-- Module      : Data.Array.Accelerate.Pattern.Either
-- Copyright   : [2018..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.Pattern.Either (

  Either,
#if __GLASGOW_HASKELL__ >= 914
  data Left_, data Right_,
#else
  pattern Left_, pattern Right_,
#endif

) where

import Data.Array.Accelerate.Pattern.TH

mkPattern ''Either

