{-# LANGUAGE CPP #-}
{-# OPTIONS_HADDOCK hide #-}
-- |
-- Module      : Data.Array.Accelerate.Test.NoFib
-- Copyright   : [2009..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.Test.NoFib (

  nofib,
  nofibIngredient,

  module Data.Array.Accelerate.Test.NoFib.Sharing,
  module Data.Array.Accelerate.Test.NoFib.Prelude,
  module Data.Array.Accelerate.Test.NoFib.Imaginary,
  module Data.Array.Accelerate.Test.NoFib.Spectral,
  module Data.Array.Accelerate.Test.NoFib.Issues,
  module Data.Array.Accelerate.Test.NoFib.Misc,

) where

import Data.Array.Accelerate.Test.NoFib.Base
import Data.Array.Accelerate.Test.NoFib.Config
import Data.Array.Accelerate.Test.NoFib.Sharing
import Data.Array.Accelerate.Test.NoFib.Prelude
import Data.Array.Accelerate.Test.NoFib.Imaginary
import Data.Array.Accelerate.Test.NoFib.Spectral
import Data.Array.Accelerate.Test.NoFib.Issues
import Data.Array.Accelerate.Test.NoFib.Misc

import Test.Tasty.Runners
import Test.Tasty.Ingredients.Rerun
import System.Environment
import Test.Tasty


nofib :: RunN -> TestTree -> IO ()
nofib runN test_runq = do
  me <- getProgName
  defaultMainWithIngredients [rerunningTests (nofibIngredient : defaultIngredients)]
    $ localOption (NumThreads 1)                        -- run each test sequentially with many cores
    $ testGroup me
        [ test_sharing
        , test_prelude runN
        , test_imaginary runN
        , test_spectral runN
        , test_issues runN
        , test_misc runN
        , test_runq
        ]
