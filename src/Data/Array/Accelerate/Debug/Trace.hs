{-# LANGUAGE TemplateHaskellQuotes #-}
-- |
-- Module      : Data.Array.Accelerate.Debug.Trace
-- Copyright   : [2008..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--
-- Functions for tracing and monitoring execution. These are useful for
-- investigating bugs.
--
-- @since 1.4.0.0
--

module Data.Array.Accelerate.Debug.Trace (

  -- * Tracing
  -- $tracing
  --
  atrace, atraceArray, atraceId, atraceExp,

) where

import Data.Array.Accelerate.Language
import Data.Array.Accelerate.Smart
import Data.Array.Accelerate.Sugar.Array                            as S
import Data.Array.Accelerate.Sugar.Elt
import qualified Data.Array.Accelerate.Representation.Array         as R
import qualified Data.Array.Accelerate.Representation.Shape         as R

import Data.Text                                                    ( Text )
import qualified Language.Haskell.TH                                as TH
import qualified Language.Haskell.TH.Syntax                         as TH
import Type.Reflection


-- $tracing
--
-- The 'atrace', 'atraceArray', 'atraceId', and 'atraceExp' functions print
-- messages to an output stream. They are intended for \"printf
-- debugging\", that is: tracing the flow of execution and printing
-- interesting values.
--
-- Note that arrays are printed in their internal representation (using
-- 'Data.Array.Accelerate.Sugar.Array.ArraysR'), which causes that tuples
-- or custom data types are shown differently.
--
-- These functions have the same caveats as those defined in "Debug.Trace".
--

-- | Outputs the trace message to the console before the 'Acc' computation
-- proceeds with the result of the second argument.
--
atrace :: Arrays a => Text -> Acc a -> Acc a
atrace message (Acc result)
  = Acc
  $ SmartAcc
  $ Atrace (Message (\_ -> "")
           (Just [|| \_ -> "" ||]) message) (SmartAcc Anil :: SmartAcc ()) result

-- | Outputs the trace message and the array(s) from the second argument to
-- the console, before the 'Acc' computation proceeds with the result of
-- the third argument.
--
atraceArray :: forall a b. (Arrays a, Arrays b, Show a, Typeable a) => Text -> Acc a -> Acc b -> Acc b
atraceArray message (Acc inspect) (Acc result)
  = Acc
  $ SmartAcc
  $ Atrace (Message showArrays (Just showArraysCode) message) inspect result
  where
    showArrays :: ArraysR a -> String
    showArrays = show . toArr @a

    showArraysCode :: TH.CodeQ (ArraysR a -> String)
    showArraysCode = TH.unsafeCodeCoerce $
      let ty     = pure $ liftTypeRep (typeRep @a)
          toArrA = TH.appTypeE [| toArr |] ty
      in  [| show . $toArrA |]

-- | Outputs the trace message and the array(s) to the console, before the
-- 'Acc' computation proceeds with the result of that array.
--
atraceId :: (Arrays a, Show a, Typeable a) => Text -> Acc a -> Acc a
atraceId message value = atraceArray message value value

-- | Outputs the trace message and a scalar value to the console, before
-- the 'Acc' computation proceeds with the result of the third argument.
--
atraceExp :: forall e a. (Elt e, Show e, Typeable e, Arrays a) => Text -> Exp e -> Acc a -> Acc a
atraceExp message value (Acc result) =
  let Acc inspect = unit value
   in Acc
    $ SmartAcc
    $ Atrace (Message showScalar (Just showScalarCode) message) inspect result
  where
    showScalar :: R.Array R.DIM0 (EltR e) -> String
    showScalar a = show (toElt @e (R.indexArray (R.ArrayR R.dim0 (eltR @e)) a ()))

    showScalarCode :: TH.CodeQ (ArraysR (Scalar e) -> String)
    showScalarCode = TH.unsafeCodeCoerce $
      let ty     = pure $ liftTypeRep (typeRep @e)
          toEltE = TH.appTypeE [| toElt |] ty
          eltRE  = TH.appTypeE [| eltR  |] ty
      in  [| \a -> show ($toEltE (R.indexArray (R.ArrayR R.dim0 $eltRE) a ())) |]

liftTypeRep :: TypeRep t -> TH.Type
liftTypeRep = \case
  Fun a b -> TH.AppT (TH.AppT TH.ArrowT (liftTypeRep a)) (liftTypeRep b)
  App f x -> TH.AppT (liftTypeRep f) (liftTypeRep x)
  Con tc  -> TH.ConT (TH.mkNameG_tc (tyConPackage tc) (tyConModule tc) (tyConName tc))
