{-# LANGUAGE ConstraintKinds     #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE PatternSynonyms     #-}
{-# LANGUAGE RebindableSyntax    #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE TypeOperators       #-}
{-# LANGUAGE ViewPatterns        #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
-- |
-- Module      : Data.Array.Accelerate.Classes.Ord
-- Copyright   : [2016..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.Classes.Ord (

  Ord(..),
  Ordering(..), pattern LT_, pattern EQ_, pattern GT_,

) where

import Data.Array.Accelerate.Analysis.Match
import Data.Array.Accelerate.Pattern
import Data.Array.Accelerate.Pattern.Ordering
import Data.Array.Accelerate.Representation.Tag
import Data.Array.Accelerate.Smart
import Data.Array.Accelerate.Sugar.Elt
import Data.Array.Accelerate.Sugar.Shape
import Data.Array.Accelerate.Type

-- We must hide (==), as that operator is used for the literals 0, 1 and 2 in the pattern synonyms for Ordering.
-- As RebindableSyntax is enabled, a literal pattern is compiled to a call to (==), meaning that the Prelude.(==) should be in scope as (==).
import Data.Array.Accelerate.Classes.Eq                             hiding ( (==) )
import qualified Data.Array.Accelerate.Classes.Eq                   as A

import Data.Char
import Language.Haskell.TH.Extra                                    hiding ( Exp )
import Prelude                                                      ( ($), (>>=), Ordering(..), Num(..), Maybe(..), String, show, error, unlines, return, concat, map, mapM )
import Text.Printf
import qualified Prelude                                            as P


infix 4 <
infix 4 >
infix 4 <=
infix 4 >=

-- | The 'Ord' class for totally ordered datatypes
--
class Eq a => Ord a where
  {-# MINIMAL (<=) | compare #-}
  (<)     :: Exp a -> Exp a -> Exp Bool
  (>)     :: Exp a -> Exp a -> Exp Bool
  (<=)    :: Exp a -> Exp a -> Exp Bool
  (>=)    :: Exp a -> Exp a -> Exp Bool
  min     :: Exp a -> Exp a -> Exp a
  max     :: Exp a -> Exp a -> Exp a
  compare :: Exp a -> Exp a -> Exp Ordering

  x <  y = if compare x y A.== constant LT then constant True  else constant False
  x <= y = if compare x y A.== constant GT then constant False else constant True
  x >  y = if compare x y A.== constant GT then constant True  else constant False
  x >= y = if compare x y A.== constant LT then constant False else constant True

  min x y = if x <= y then x else y
  max x y = if x <= y then y else x

  compare x y =
    if x A.== y then constant EQ else
    if x   <= y then constant LT
                else constant GT

-- Local redefinition for use with RebindableSyntax (pulled forward from Prelude.hs)
--
ifThenElse :: Elt a => Exp Bool -> Exp a -> Exp a -> Exp a
ifThenElse (Exp c) (Exp x) (Exp y) = Exp $ SmartExp $ Cond (mkCoerce' c) x y

instance Ord () where
  (<)     _ _ = constant False
  (>)     _ _ = constant False
  (>=)    _ _ = constant True
  (<=)    _ _ = constant True
  min     _ _ = constant ()
  max     _ _ = constant ()
  compare _ _ = constant EQ

instance Ord Z where
  (<)  _ _ = constant False
  (>)  _ _ = constant False
  (<=) _ _ = constant True
  (>=) _ _ = constant True
  min  _ _ = constant Z
  max  _ _ = constant Z


-- Instances of 'Prelude.Ord' (mostly) don't make sense with the standard
-- signatures as the return type is fixed to 'Bool'. This instance is provided
-- to provide a useful error message.
--
-- Note that 'min' and 'max' are implementable, so we do hook those into the
-- accelerate instances defined here. This allows us to use operations such as
-- 'Prelude.minimum' and 'Prelude.maximum'.
--
instance Ord a => P.Ord (Exp a) where
  (<)     = preludeError "Ord.(<)"  "(<)"
  (<=)    = preludeError "Ord.(<=)" "(<=)"
  (>)     = preludeError "Ord.(>)"  "(>)"
  (>=)    = preludeError "Ord.(>=)" "(>=)"
  min     = min
  max     = max

preludeError :: String -> String -> a
preludeError x y
  = error
  $ unlines [ printf "Prelude.%s applied to EDSL types: use Data.Array.Accelerate.%s instead" x y
            , ""
            , "These Prelude.Ord instances are present only to fulfil superclass"
            , "constraints for subsequent classes in the standard Haskell numeric"
            , "hierarchy."
            ]

runQ $ do
  let
      integralTypes :: [Name]
      integralTypes =
        [ ''Int
        , ''Int8
        , ''Int16
        , ''Int32
        , ''Int64
        , ''Word
        , ''Word8
        , ''Word16
        , ''Word32
        , ''Word64
        ]

      floatingTypes :: [Name]
      floatingTypes =
        [ ''Half
        , ''Float
        , ''Double
        ]

      nonNumTypes :: [Name]
      nonNumTypes =
        [ ''Char
        ]

      cTypes :: [Name]
      cTypes =
        [ ''CInt
        , ''CUInt
        , ''CLong
        , ''CULong
        , ''CLLong
        , ''CULLong
        , ''CShort
        , ''CUShort
        , ''CChar
        , ''CUChar
        , ''CSChar
        , ''CFloat
        , ''CDouble
        ]

      mkPrim :: Name -> Q [Dec]
      mkPrim t =
        [d| instance Ord $(conT t) where
              (<)  = mkLt
              (>)  = mkGt
              (<=) = mkLtEq
              (>=) = mkGtEq
              min  = mkMin
              max  = mkMax
          |]

      mkLt' :: [ExpQ] -> [ExpQ] -> ExpQ
      mkLt' [x] [y]       = [| $x < $y |]
      mkLt' (x:xs) (y:ys) = [| $x < $y ||! ( $x A.== $y &&! $(mkLt' xs ys) ) |]
      mkLt' _      _      = error "mkLt'"

      mkGt' :: [ExpQ] -> [ExpQ] -> ExpQ
      mkGt' [x]    [y]    = [| $x > $y |]
      mkGt' (x:xs) (y:ys) = [| $x > $y ||! ( $x A.== $y &&! $(mkGt' xs ys) ) |]
      mkGt' _      _      = error "mkGt'"

      mkLtEq' :: [ExpQ] -> [ExpQ] -> ExpQ
      mkLtEq' [x] [y]       = [| $x < $y |]
      mkLtEq' (x:xs) (y:ys) = [| $x < $y ||! ( $x A.== $y &&! $(mkLtEq' xs ys) ) |]
      mkLtEq' _      _      = error "mkLtEq'"

      mkGtEq' :: [ExpQ] -> [ExpQ] -> ExpQ
      mkGtEq' [x]    [y]    = [| $x > $y |]
      mkGtEq' (x:xs) (y:ys) = [| $x > $y ||! ( $x A.== $y &&! $(mkGtEq' xs ys) ) |]
      mkGtEq' _      _      = error "mkGtEq'"

      mkTup :: Int -> Q [Dec]
      mkTup n =
        let
            xs      = [ mkName ('x':show i) | i <- [0 .. n-1] ]
            ys      = [ mkName ('y':show i) | i <- [0 .. n-1] ]
            cst     = tupT (map (\x -> [t| Ord $(varT x) |]) xs)
            res     = tupT (map varT xs)
            pat vs  = conP (mkName ('T':show n)) (map varP vs)
        in
        [d| instance $cst => Ord $res where
              $(pat xs) <  $(pat ys) = $( mkLt' (map varE xs) (map varE ys) )
              $(pat xs) >  $(pat ys) = $( mkGt' (map varE xs) (map varE ys) )
              $(pat xs) >= $(pat ys) = $( mkGtEq' (map varE xs) (map varE ys) )
              $(pat xs) <= $(pat ys) = $( mkLtEq' (map varE xs) (map varE ys) )
          |]

  is <- mapM mkPrim integralTypes
  fs <- mapM mkPrim floatingTypes
  ns <- mapM mkPrim nonNumTypes
  cs <- mapM mkPrim cTypes
  ts <- mapM mkTup [2..16]
  return $ concat (concat [is,fs,ns,cs,ts])

instance Ord sh => Ord (sh :. Int) where
  x <= y = indexHead x <= indexHead y &&! indexTail x <= indexTail y
  x >= y = indexHead x >= indexHead y &&! indexTail x >= indexTail y
  x < y  = indexHead x < indexHead y
        &&! case matchTypeR (eltR @sh) (eltR @Z) of
             Just Refl -> constant True
             Nothing   -> indexTail x < indexTail y
  x > y  = indexHead x > indexHead y
        &&! case matchTypeR (eltR @sh) (eltR @Z) of
             Just Refl -> constant True
             Nothing   -> indexTail x > indexTail y

instance Ord Ordering where
  x < y   = mkCoerce x < (mkCoerce y :: Exp TAG)
  x > y   = mkCoerce x > (mkCoerce y :: Exp TAG)
  x <= y  = mkCoerce x <= (mkCoerce y :: Exp TAG)
  x >= y  = mkCoerce x >= (mkCoerce y :: Exp TAG)
  min x y = mkCoerce $ min (mkCoerce x) (mkCoerce y :: Exp TAG)
  max x y = mkCoerce $ max (mkCoerce x) (mkCoerce y :: Exp TAG)

