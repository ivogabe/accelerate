{-# LANGUAGE BangPatterns          #-}
{-# LANGUAGE EmptyCase             #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TemplateHaskellQuotes #-}
{-# LANGUAGE TypeOperators         #-}
{-# OPTIONS_HADDOCK hide #-}
-- |
-- Module      : Data.Array.Accelerate.AST.Exp
-- Copyright   : [2008..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.AST.Exp (
  -- ** Scalar expressions
  ELeftHandSide, ExpVar, ExpVars, expVars, undefs,
  PreOpenFun(..),
  PreOpenExp(..),
  PrimFun(..),
  Cmp(..), negateCmp,
  PrimBool,
  PrimMaybe,
  TAG,
  IsArrayInstr(..),
  NoArrayInstr,

  -- ** Extracting type information
  expType,
  primFunType,

  -- ** Normal-form
  rnfOpenFun,
  rnfOpenExp,
  rnfConst,
  rnfPrimFun,
  rnfMaybe,
  rnfELeftHandSide,
  rnfExpVar,

  -- ** Template Haskell
  liftOpenFun,
  liftOpenExp,
  liftMaybe,
  liftELeftHandSide,
  liftExpVar,
  liftPrimFun,

  -- ** Miscellaneous
  mkConstant, mkBinary, unBody,
  formatExpOp, Direction(..),
  expIsTrivial, shapeExpVars,

) where

import Data.Array.Accelerate.AST.Idx
import Data.Array.Accelerate.AST.LeftHandSide
import Data.Array.Accelerate.AST.Var
import Data.Array.Accelerate.Error
import Data.Array.Accelerate.Representation.Elt
import Data.Array.Accelerate.Representation.Shape
import Data.Array.Accelerate.Representation.Tag
import Data.Array.Accelerate.Representation.Type
import Data.Array.Accelerate.Representation.Vec
import Data.Array.Accelerate.Sugar.Foreign
import Data.Array.Accelerate.Type
import Data.Primitive.Vec
import Data.String
import Data.Typeable                                                ( (:~:) )
import Data.ByteString.Builder                                      ( Builder )
import Data.Text                                                    ( Text )

import Control.DeepSeq
import Language.Haskell.TH.Extra                                ( CodeQ )
import Formatting
import Prelude

import GHC.TypeLits


-- Bool is not a primitive type
type PrimBool    = TAG
type PrimMaybe a = (TAG, ((), a))

-- Embedded expressions
-- --------------------

-- | Vanilla open function abstraction parameterized over array instructions
--
data PreOpenFun arr env t where
  Body ::                             PreOpenExp arr env  t -> PreOpenFun arr env t
  Lam  :: ELeftHandSide a env env' -> PreOpenFun arr env' t -> PreOpenFun arr env (a -> t)

-- | Vanilla open expressions using de Bruijn indices for variables ranging
-- over tuples of scalars and arrays of tuples. All code, except Cond, is
-- evaluated eagerly. N-tuples are represented as nested pairs.
--
-- It is parametrised over the type of array instructions, 'arr'.
--
-- The data type is parametrised over the representation type (not the
-- surface types).
--
data PreOpenExp arr env t where

  -- Local binding of a scalar expression
  Let           :: ELeftHandSide bnd_t env env'
                -> PreOpenExp arr env  bnd_t
                -> PreOpenExp arr env' body_t
                -> PreOpenExp arr env  body_t

  -- Variable index, ranging _only_ over scalars
  Evar          :: ExpVar env t
                -> PreOpenExp arr env t

  -- Apply a backend-specific foreign function
  Foreign       :: Foreign asm
                => TypeR y
                -> asm    (x -> y)            -- foreign function
                -> PreOpenFun NoArrayInstr () (x -> y) -- alternate implementation (for other backends)
                -> PreOpenExp arr env x
                -> PreOpenExp arr env y

  -- Tuples
  Pair          :: PreOpenExp arr env t1
                -> PreOpenExp arr env t2
                -> PreOpenExp arr env (t1, t2)

  Nil           :: PreOpenExp arr env ()

  -- SIMD vectors
  VecPack       :: KnownNat n
                => VecR n s tup
                -> PreOpenExp arr env tup
                -> PreOpenExp arr env (Vec n s)

  VecUnpack     :: KnownNat n
                => VecR n s tup
                -> PreOpenExp arr env (Vec n s)
                -> PreOpenExp arr env tup

  -- Shape and index conversion
  ToIndex       :: ShapeR sh
                -> PreOpenExp arr env sh           -- shape of the array
                -> PreOpenExp arr env sh           -- index into the array
                -> PreOpenExp arr env Int

  FromIndex     :: ShapeR sh
                -> PreOpenExp arr env sh           -- shape of the array
                -> PreOpenExp arr env Int          -- index into linear representation
                -> PreOpenExp arr env sh

  -- Case statement
  Case          :: PreOpenExp arr env TAG
                -> [(TAG, PreOpenExp arr env b)]      -- list of equations
                -> Maybe (PreOpenExp arr env b)       -- default case
                -> PreOpenExp arr env b

  -- Conditional expression (non-strict in 2nd and 3rd argument)
  Cond          :: PreOpenExp arr env PrimBool
                -> PreOpenExp arr env t
                -> PreOpenExp arr env t
                -> PreOpenExp arr env t

  -- Conditional expression that chooses one value based on the condition without branching.
  Select        :: PreOpenExp arr env PrimBool
                -> PreOpenExp arr env t
                -> PreOpenExp arr env t
                -> PreOpenExp arr env t

  Assert        :: Text
                -> PreOpenExp arr env PrimBool
                -> PreOpenExp arr env t
                -> PreOpenExp arr env t

  Assume        :: PreOpenExp arr env PrimBool
                -> PreOpenExp arr env t
                -> PreOpenExp arr env t

  -- Value recursion
  While         :: PreOpenFun arr env (a -> PrimBool) -- continue while true
                -> PreOpenFun arr env (a -> a)        -- function to iterate
                -> PreOpenExp arr env a               -- initial value
                -> PreOpenExp arr env a

  -- Constant values
  Const         :: ScalarType t
                -> t
                -> PreOpenExp arr env t

  -- Primitive scalar operations
  PrimApp       :: PrimFun (a -> r)
                -> PreOpenExp arr env a
                -> PreOpenExp arr env r

  ArrayInstr    :: arr (a -> b)
                -> PreOpenExp arr env a
                -> PreOpenExp arr env b 

  -- Number of elements of an array given its shape
  ShapeSize     :: ShapeR dim
                -> PreOpenExp arr env dim
                -> PreOpenExp arr env Int

  -- Unsafe operations (may fail or result in undefined behaviour)
  -- An unspecified bit pattern
  Undef         :: ScalarType t
                -> PreOpenExp arr env t

  -- Reinterpret the bits of a value as a different type
  Coerce        :: BitSizeEq a b
                => ScalarType a
                -> ScalarType b
                -> PreOpenExp arr env a
                -> PreOpenExp arr env b

expVars :: ExpVars env t -> PreOpenExp arr env t
expVars TupRunit         = Nil
expVars (TupRsingle var) = Evar var
expVars (TupRpair v1 v2) = expVars v1 `Pair` expVars v2

undefs :: TypeR t -> PreOpenExp arr env t
undefs (TupRsingle tp) = Undef tp
undefs (TupRpair t1 t2) = undefs t1 `Pair` undefs t2
undefs TupRunit = Nil

-- Types for scalar bindings
--
type ELeftHandSide = LeftHandSide ScalarType
type ExpVar        = Var ScalarType
type ExpVars env   = Vars ScalarType env

-- | The expressions are parametrised over the type of array instructions.
-- Type class 'IsArrayInstr' should be implemented for that type.
class IsArrayInstr arr where
  arrayInstrType :: arr (a -> b) -> TypeR b
  liftArrayInstr :: arr t -> CodeQ (arr t)
  rnfArrayInstr  :: arr t -> ()
  showArrayInstrOp :: arr t -> String
  encodeArrayInstr :: arr a -> Builder
  matchArrayInstr :: arr t -> arr s -> Maybe (t :~: s)
  -- | Whether the array instruction may be inlined (and duplicated)
  -- True for Parameter and False for Index
  inlineArrayInstr :: arr t -> Bool

-- | Allows no array instructions at all. Used for expressions
-- which cannot perform array operations. The only use case
-- is currently the fallback function of a foreign.
-- 
data NoArrayInstr t where

instance IsArrayInstr NoArrayInstr where
  arrayInstrType   = \case {}
  liftArrayInstr   = \case {}
  rnfArrayInstr    = \case {}
  showArrayInstrOp = \case {}
  encodeArrayInstr = \case {}
  matchArrayInstr  = \case {}
  inlineArrayInstr = \case {}

data Direction = LeftToRight | RightToLeft
  deriving Eq


-- |Primitive scalar operations
--
data PrimFun sig where

  -- operators from Num
  PrimAdd  :: NumType a -> PrimFun ((a, a) -> a)
  PrimSub  :: NumType a -> PrimFun ((a, a) -> a)
  PrimMul  :: NumType a -> PrimFun ((a, a) -> a)
  PrimNeg  :: NumType a -> PrimFun (a      -> a)
  PrimAbs  :: NumType a -> PrimFun (a      -> a)
  PrimSig  :: NumType a -> PrimFun (a      -> a)

  -- operators from Integral
  PrimQuot     :: IntegralType a -> PrimFun ((a, a)   -> a)
  PrimRem      :: IntegralType a -> PrimFun ((a, a)   -> a)
  PrimQuotRem  :: IntegralType a -> PrimFun ((a, a)   -> (a, a))
  PrimIDiv     :: IntegralType a -> PrimFun ((a, a)   -> a)
  PrimMod      :: IntegralType a -> PrimFun ((a, a)   -> a)
  PrimDivMod   :: IntegralType a -> PrimFun ((a, a)   -> (a, a))

  -- operators from Bits & FiniteBits
  PrimBAnd               :: IntegralType a -> PrimFun ((a, a)   -> a)
  PrimBOr                :: IntegralType a -> PrimFun ((a, a)   -> a)
  PrimBXor               :: IntegralType a -> PrimFun ((a, a)   -> a)
  PrimBNot               :: IntegralType a -> PrimFun (a        -> a)
  PrimBShiftL            :: IntegralType a -> PrimFun ((a, Int) -> a)
  PrimBShiftR            :: IntegralType a -> PrimFun ((a, Int) -> a)
  PrimBRotateL           :: IntegralType a -> PrimFun ((a, Int) -> a)
  PrimBRotateR           :: IntegralType a -> PrimFun ((a, Int) -> a)
  PrimPopCount           :: IntegralType a -> PrimFun (a -> Int)
  PrimCountLeadingZeros  :: IntegralType a -> PrimFun (a -> Int)
  PrimCountTrailingZeros :: IntegralType a -> PrimFun (a -> Int)

  -- operators from Fractional and Floating
  PrimFDiv        :: FloatingType a -> PrimFun ((a, a) -> a)
  PrimRecip       :: FloatingType a -> PrimFun (a      -> a)
  PrimSin         :: FloatingType a -> PrimFun (a      -> a)
  PrimCos         :: FloatingType a -> PrimFun (a      -> a)
  PrimTan         :: FloatingType a -> PrimFun (a      -> a)
  PrimAsin        :: FloatingType a -> PrimFun (a      -> a)
  PrimAcos        :: FloatingType a -> PrimFun (a      -> a)
  PrimAtan        :: FloatingType a -> PrimFun (a      -> a)
  PrimSinh        :: FloatingType a -> PrimFun (a      -> a)
  PrimCosh        :: FloatingType a -> PrimFun (a      -> a)
  PrimTanh        :: FloatingType a -> PrimFun (a      -> a)
  PrimAsinh       :: FloatingType a -> PrimFun (a      -> a)
  PrimAcosh       :: FloatingType a -> PrimFun (a      -> a)
  PrimAtanh       :: FloatingType a -> PrimFun (a      -> a)
  PrimExpFloating :: FloatingType a -> PrimFun (a      -> a)
  PrimSqrt        :: FloatingType a -> PrimFun (a      -> a)
  PrimLog         :: FloatingType a -> PrimFun (a      -> a)
  PrimFPow        :: FloatingType a -> PrimFun ((a, a) -> a)
  PrimLogBase     :: FloatingType a -> PrimFun ((a, a) -> a)

  -- FIXME: add missing operations from RealFrac & RealFloat

  -- operators from RealFrac
  PrimTruncate :: FloatingType a -> IntegralType b -> PrimFun (a -> b)
  PrimRound    :: FloatingType a -> IntegralType b -> PrimFun (a -> b)
  PrimFloor    :: FloatingType a -> IntegralType b -> PrimFun (a -> b)
  PrimCeiling  :: FloatingType a -> IntegralType b -> PrimFun (a -> b)
  -- PrimProperFraction :: FloatingType a -> IntegralType b -> PrimFun (a -> (b, a))

  -- operators from RealFloat
  PrimAtan2      :: FloatingType a -> PrimFun ((a, a) -> a)
  PrimIsNaN      :: FloatingType a -> PrimFun (a -> PrimBool)
  PrimIsInfinite :: FloatingType a -> PrimFun (a -> PrimBool)

  -- relational and equality operators
  PrimCmp  :: SingleType a -> Cmp -> PrimFun ((a, a) -> PrimBool)
  PrimMax  :: SingleType a -> PrimFun ((a, a) -> a)
  PrimMin  :: SingleType a -> PrimFun ((a, a) -> a)

  -- logical operators
  --
  -- Note that these operators are strict in both arguments. That is, the
  -- second argument of PrimLAnd is always evaluated even when the first
  -- argument is false.
  --
  -- We define (surface level) (&&) and (||) using if-then-else to enable
  -- short-circuiting, while (&&!) and (||!) are strict versions of these
  -- operators, which are defined using PrimLAnd and PrimLOr.
  --
  PrimLAnd :: PrimFun ((PrimBool, PrimBool) -> PrimBool)
  PrimLOr  :: PrimFun ((PrimBool, PrimBool) -> PrimBool)
  PrimLNot :: PrimFun (PrimBool             -> PrimBool)

  -- general conversion between types
  PrimFromIntegral :: IntegralType a -> NumType b -> PrimFun (a -> b)
  PrimToFloating   :: NumType a -> FloatingType b -> PrimFun (a -> b)

-- | Comparison operator
-- Greater-than and less-than-equal are missing, as they are equal to
-- respectively less-than and greater-than-equal with their arguments swapped.
-- We kept less-than and greater-than-equal as they are each others negation
-- (similar to equal and not-equal).
--
data Cmp = CmpLt | CmpGtEq | CmpEq | CmpNEq deriving Eq

negateCmp :: Cmp -> Cmp
negateCmp CmpLt = CmpGtEq
negateCmp CmpGtEq = CmpLt
negateCmp CmpEq = CmpNEq
negateCmp CmpNEq = CmpEq

expType :: (HasCallStack, IsArrayInstr arr) => PreOpenExp arr env t -> TypeR t
expType = \case
  Let _ _ body                 -> expType body
  Evar (Var tR _)              -> TupRsingle tR
  Foreign tR _ _ _             -> tR
  Pair e1 e2                   -> TupRpair (expType e1) (expType e2)
  Nil                          -> TupRunit
  VecPack   vecR _             -> TupRsingle $ VectorScalarType $ vecRvector vecR
  VecUnpack vecR _             -> vecRtuple vecR
  ToIndex{}                    -> TupRsingle scalarTypeInt
  FromIndex shr _ _            -> shapeType shr
  Case _ ((_,e):_) _           -> expType e
  Case _ [] (Just e)           -> expType e
  Case{}                       -> internalError "empty case encountered"
  Cond _ e _                   -> expType e
  Select _ e _                 -> expType e
  While _ (Lam lhs _) _        -> lhsToTupR lhs
  While{}                      -> internalError "What's the matter, you're running in the shadows"
  Const tR _                   -> TupRsingle tR
  PrimApp f _                  -> snd $ primFunType f
  ArrayInstr arr _             -> arrayInstrType arr
  ShapeSize{}                  -> TupRsingle scalarTypeInt
  Undef tR                     -> TupRsingle tR
  Coerce _ tR _                -> TupRsingle tR
  Assert _ _ e2                -> expType e2
  Assume _ e2                  -> expType e2

primFunType :: PrimFun (a -> b) -> (TypeR a, TypeR b)
primFunType = \case
  -- Num
  PrimAdd t                 -> binary' $ num t
  PrimSub t                 -> binary' $ num t
  PrimMul t                 -> binary' $ num t
  PrimNeg t                 -> unary'  $ num t
  PrimAbs t                 -> unary'  $ num t
  PrimSig t                 -> unary'  $ num t

  -- Integral
  PrimQuot t                -> binary' $ integral t
  PrimRem  t                -> binary' $ integral t
  PrimQuotRem t             -> unary' $ integral t `TupRpair` integral t
  PrimIDiv t                -> binary' $ integral t
  PrimMod  t                -> binary' $ integral t
  PrimDivMod t              -> unary' $ integral t `TupRpair` integral t

  -- Bits & FiniteBits
  PrimBAnd t                -> binary' $ integral t
  PrimBOr t                 -> binary' $ integral t
  PrimBXor t                -> binary' $ integral t
  PrimBNot t                -> unary' $ integral t
  PrimBShiftL t             -> (integral t `TupRpair` tint, integral t)
  PrimBShiftR t             -> (integral t `TupRpair` tint, integral t)
  PrimBRotateL t            -> (integral t `TupRpair` tint, integral t)
  PrimBRotateR t            -> (integral t `TupRpair` tint, integral t)
  PrimPopCount t            -> unary (integral t) tint
  PrimCountLeadingZeros t   -> unary (integral t) tint
  PrimCountTrailingZeros t  -> unary (integral t) tint

  -- Fractional, Floating
  PrimFDiv t                -> binary' $ floating t
  PrimRecip t               -> unary'  $ floating t
  PrimSin t                 -> unary'  $ floating t
  PrimCos t                 -> unary'  $ floating t
  PrimTan t                 -> unary'  $ floating t
  PrimAsin t                -> unary'  $ floating t
  PrimAcos t                -> unary'  $ floating t
  PrimAtan t                -> unary'  $ floating t
  PrimSinh t                -> unary'  $ floating t
  PrimCosh t                -> unary'  $ floating t
  PrimTanh t                -> unary'  $ floating t
  PrimAsinh t               -> unary'  $ floating t
  PrimAcosh t               -> unary'  $ floating t
  PrimAtanh t               -> unary'  $ floating t
  PrimExpFloating t         -> unary'  $ floating t
  PrimSqrt t                -> unary'  $ floating t
  PrimLog t                 -> unary'  $ floating t
  PrimFPow t                -> binary' $ floating t
  PrimLogBase t             -> binary' $ floating t

  -- RealFrac
  PrimTruncate a b          -> unary (floating a) (integral b)
  PrimRound a b             -> unary (floating a) (integral b)
  PrimFloor a b             -> unary (floating a) (integral b)
  PrimCeiling a b           -> unary (floating a) (integral b)

  -- RealFloat
  PrimAtan2 t               -> binary' $ floating t
  PrimIsNaN t               -> unary (floating t) tbool
  PrimIsInfinite t          -> unary (floating t) tbool

  -- Relational and equality
  PrimCmp t _               -> compare' t
  PrimMax t                 -> binary' $ single t
  PrimMin t                 -> binary' $ single t

  -- Logical
  PrimLAnd                  -> binary' tbool
  PrimLOr                   -> binary' tbool
  PrimLNot                  -> unary' tbool

  -- general conversion between types
  PrimFromIntegral a b      -> unary (integral a) (num b)
  PrimToFloating   a b      -> unary (num a) (floating b)

  where
    unary a b  = (a, b)
    unary' a   = unary a a
    binary a b = (a `TupRpair` a, b)
    binary' a  = binary a a
    compare' a = binary (single a) tbool

    single   = TupRsingle . SingleScalarType
    num      = TupRsingle . SingleScalarType . NumSingleType
    integral = num . IntegralNumType
    floating = num . FloatingNumType

    tbool    = TupRsingle scalarTypeWord8
    tint     = TupRsingle scalarTypeInt

rnfOpenFun :: forall arr env t. IsArrayInstr arr => PreOpenFun arr env t -> ()
rnfOpenFun (Body b)    = rnfOpenExp b
rnfOpenFun (Lam lhs f) = rnfELeftHandSide lhs `seq` rnfOpenFun f

rnfOpenExp :: forall arr env t. IsArrayInstr arr => PreOpenExp arr env t -> ()
rnfOpenExp topExp =
  let
      rnfF :: PreOpenFun arr env' t' -> ()
      rnfF = rnfOpenFun

      rnfE :: PreOpenExp arr env' t' -> ()
      rnfE = rnfOpenExp
  in
  case topExp of
    Let lhs bnd body          -> rnfELeftHandSide lhs `seq` rnfE bnd `seq` rnfE body
    Evar v                    -> rnfExpVar v
    Foreign tp asm f x        -> rnfTypeR tp `seq` rnf (strForeign asm) `seq` rnfOpenFun f `seq` rnfE x
    Const tp c                -> c `seq` rnfScalarType tp -- scalars should have (nf == whnf)
    Undef tp                  -> rnfScalarType tp
    Pair a b                  -> rnfE a `seq` rnfE b
    Nil                       -> ()
    VecPack   vecr e          -> rnfVecR vecr `seq` rnfE e
    VecUnpack vecr e          -> rnfVecR vecr `seq` rnfE e
    ToIndex shr sh ix         -> rnfShapeR shr `seq` rnfE sh `seq` rnfE ix
    FromIndex shr sh ix       -> rnfShapeR shr `seq` rnfE sh `seq` rnfE ix
    Case e rhs def            -> rnfE e `seq` rnfList (\(t,c) -> t `seq` rnfE c) rhs `seq` rnfMaybe rnfE def
    Cond p e1 e2              -> rnfE p `seq` rnfE e1 `seq` rnfE e2
    Select p e1 e2            -> rnfE p `seq` rnfE e1 `seq` rnfE e2
    While p f x               -> rnfF p `seq` rnfF f `seq` rnfE x
    PrimApp f x               -> rnfPrimFun f `seq` rnfE x
    ArrayInstr arr e          -> rnfArrayInstr arr `seq` rnfE e
    ShapeSize shr sh          -> rnfShapeR shr `seq` rnfE sh
    Coerce t1 t2 e            -> rnfScalarType t1 `seq` rnfScalarType t2 `seq` rnfE e
    Assert msg e1 e2          -> rnf msg `seq` rnfE e1 `seq` rnfE e2
    Assume e1 e2              -> rnfE e1 `seq` rnfE e2

rnfExpVar :: ExpVar env t -> ()
rnfExpVar = rnfVar rnfScalarType

rnfELeftHandSide :: ELeftHandSide t env env' -> ()
rnfELeftHandSide = rnfLeftHandSide rnfScalarType

rnfConst :: TypeR t -> t -> ()
rnfConst TupRunit          ()    = ()
rnfConst (TupRsingle t)    !_    = rnfScalarType t  -- scalars should have (nf == whnf)
rnfConst (TupRpair ta tb)  (a,b) = rnfConst ta a `seq` rnfConst tb b

rnfPrimFun :: PrimFun f -> ()
rnfPrimFun (PrimAdd t)                = rnfNumType t
rnfPrimFun (PrimSub t)                = rnfNumType t
rnfPrimFun (PrimMul t)                = rnfNumType t
rnfPrimFun (PrimNeg t)                = rnfNumType t
rnfPrimFun (PrimAbs t)                = rnfNumType t
rnfPrimFun (PrimSig t)                = rnfNumType t
rnfPrimFun (PrimQuot t)               = rnfIntegralType t
rnfPrimFun (PrimRem t)                = rnfIntegralType t
rnfPrimFun (PrimQuotRem t)            = rnfIntegralType t
rnfPrimFun (PrimIDiv t)               = rnfIntegralType t
rnfPrimFun (PrimMod t)                = rnfIntegralType t
rnfPrimFun (PrimDivMod t)             = rnfIntegralType t
rnfPrimFun (PrimBAnd t)               = rnfIntegralType t
rnfPrimFun (PrimBOr t)                = rnfIntegralType t
rnfPrimFun (PrimBXor t)               = rnfIntegralType t
rnfPrimFun (PrimBNot t)               = rnfIntegralType t
rnfPrimFun (PrimBShiftL t)            = rnfIntegralType t
rnfPrimFun (PrimBShiftR t)            = rnfIntegralType t
rnfPrimFun (PrimBRotateL t)           = rnfIntegralType t
rnfPrimFun (PrimBRotateR t)           = rnfIntegralType t
rnfPrimFun (PrimPopCount t)           = rnfIntegralType t
rnfPrimFun (PrimCountLeadingZeros t)  = rnfIntegralType t
rnfPrimFun (PrimCountTrailingZeros t) = rnfIntegralType t
rnfPrimFun (PrimFDiv t)               = rnfFloatingType t
rnfPrimFun (PrimRecip t)              = rnfFloatingType t
rnfPrimFun (PrimSin t)                = rnfFloatingType t
rnfPrimFun (PrimCos t)                = rnfFloatingType t
rnfPrimFun (PrimTan t)                = rnfFloatingType t
rnfPrimFun (PrimAsin t)               = rnfFloatingType t
rnfPrimFun (PrimAcos t)               = rnfFloatingType t
rnfPrimFun (PrimAtan t)               = rnfFloatingType t
rnfPrimFun (PrimSinh t)               = rnfFloatingType t
rnfPrimFun (PrimCosh t)               = rnfFloatingType t
rnfPrimFun (PrimTanh t)               = rnfFloatingType t
rnfPrimFun (PrimAsinh t)              = rnfFloatingType t
rnfPrimFun (PrimAcosh t)              = rnfFloatingType t
rnfPrimFun (PrimAtanh t)              = rnfFloatingType t
rnfPrimFun (PrimExpFloating t)        = rnfFloatingType t
rnfPrimFun (PrimSqrt t)               = rnfFloatingType t
rnfPrimFun (PrimLog t)                = rnfFloatingType t
rnfPrimFun (PrimFPow t)               = rnfFloatingType t
rnfPrimFun (PrimLogBase t)            = rnfFloatingType t
rnfPrimFun (PrimTruncate f i)         = rnfFloatingType f `seq` rnfIntegralType i
rnfPrimFun (PrimRound f i)            = rnfFloatingType f `seq` rnfIntegralType i
rnfPrimFun (PrimFloor f i)            = rnfFloatingType f `seq` rnfIntegralType i
rnfPrimFun (PrimCeiling f i)          = rnfFloatingType f `seq` rnfIntegralType i
rnfPrimFun (PrimIsNaN t)              = rnfFloatingType t
rnfPrimFun (PrimIsInfinite t)         = rnfFloatingType t
rnfPrimFun (PrimAtan2 t)              = rnfFloatingType t
rnfPrimFun (PrimCmp t !_)             = rnfSingleType t
rnfPrimFun (PrimMax t)                = rnfSingleType t
rnfPrimFun (PrimMin t)                = rnfSingleType t
rnfPrimFun PrimLAnd                   = ()
rnfPrimFun PrimLOr                    = ()
rnfPrimFun PrimLNot                   = ()
rnfPrimFun (PrimFromIntegral i n)     = rnfIntegralType i `seq` rnfNumType n
rnfPrimFun (PrimToFloating n f)       = rnfNumType n `seq` rnfFloatingType f

rnfMaybe :: (a -> ()) -> Maybe a -> ()
rnfMaybe _ Nothing  = ()
rnfMaybe f (Just x) = f x

rnfList :: (a -> ()) -> [a] -> ()
rnfList r = go
  where
    go []     = ()
    go (x:xs) = r x `seq` go xs

-- Template Haskell
-- ================

liftOpenFun
    :: IsArrayInstr arr
    => PreOpenFun arr env t
    -> CodeQ (PreOpenFun arr env t)
liftOpenFun (Lam lhs f)  = [|| Lam $$(liftELeftHandSide lhs) $$(liftOpenFun f) ||]
liftOpenFun (Body b)     = [|| Body $$(liftOpenExp b) ||]

liftOpenExp
    :: forall arr env t. IsArrayInstr arr
    => PreOpenExp arr env t
    -> CodeQ (PreOpenExp arr env t)
liftOpenExp pexp =
  let
      liftE :: PreOpenExp arr env e -> CodeQ (PreOpenExp arr env e)
      liftE = liftOpenExp

      liftF :: PreOpenFun arr env f -> CodeQ (PreOpenFun arr env f)
      liftF = liftOpenFun
  in
  case pexp of
    Let lhs bnd body          -> [|| Let $$(liftELeftHandSide lhs) $$(liftOpenExp bnd) $$(liftOpenExp body) ||]
    Evar var                  -> [|| Evar $$(liftExpVar var) ||]
    Foreign repr asm f x      -> [|| Foreign $$(liftTypeR repr) $$(liftForeign asm) $$(liftOpenFun f) $$(liftE x) ||]
    Const tp c                -> [|| Const $$(liftScalarType tp) $$(liftElt (TupRsingle tp) c) ||]
    Undef tp                  -> [|| Undef $$(liftScalarType tp) ||]
    Pair a b                  -> [|| Pair $$(liftE a) $$(liftE b) ||]
    Nil                       -> [|| Nil ||]
    VecPack   vecr e          -> [|| VecPack   $$(liftVecR vecr) $$(liftE e) ||]
    VecUnpack vecr e          -> [|| VecUnpack $$(liftVecR vecr) $$(liftE e) ||]
    ToIndex shr sh ix         -> [|| ToIndex $$(liftShapeR shr) $$(liftE sh) $$(liftE ix) ||]
    FromIndex shr sh ix       -> [|| FromIndex $$(liftShapeR shr) $$(liftE sh) $$(liftE ix) ||]
    Case p rhs def            -> [|| Case $$(liftE p) $$(liftList (\(t,c) -> [|| (t, $$(liftE c)) ||]) rhs) $$(liftMaybe liftE def) ||]
    Cond p t e                -> [|| Cond $$(liftE p) $$(liftE t) $$(liftE e) ||]
    Select p t e              -> [|| Select $$(liftE p) $$(liftE t) $$(liftE e) ||]
    While p f x               -> [|| While $$(liftF p) $$(liftF f) $$(liftE x) ||]
    PrimApp f x               -> [|| PrimApp $$(liftPrimFun f) $$(liftE x) ||]
    ArrayInstr arr x          -> [|| ArrayInstr $$(liftArrayInstr arr) $$(liftE x) ||]
    ShapeSize shr ix          -> [|| ShapeSize $$(liftShapeR shr) $$(liftE ix) ||]
    Coerce t1 t2 e            -> [|| Coerce $$(liftScalarType t1) $$(liftScalarType t2) $$(liftE e) ||]
    Assert msg e1 e2          -> [|| Assert msg $$(liftE e1) $$(liftE e2) ||]
    Assume e1 e2              -> [|| Assume $$(liftE e1) $$(liftE e2) ||]

liftPrimFun :: PrimFun f -> CodeQ (PrimFun f)
liftPrimFun (PrimAdd t)                = [|| PrimAdd $$(liftNumType t) ||]
liftPrimFun (PrimSub t)                = [|| PrimSub $$(liftNumType t) ||]
liftPrimFun (PrimMul t)                = [|| PrimMul $$(liftNumType t) ||]
liftPrimFun (PrimNeg t)                = [|| PrimNeg $$(liftNumType t) ||]
liftPrimFun (PrimAbs t)                = [|| PrimAbs $$(liftNumType t) ||]
liftPrimFun (PrimSig t)                = [|| PrimSig $$(liftNumType t) ||]
liftPrimFun (PrimQuot t)               = [|| PrimQuot $$(liftIntegralType t) ||]
liftPrimFun (PrimRem t)                = [|| PrimRem $$(liftIntegralType t) ||]
liftPrimFun (PrimQuotRem t)            = [|| PrimQuotRem $$(liftIntegralType t) ||]
liftPrimFun (PrimIDiv t)               = [|| PrimIDiv $$(liftIntegralType t) ||]
liftPrimFun (PrimMod t)                = [|| PrimMod $$(liftIntegralType t) ||]
liftPrimFun (PrimDivMod t)             = [|| PrimDivMod $$(liftIntegralType t) ||]
liftPrimFun (PrimBAnd t)               = [|| PrimBAnd $$(liftIntegralType t) ||]
liftPrimFun (PrimBOr t)                = [|| PrimBOr $$(liftIntegralType t) ||]
liftPrimFun (PrimBXor t)               = [|| PrimBXor $$(liftIntegralType t) ||]
liftPrimFun (PrimBNot t)               = [|| PrimBNot $$(liftIntegralType t) ||]
liftPrimFun (PrimBShiftL t)            = [|| PrimBShiftL $$(liftIntegralType t) ||]
liftPrimFun (PrimBShiftR t)            = [|| PrimBShiftR $$(liftIntegralType t) ||]
liftPrimFun (PrimBRotateL t)           = [|| PrimBRotateL $$(liftIntegralType t) ||]
liftPrimFun (PrimBRotateR t)           = [|| PrimBRotateR $$(liftIntegralType t) ||]
liftPrimFun (PrimPopCount t)           = [|| PrimPopCount $$(liftIntegralType t) ||]
liftPrimFun (PrimCountLeadingZeros t)  = [|| PrimCountLeadingZeros $$(liftIntegralType t) ||]
liftPrimFun (PrimCountTrailingZeros t) = [|| PrimCountTrailingZeros $$(liftIntegralType t) ||]
liftPrimFun (PrimFDiv t)               = [|| PrimFDiv $$(liftFloatingType t) ||]
liftPrimFun (PrimRecip t)              = [|| PrimRecip $$(liftFloatingType t) ||]
liftPrimFun (PrimSin t)                = [|| PrimSin $$(liftFloatingType t) ||]
liftPrimFun (PrimCos t)                = [|| PrimCos $$(liftFloatingType t) ||]
liftPrimFun (PrimTan t)                = [|| PrimTan $$(liftFloatingType t) ||]
liftPrimFun (PrimAsin t)               = [|| PrimAsin $$(liftFloatingType t) ||]
liftPrimFun (PrimAcos t)               = [|| PrimAcos $$(liftFloatingType t) ||]
liftPrimFun (PrimAtan t)               = [|| PrimAtan $$(liftFloatingType t) ||]
liftPrimFun (PrimSinh t)               = [|| PrimSinh $$(liftFloatingType t) ||]
liftPrimFun (PrimCosh t)               = [|| PrimCosh $$(liftFloatingType t) ||]
liftPrimFun (PrimTanh t)               = [|| PrimTanh $$(liftFloatingType t) ||]
liftPrimFun (PrimAsinh t)              = [|| PrimAsinh $$(liftFloatingType t) ||]
liftPrimFun (PrimAcosh t)              = [|| PrimAcosh $$(liftFloatingType t) ||]
liftPrimFun (PrimAtanh t)              = [|| PrimAtanh $$(liftFloatingType t) ||]
liftPrimFun (PrimExpFloating t)        = [|| PrimExpFloating $$(liftFloatingType t) ||]
liftPrimFun (PrimSqrt t)               = [|| PrimSqrt $$(liftFloatingType t) ||]
liftPrimFun (PrimLog t)                = [|| PrimLog $$(liftFloatingType t) ||]
liftPrimFun (PrimFPow t)               = [|| PrimFPow $$(liftFloatingType t) ||]
liftPrimFun (PrimLogBase t)            = [|| PrimLogBase $$(liftFloatingType t) ||]
liftPrimFun (PrimTruncate ta tb)       = [|| PrimTruncate $$(liftFloatingType ta) $$(liftIntegralType tb) ||]
liftPrimFun (PrimRound ta tb)          = [|| PrimRound $$(liftFloatingType ta) $$(liftIntegralType tb) ||]
liftPrimFun (PrimFloor ta tb)          = [|| PrimFloor $$(liftFloatingType ta) $$(liftIntegralType tb) ||]
liftPrimFun (PrimCeiling ta tb)        = [|| PrimCeiling $$(liftFloatingType ta) $$(liftIntegralType tb) ||]
liftPrimFun (PrimIsNaN t)              = [|| PrimIsNaN $$(liftFloatingType t) ||]
liftPrimFun (PrimIsInfinite t)         = [|| PrimIsInfinite $$(liftFloatingType t) ||]
liftPrimFun (PrimAtan2 t)              = [|| PrimAtan2 $$(liftFloatingType t) ||]
liftPrimFun (PrimCmp t c)              = [|| PrimCmp $$(liftSingleType t) $$(liftCmp c) ||]
liftPrimFun (PrimMax t)                = [|| PrimMax $$(liftSingleType t) ||]
liftPrimFun (PrimMin t)                = [|| PrimMin $$(liftSingleType t) ||]
liftPrimFun PrimLAnd                   = [|| PrimLAnd ||]
liftPrimFun PrimLOr                    = [|| PrimLOr ||]
liftPrimFun PrimLNot                   = [|| PrimLNot ||]
liftPrimFun (PrimFromIntegral ta tb)   = [|| PrimFromIntegral $$(liftIntegralType ta) $$(liftNumType tb) ||]
liftPrimFun (PrimToFloating ta tb)     = [|| PrimToFloating $$(liftNumType ta) $$(liftFloatingType tb) ||]

liftMaybe :: (a -> CodeQ a) -> Maybe a -> CodeQ (Maybe a)
liftMaybe _ Nothing  = [|| Nothing ||]
liftMaybe f (Just x) = [|| Just $$(f x) ||]

liftList :: (a -> CodeQ a) -> [a] -> CodeQ [a]
liftList _ []     = [|| [] ||]
liftList f (x:xs) = [|| $$(f x) : $$(liftList f xs) ||]

liftELeftHandSide :: ELeftHandSide t env env' -> CodeQ (ELeftHandSide t env env')
liftELeftHandSide = liftLeftHandSide liftScalarType

liftExpVar :: ExpVar env t -> CodeQ (ExpVar env t)
liftExpVar = liftVar liftScalarType

liftCmp :: Cmp -> CodeQ Cmp
liftCmp CmpLt   = [|| CmpLt ||]
liftCmp CmpGtEq = [|| CmpGtEq ||]
liftCmp CmpEq   = [|| CmpEq ||]
liftCmp CmpNEq  = [|| CmpNEq ||]

mkConstant :: TypeR t -> t -> PreOpenExp arr env t
mkConstant (TupRsingle tp)  c        = Const tp c
mkConstant (TupRpair t1 t2) (c1, c2) = mkConstant t1 c1 `Pair` mkConstant t2 c2
mkConstant TupRunit         ()       = Nil

mkBinary :: PrimFun ((a, b) -> c) -> PreOpenExp arr env a -> PreOpenExp arr env b -> PreOpenExp arr env c
mkBinary fun a b = PrimApp fun $ Pair a b

-- Extracts the body from a PreOpenFun. The type gives evidence
-- that 't' is not a function type and the PreOpenFun thus must
-- be a Body.
--
unBody :: TypeR t -> PreOpenFun arr env t -> PreOpenExp arr env t
unBody _  (Body e)  = e
unBody tp (Lam _ _) = functionImpossible tp

formatExpOp :: IsArrayInstr arr => Format r (PreOpenExp arr env t -> r)
formatExpOp = later $ \case
  Let{}           -> "Let"
  Evar (Var _ ix) -> bformat ("Var x" % int) (idxToInt ix)
  Const tp c      -> bformat ("Const " % string) (showElt (TupRsingle tp) c)
  Undef{}         -> "Undef"
  Foreign{}       -> "Foreign"
  Pair{}          -> "Pair"
  Nil{}           -> "Nil"
  VecPack{}       -> "VecPack"
  VecUnpack{}     -> "VecUnpack"
  ToIndex{}       -> "ToIndex"
  FromIndex{}     -> "FromIndex"
  Case{}          -> "Case"
  Cond{}          -> "Cond"
  Select{}        -> "Select"
  While{}         -> "While"
  PrimApp{}       -> "PrimApp"
  ArrayInstr ar _ -> fromString $ showArrayInstrOp ar
  ShapeSize{}     -> "ShapeSize"
  Coerce{}        -> "Coerce"
  Assert{}        -> "Assert"
  Assume{}        -> "Assume"

expIsTrivial :: forall arr env t. (forall s. arr s -> Bool) -> PreOpenExp arr env t -> Bool
expIsTrivial arrayInstr = \case
  Let _ bnd body          -> trav bnd && trav body
  Evar{}                  -> True
  Const{}                 -> True
  Undef{}                 -> True
  Pair a b                -> trav a && trav b
  Nil                     -> True
  VecPack _ e             -> trav e
  VecUnpack _ e           -> trav e
  ToIndex _ a b           -> trav a && trav b
  FromIndex _ a b         -> trav a && trav b
  Case scrutinee alts def -> trav scrutinee && all (trav . snd) alts && all trav def
  Cond c t f              -> trav c && trav t && trav f
  PrimApp _ a             -> trav a
  ArrayInstr ar a         -> arrayInstr ar && trav a
  ShapeSize _ a           -> trav a
  Coerce _ _ a            -> trav a
  Assert _ cond e         -> trav cond && trav e
  Assume _ e              -> trav e -- Condition is not executed, so does not have to be trivial
  _                       -> False
  where
    trav :: PreOpenExp arr env' t' -> Bool
    trav = expIsTrivial arrayInstr

shapeExpVars :: Distributes s => ShapeR sh -> Vars s env sh -> ExpVars env sh
shapeExpVars ShapeRz          TupRunit                       = TupRunit
shapeExpVars (ShapeRsnoc shr) (sh `TupRpair` TupRsingle var) = shapeExpVars shr sh `TupRpair` TupRsingle var{varType = scalarTypeInt}
shapeExpVars ShapeRz          (TupRsingle (Var tp _))        = unitImpossible tp
shapeExpVars (ShapeRsnoc _)   (TupRsingle (Var tp _))        = pairImpossible tp
