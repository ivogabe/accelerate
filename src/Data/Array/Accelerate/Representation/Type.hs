{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds   #-}
{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE EmptyCase         #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs             #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes        #-}
{-# LANGUAGE StandaloneDeriving#-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE TypeFamilies      #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeOperators     #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_HADDOCK hide #-}
-- |
-- Module      : Data.Array.Accelerate.Representation.Type
-- Copyright   : [2008..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.Representation.Type
  where

import Data.Array.Accelerate.Type
import Data.Array.Accelerate.Error
import Data.Primitive.Vec
import Data.Type.Equality

import Formatting
import Language.Haskell.TH.Extra


-- | Both arrays (Acc) and expressions (Exp) are represented as nested
-- pairs consisting of:
--
--   * unit (void)
--
--   * pairs: representing compound values (i.e. tuples) where each component
--     will be stored in a separate array.
--
--   * single array / scalar types
--     in case of expressions: values which go in registers. These may be single value
--     types such as int and float, or SIMD vectors of single value types such
--     as <4 * float>. We do not allow vectors-of-vectors.
--
data TupR s a where
  TupRunit   ::                         TupR s ()
  TupRsingle :: s a                  -> TupR s a
  TupRpair   :: TupR s a -> TupR s b -> TupR s (a, b)

deriving instance (forall a. Show (s a)) => Show (TupR s t)

formatTypeR :: Format r (TypeR a -> r)
formatTypeR = later $ \case
  TupRunit     -> "()"
  TupRsingle t -> bformat formatScalarType t
  TupRpair a b -> bformat (parenthesised (formatTypeR % "," % formatTypeR)) a b

type TypeR = TupR ScalarType

-- class IsTypeR a where
--   typeR :: TypeR a

-- instance (IsTypeR a, IsTypeR b) => IsTypeR (a,b) where
--   typeR = TupRpair typeR typeR

-- instance IsTypeR () where
--   typeR = TupRunit

-- instance IsScalar a => IsTypeR a where
--   typeR = TupRsingle scalarType 

data TupleIdx s t where
  TupleIdxLeft  :: TupleIdx l t -> TupleIdx (l, r) t
  TupleIdxRight :: TupleIdx r t -> TupleIdx (l, r) t
  TupleIdxSelf  :: TupleIdx t t

tupleLeft :: TupleIdx a (b, c) -> TupleIdx a b
tupleLeft (TupleIdxLeft  idx) = TupleIdxLeft  $ tupleLeft idx
tupleLeft (TupleIdxRight idx) = TupleIdxRight $ tupleLeft idx
tupleLeft TupleIdxSelf        = TupleIdxLeft TupleIdxSelf

tupleRight :: TupleIdx a (b, c) -> TupleIdx a c
tupleRight (TupleIdxLeft  idx) = TupleIdxLeft  $ tupleRight idx
tupleRight (TupleIdxRight idx) = TupleIdxRight $ tupleRight idx
tupleRight TupleIdxSelf        = TupleIdxRight TupleIdxSelf

-- | Distributes a type constructor over the elements of a tuple.
-- TODO: Could we make this type class injective? Then we wouldn't
-- need the type class Distributes any more.
-- Note that we must use a standard, lazy pair here, as we rely on
-- laziness in type alias Buffers to make host-device copies lazy.
--
type family Distribute f a = b where
  Distribute f () = ()
  Distribute f (a, b) = (Distribute f a, Distribute f b)
  Distribute f a = f a

class Distributes s where
  -- Shows that a single element isn't unit or a pair
  reprIsSingle :: s t -> Distribute f t :~: f t
  pairImpossible :: s (t, v) -> a
  unitImpossible :: s () -> a

instance Distributes ScalarType where
  reprIsSingle (VectorScalarType _) = Refl
  reprIsSingle (SingleScalarType (NumSingleType tp)) = case tp of
    IntegralNumType TypeInt    -> Refl
    IntegralNumType TypeInt8   -> Refl
    IntegralNumType TypeInt16  -> Refl
    IntegralNumType TypeInt32  -> Refl
    IntegralNumType TypeInt64  -> Refl
    IntegralNumType TypeWord   -> Refl
    IntegralNumType TypeWord8  -> Refl
    IntegralNumType TypeWord16 -> Refl
    IntegralNumType TypeWord32 -> Refl
    IntegralNumType TypeWord64 -> Refl
    FloatingNumType TypeHalf   -> Refl
    FloatingNumType TypeFloat  -> Refl
    FloatingNumType TypeDouble -> Refl

  pairImpossible (SingleScalarType (NumSingleType tp))
    | IntegralNumType t <- tp = case t of {}
    | FloatingNumType t <- tp = case t of {}

  unitImpossible (SingleScalarType (NumSingleType tp))
    | IntegralNumType t <- tp = case t of {}
    | FloatingNumType t <- tp = case t of {}

rnfTupR :: (forall b. s b -> ()) -> TupR s a -> ()
rnfTupR _ TupRunit       = ()
rnfTupR f (TupRsingle s) = f s
rnfTupR f (TupRpair a b) = rnfTupR f a `seq` rnfTupR f b

rnfTypeR :: TypeR t -> ()
rnfTypeR = rnfTupR rnfScalarType

tupleSize :: TupR b t -> Int
tupleSize TupRunit       = 0
tupleSize (TupRsingle _) = 1
tupleSize (TupRpair a b) = tupleSize a + tupleSize b

tupleIdxToInt :: TupR b s -> TupleIdx s t -> Int
tupleIdxToInt (TupRpair a _) (TupleIdxLeft ix) = tupleIdxToInt a ix
tupleIdxToInt (TupRpair a b) (TupleIdxRight ix) = tupleSize a + tupleIdxToInt b ix
tupleIdxToInt _              _                  = 0

prjTupleIdxR :: TupR b s -> TupleIdx s t -> TupR b t
prjTupleIdxR (TupRpair a _) (TupleIdxLeft  ix) = prjTupleIdxR a ix
prjTupleIdxR (TupRpair _ b) (TupleIdxRight ix) = prjTupleIdxR b ix
prjTupleIdxR t              TupleIdxSelf       = t
prjTupleIdxR _              _                  = internalError "Tuple mismatch"

liftTupR :: (forall b. s b -> CodeQ (s b)) -> TupR s a -> CodeQ (TupR s a)
liftTupR _ TupRunit       = [|| TupRunit ||]
liftTupR f (TupRsingle s) = [|| TupRsingle $$(f s) ||]
liftTupR f (TupRpair a b) = [|| TupRpair $$(liftTupR f a) $$(liftTupR f b) ||]

liftTypeR :: TypeR t -> CodeQ (TypeR t)
liftTypeR TupRunit         = [|| TupRunit ||]
liftTypeR (TupRsingle t)   = [|| TupRsingle $$(liftScalarType t) ||]
liftTypeR (TupRpair ta tb) = [|| TupRpair $$(liftTypeR ta) $$(liftTypeR tb) ||]

liftTypeQ :: TypeR t -> TypeQ
liftTypeQ = tuple
  where
    tuple :: TypeR t -> TypeQ
    tuple TupRunit         = [t| () |]
    tuple (TupRpair t1 t2) = [t| ($(tuple t1), $(tuple t2)) |]
    tuple (TupRsingle t)   = scalar t

    scalar :: ScalarType t -> TypeQ
    scalar (SingleScalarType t) = single t
    scalar (VectorScalarType t) = vector t

    vector :: VectorType (Vec n a) -> TypeQ
    vector (VectorType n t) = [t| Vec $(litT (numTyLit (toInteger n))) $(single t) |]

    single :: SingleType t -> TypeQ
    single (NumSingleType t) = num t

    num :: NumType t -> TypeQ
    num (IntegralNumType t) = integral t
    num (FloatingNumType t) = floating t

    integral :: IntegralType t -> TypeQ
    integral TypeInt    = [t| Int |]
    integral TypeInt8   = [t| Int8 |]
    integral TypeInt16  = [t| Int16 |]
    integral TypeInt32  = [t| Int32 |]
    integral TypeInt64  = [t| Int64 |]
    integral TypeWord   = [t| Word |]
    integral TypeWord8  = [t| Word8 |]
    integral TypeWord16 = [t| Word16 |]
    integral TypeWord32 = [t| Word32 |]
    integral TypeWord64 = [t| Word64 |]

    floating :: FloatingType t -> TypeQ
    floating TypeHalf   = [t| Half |]
    floating TypeFloat  = [t| Float |]
    floating TypeDouble = [t| Double |]

runQ $
  let
      mkT :: Int -> Q Dec
      mkT n =
        let xs  = [ mkName ('x' : show i) | i <- [0 .. n-1] ]
            ts  = map varT xs
            rhs = foldl (\a b -> [t| ($a, $b) |]) [t| () |] ts
         in
         tySynD (mkName ("Tup" ++ show n)) (map plainTV xs) rhs
  in
  mapM mkT [2..16]

mapTupR :: (forall s. a s -> b s) -> TupR a t -> TupR b t
mapTupR f (TupRsingle a)   = TupRsingle $ f a
mapTupR _ TupRunit         = TupRunit
mapTupR f (TupRpair a1 a2) = mapTupR f a1 `TupRpair` mapTupR f a2

traverseTupR :: Applicative f => (forall s. a s -> f (b s)) -> TupR a t -> f (TupR b t)
traverseTupR f (TupRsingle a)   = TupRsingle <$> f a
traverseTupR _ TupRunit         = pure TupRunit
traverseTupR f (TupRpair a1 a2) = TupRpair <$> traverseTupR f a1 <*> traverseTupR f a2

functionImpossible :: TypeR (s -> t) -> a
functionImpossible (TupRsingle (SingleScalarType (NumSingleType tp))) = case tp of
  IntegralNumType t -> case t of {}
  FloatingNumType t -> case t of {}
