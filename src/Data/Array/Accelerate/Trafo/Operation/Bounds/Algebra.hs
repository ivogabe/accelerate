{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE EmptyCase           #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE MultiWayIf          #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE PatternGuards       #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE TypeOperators       #-}
{-# OPTIONS_HADDOCK hide #-}
-- |
-- Module      : Data.Array.Accelerate.Trafo.Operation.Bounds.Algebra
-- Copyright   : [2012..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.Trafo.Operation.Bounds.Algebra where

import Data.Array.Accelerate.AST.Environment
import Data.Array.Accelerate.AST.Idx
import Data.Array.Accelerate.AST.Graph (InEdge(..))
import Data.Array.Accelerate.AST.Operation
import Data.Array.Accelerate.Array.Buffer
import Data.Array.Accelerate.Representation.Type
import Data.Array.Accelerate.Representation.Shape hiding (union)
import Data.Array.Accelerate.Type
import Data.Array.Accelerate.Error

import Data.Typeable ( (:~:)(..) )

-- x <= y becomes an edge from x to y with distance 0.
-- x <  y becomes an edge from x to y with distance -1.
--
-- x <= y + c could become an edge from x to y with distance c.
-- We however do not track them yet, as integer overflow may happen, which is
-- difficult to track. To keep the analysis sound without making it too
-- difficult, we thus ignore that (for now).
--
data Edge s t = Edge { distance :: Integer } deriving (Eq, Ord)

-- We use bound (singular) to refer to the combination of a lowerbound and an upperbound.
-- Bounds (plural) refers to a tuple where each value is a bound.
--
-- t should be an IntegralType or a Buffer of an IntegralType
data TermBound env t = TermBound
  -- An edge from a variable x with distance c means:
  -- x <= this + c
  { lower :: PartialEnv (InEdge Edge t) env
  -- An edge to a variable y with distance c means:
  -- this <= y + c
  , upper :: PartialEnv (Edge t) env
  }

type TermBounds env = TupR (TermBound env)

bottom :: forall t env. Idx env Int -> ScalarType t -> TermBound env t
-- We could give each integral variable a lower bound and upper bound based on
-- the range of its type. That however causes that each variable is connected
-- with each other variable in the graph, so we do not include those bounds.
-- If we ever change our minds, we can use the following code:
--
-- bottom zero (SingleScalarType (NumSingleType (IntegralNumType tp)))
--   | IntegralDict <- integralDict tp
--   = boundRange zero (fromIntegral (minBound :: t)) (fromIntegral (maxBound :: t))
bottom _ _
  = TermBound PEnd PEnd

bottomGround :: Idx env Int -> GroundR t -> TermBound env t
bottomGround zero (GroundRscalar tp) = bottom zero tp
bottomGround zero (GroundRbuffer tp) = castTermBound $ bottom zero tp

nonNegative :: forall t env. Idx env Int -> ScalarType t -> TermBound env t
nonNegative zero (SingleScalarType (NumSingleType (IntegralNumType tp)))
  | IntegralDict <- integralDict tp
  = boundRange zero 0 (fromIntegral (maxBound :: t))
nonNegative _ _
  = TermBound PEnd PEnd

undefBound :: Idx env Int -> ScalarType t -> TermBound env t
-- Not sure if the range maxBound .. minBound would work in the entire
-- analysis. 0 .. 0 should definitely be safe, but then we would convert
-- Undef to 0. Hence we use 0 .. 1, the next best option.
-- In the future we may want to include a separate 'undef' value in the
-- analysis.
undefBound zero _ = boundRange zero 0 1

bottoms :: Idx env Int -> TypeR t -> TermBounds env t
bottoms zero = mapTupR (bottom zero)

bottomsGround :: Idx env Int -> GroundsR t -> TermBounds env t
bottomsGround zero = mapTupR (bottomGround zero)

boundRange :: Idx env Int -> Integer -> Integer -> TermBound env t
boundRange zero lowerB upperB = TermBound
  -- zero <= this - lowerB
  -- which (for infinite-precision Integers) is equal to
  -- lowerB <= this
  (partialEnvSingleton zero $ InEdge $ Edge $ negate lowerB)
  -- this <= zero + upperB
  (partialEnvSingleton zero $ Edge upperB)

boundConst :: Idx env Int -> Integer -> TermBound env t
boundConst zero value = boundRange zero value value

getBoundRange :: forall t env. Idx env Int -> IntegralType t -> TermBound env t -> (Integer, Integer)
getBoundRange zero tp bound
  | IntegralDict <- integralDict tp =
    ( case prjPartial zero $ lower bound of
        Just (InEdge (Edge distance')) -> negate distance'
        Nothing -> fromIntegral (minBound :: t)
    , case prjPartial zero $ upper bound of
        Just (Edge distance') -> distance'
        Nothing -> fromIntegral (maxBound :: t)
    )

boundIsBool :: Idx env Int -> TermBound env Word8 -> Bool
boundIsBool zero bound = l >= 0 && u <= 1
  where (l, u) = getBoundRange zero TypeWord8 bound

boundVar :: Idx env Int -> Idx env t -> TermBound env t
boundVar _zero ix = TermBound
  (partialEnvSingleton ix $ InEdge $ Edge 0)
  (partialEnvSingleton ix $ Edge 0)

-- Casts the bounds for a type 's' to be used for a term of type 't'.
-- This does not protect for underflow or overflow; casting from Int64 to Word8
-- is thus not always safe. It is definitely safe to cast from 't' to
-- 'Buffer t' however.
castTermBound :: TermBound env s -> TermBound env t
castTermBound (TermBound l u) = TermBound
  (mapPartialEnv (\(InEdge (Edge d)) -> InEdge $ Edge d) l)
  (mapPartialEnv (\(Edge d) -> Edge d) u)

unBufferTermBounds :: forall env t. TypeR t -> TermBounds env (Buffers t) -> TermBounds env t
unBufferTermBounds (TupRsingle tp) (TupRsingle bound)
  | Refl <- reprIsSingle @ScalarType @t @Buffer tp =
    TupRsingle $ castTermBound bound
unBufferTermBounds (TupRpair t1 t2) (TupRpair b1 b2) =
  unBufferTermBounds t1 b1 `TupRpair` unBufferTermBounds t2 b2
unBufferTermBounds TupRunit TupRunit = TupRunit
unBufferTermBounds _ _ = internalError "Tuple mismatch"

bufferTermBounds :: forall env t. TypeR t -> TermBounds env t -> TermBounds env (Buffers t)
bufferTermBounds (TupRsingle tp) (TupRsingle bound)
  | Refl <- reprIsSingle @ScalarType @t @Buffer tp =
    TupRsingle $ castTermBound bound
bufferTermBounds (TupRpair t1 t2) (TupRpair b1 b2) = bufferTermBounds t1 b1 `TupRpair` bufferTermBounds t2 b2
bufferTermBounds TupRunit TupRunit = TupRunit
bufferTermBounds _ _ = internalError "Tuple mismatch"

-- | Returns bounds that are valid for both arguments.
-- Some accuracy may be lost. 'makeTransitive' should be called to prevent most of that.
union :: TermBound env t -> TermBound env t -> TermBound env t
union a b = TermBound
  -- Note that we use 'max' instead of 'min' here as InEdge swaps the edge around, see the comments in TermBound.
  (intersectPartialEnv (\(InEdge x) (InEdge y) -> InEdge $ max x y) (lower a) (lower b))
  (intersectPartialEnv max (upper a) (upper b))

unions :: TermBounds env t -> TermBounds env t -> TermBounds env t
unions (TupRsingle a) (TupRsingle b) = TupRsingle $ union a b
unions (TupRpair a1 a2) (TupRpair b1 b2) = unions a1 b1 `TupRpair` unions a2 b2
unions TupRunit TupRunit = TupRunit
unions _ _ = internalError "Tuple mismatch"

app
  :: Idx env Int -- Index of the zero node in the bounds graph
  -> PrimFun (s -> t)
  -> OpenExp env' benv s
  -> TermBounds env s -- ^ Bounds of the argument
  -- | Transitively closed bounds of the argument. Consumed lazily (only when
  -- needed for a specific PrimFun), due to the time to make the bounds
  -- transitively closed.
  -> TermBounds env s
  -> (TermBounds env t, OpenExp env' benv t)
app zero f arg (TupRsingle bound) (TupRsingle closed) = app1 zero f arg bound closed
app zero f (Pair e1 e2) (TupRpair (TupRsingle b1) (TupRsingle b2)) (TupRpair (TupRsingle c1) (TupRsingle c2)) = app2 zero f e1 e2 b1 b2 c1 c2
app zero f arg _ _ = (bottoms zero $ snd $ primFunType f, PrimApp f arg)

app1
  :: forall env env' benv s t.
     Idx env Int
  -> PrimFun (s -> t)
  -> OpenExp env' benv s
  -> TermBound env s
  -> TermBound env s
  -> (TermBounds env t, OpenExp env' benv t)
app1 zero f arg bound closed = case f of
  PrimAbs tp@(IntegralNumType _)
    | closed `greaterThanEqual` boundConst zero 0 ->
      -- if arg >= 0, then abs arg == arg
      (TupRsingle bound, arg)
    | boundConst zero 0 `greaterThanEqual` closed ->
      (TupRsingle $ bottom zero $ SingleScalarType $ NumSingleType tp, PrimApp (PrimNeg tp) arg)
    | otherwise ->
      -- Note that we cannot assume that the result of abs is non-negative.
      -- For signed integers, abs minBound = minBound. For instance for Int8,
      -- minBound = -128, and abs (-128) = -(-128) = -128 due to integer
      -- overflow. Hence abs x >= 0 is not true for all x.
      (TupRsingle $ bottom zero $ SingleScalarType $ NumSingleType tp, PrimApp (PrimAbs tp) arg)
  -- TODO: PrimSig
  PrimFromIntegral source (IntegralNumType target) ->
    withBounds $ TupRsingle $ castIntegral zero source target closed
  _ -> withBounds $ bottoms zero $ snd $ primFunType f
  where
    withBounds :: TermBounds env t -> (TermBounds env t, OpenExp env' benv t)
    withBounds retBounds = (retBounds, PrimApp f arg)

app2
  :: forall env env' benv a b t.
     Idx env Int
  -> PrimFun ((a, b) -> t)
  -> OpenExp env' benv a
  -> OpenExp env' benv b
  -> TermBound env a
  -> TermBound env b
  -> TermBound env a -- Transitively closed bound of first argument, see comment in type signature of 'app'
  -> TermBound env b -- Transitively closed bound of second argument
  -> (TermBounds env t, OpenExp env' benv t)
app2 zero f arg1 arg2 bound1 bound2 closed1 closed2 = case f of
  -- Min & max
  PrimMin (NumSingleType (IntegralNumType _))
    | bound1 `greaterThanEqual` closed2 ->
      (TupRsingle bound2, arg2)
    | bound2 `greaterThanEqual` closed1 ->
      (TupRsingle bound1, arg1)
    | otherwise ->
      withBounds $ TupRsingle $ TermBound
        -- Note that we use 'max' instead of 'min' here as InEdge swaps the edge around, see the comments in TermBound.
        (intersectPartialEnv (\(InEdge x) (InEdge y) -> InEdge $ max x y) (lower closed1) (lower closed2))
        (unionPartialEnv min (upper bound1) (upper bound2))
  PrimMax (NumSingleType (IntegralNumType _))
    | closed2 `greaterThanEqual` bound1 ->
      (TupRsingle bound2, arg2)
    | closed1 `greaterThanEqual` bound2 ->
      (TupRsingle bound1, arg1)
    | otherwise ->
      withBounds $ TupRsingle $ TermBound
        -- Note that we use 'min' instead of 'max' here as InEdge swaps the edge around, see the comments in TermBound.
        (unionPartialEnv (\(InEdge x) (InEdge y) -> InEdge $ min x y) (lower bound1) (lower bound2))
        (intersectPartialEnv max (upper closed1) (upper closed2))
  -- Comparisons
  PrimCmp _ CmpEq
    | closed1 `equal` bound2 -> true zero
    | closed1 `notEqual` bound2 -> false zero
  PrimCmp _ CmpNEq
    | closed1 `equal` bound2 -> false zero
    | closed1 `notEqual` bound2 -> true zero
  PrimCmp (NumSingleType (IntegralNumType _)) CmpLt
    | closed1 `lessThan` bound2 -> true zero
    | closed1 `greaterThanEqual` bound2 -> false zero
  PrimCmp (NumSingleType (IntegralNumType _)) CmpGtEq
    | closed1 `lessThan` bound2 -> false zero
    | closed1 `greaterThanEqual` bound2 -> true zero
  PrimCmp (NumSingleType (IntegralNumType TypeWord8)) cmp
    | Const _ constant <- arg1
    , boundIsBool zero closed2
    , Just result <- cmpBool cmp constant arg2
      -> (TupRsingle $ boundRange zero 0 1, result)
    | Const _ constant <- arg2
    , boundIsBool zero closed1
    -- Note that we reorder the arguments to cmpBool (constant and arg1);
    -- this is sound as we only handle CmpEq and CmpNEq there
    -- (and not CmpLt and CmpGtEq)
    , Just result <- cmpBool cmp constant arg1
      -> (TupRsingle $ boundRange zero 0 1, result)
  PrimCmp _ _ -> bool
  -- Other boolean operations
  PrimIsNaN _ -> bool
  PrimIsInfinite _ -> bool
  PrimLAnd -> bool
  PrimLOr -> bool
  -- Div, Mod, Quot and rem
  PrimIDiv tp
    | Just (divBounds, _, divExpr, _, _) <- divModOrQuotRem tp
      -> (divBounds, divExpr)
  PrimQuot tp
    | Just (divBounds, _, divExpr, _, _) <- divModOrQuotRem tp
      -> (divBounds, divExpr)
  PrimMod tp
    | Just (_, modBounds, _, modExpr, _) <- divModOrQuotRem tp
      -> (modBounds, modExpr)
  PrimRem tp
    | Just (_, modBounds, _, modExpr, _) <- divModOrQuotRem tp
      -> (modBounds, modExpr)
  PrimDivMod tp
    | Just (divBounds, modBounds, _, _, divModExpr) <- divModOrQuotRem tp
      -> (TupRpair divBounds modBounds, divModExpr)
  PrimQuotRem tp
    | Just (divBounds, modBounds, _, _, divModExpr) <- divModOrQuotRem tp
      -> (TupRpair divBounds modBounds, divModExpr)

  -- Default fallback
  _ -> withBounds $ bottoms zero $ snd $ primFunType f
  where
    withBounds :: TermBounds env t -> (TermBounds env t, OpenExp env' benv t)
    withBounds retBounds = (retBounds, PrimApp f $ Pair arg1 arg2)
    
    bool :: t ~ PrimBool => (TermBounds env t, OpenExp env' benv t)
    bool = withBounds $ TupRsingle $ boundRange zero 0 1

    -- Optimize comparisons of boolean expressions with constants.
    -- 'arg' is thus assumed to be an expression that can only evaluate to 0 or
    -- 1. Note that for the constant, we only pattern match on 0 and 1,
    -- out of bounds arguments are already be handled in prior cases.
    cmpBool :: Cmp -> PrimBool -> OpenExp env' benv PrimBool -> Maybe (OpenExp env' benv PrimBool)
    cmpBool CmpEq   1 arg = Just arg -- True == arg --> arg
    cmpBool CmpEq   0 arg = Just $ PrimApp PrimLNot arg -- False == arg --> not arg
    cmpBool CmpNEq  1 arg = Just $ PrimApp PrimLNot arg -- True /= arg --> not arg
    cmpBool CmpNEq  0 arg = Just arg -- False /= arg --> arg
    -- Note: we don't pattern match on CmpLt and CmpGtEq, as that allows us to
    -- freely reorder the arguments (the constant and the expression).
    cmpBool _ _ _ = Nothing

    -- TODO: For rem, always set bounds, also if we only know that arg2 is positive?
    divModOrQuotRem :: a ~ b => IntegralType a -> Maybe (TermBounds env a, TermBounds env a, OpenExp env' benv a, OpenExp env' benv a, OpenExp env' benv (a, a))
    divModOrQuotRem tp
      -- If arg1 >= 0 and arg2 > 0, then divMod and quotRem behave the same way.
      -- Since the hardware natively supports quot and rem, not div and mod, we
      -- convert div and mod to quot and rem.
      | closed1 `greaterThanEqual` boundConst zero 0
      , boundConst zero 0 `lessThan` closed2 =
        if bound1 `lessThan` closed2 then
          let
            divExpr = case integralDict tp of
              IntegralDict -> Const (SingleScalarType $ NumSingleType $ IntegralNumType tp) 0
            modExpr = arg1
          in Just
            -- If the above, and arg1 < arg2, then
            -- arg1 `divMod` arg2 = arg1 `quotRem` arg2 = (0, arg1)
            ( TupRsingle $ boundConst zero 0
            , TupRsingle bound1
            , divExpr
            , modExpr
            , Pair divExpr modExpr
            )
        else Just
          -- Bounds of div or quot
          ( TupRsingle $ nonNegative zero $ SingleScalarType $ NumSingleType $ IntegralNumType tp
          -- Bounds of mod or rem
          , TupRsingle $ TermBound
            (partialEnvSingleton zero $ InEdge $ Edge 0)
            (upper bound2)
          , PrimApp (PrimQuot tp) $ Pair arg1 arg2
          , PrimApp (PrimRem tp) $ Pair arg1 arg2
          , PrimApp (PrimQuotRem tp) $ Pair arg1 arg2
          )
      | otherwise = Nothing

true :: Idx env Int -> (TermBounds env PrimBool, OpenExp env' benv PrimBool)
true zero = (TupRsingle $ boundConst zero 1, Const scalarType 1)

false :: Idx env Int -> (TermBounds env PrimBool, OpenExp env' benv PrimBool)
false zero = (TupRsingle $ boundConst zero 0, Const scalarType 0)

indexBounds :: forall env sh. Idx env Int -> TermBounds env sh -> TermBounds env sh
indexBounds zero = mapTupR f
  where
    f :: TermBound env t -> TermBound env t
    f (TermBound _ u) = TermBound
      (partialEnvSingleton zero $ InEdge $ Edge 0)
      (mapPartialEnv (\(Edge d) -> Edge $ d - 1) u)

fromIndex :: forall env sh. Idx env Int -> ShapeR sh -> TermBounds env sh -> TermBound env Int -> TermBounds env sh
-- TODO: We could make this more sophisticated by using the constant bounds on the Int argument.
fromIndex zero _ sz _ = indexBounds zero sz

-- Returns true if we can already proof that the first argument is greater than
-- or equal to the second argument
greaterThanEqual :: TermBound env a -> TermBound env a -> Bool
-- Search for a node that is a lower bound of the first argument,
-- and an upper bound of the second argument.
-- If we find such a node x, then
-- x <= arg1 + a
-- and
-- arg2 <= x + b
-- Thus arg2 <= x + b <= arg1 + a + b
-- Thus if a + b <= 0, then arg2 <= arg1
greaterThanEqual (TermBound low _) (TermBound _ up) =
  or
  $ partialEnvValues
  $ intersectPartialEnv
    (\(InEdge (Edge a)) (Edge b) -> IdentityF $ a + b <= 0)
    low
    up

lessThan :: TermBound env a -> TermBound env a -> Bool
lessThan (TermBound _ up) (TermBound low _) =
  -- Similar to greaterThanEqual
  or
  $ partialEnvValues
  $ intersectPartialEnv
    (\(InEdge (Edge a)) (Edge b) -> IdentityF $ a + b < 0)
    low
    up

equal :: TermBound env a -> TermBound env a -> Bool
equal a b = greaterThanEqual a b && greaterThanEqual b a

notEqual :: TermBound env a -> TermBound env a -> Bool
notEqual a b = lessThan a b || lessThan b a

cast :: Idx env Int -> ScalarType s -> ScalarType t -> TermBound env s -> TermBound env t
cast zero (SingleScalarType (NumSingleType (IntegralNumType source))) (SingleScalarType (NumSingleType (IntegralNumType target))) bound
  = castIntegral zero source target bound
cast zero _ target _ = bottom zero target

castIntegral :: Idx env Int -> IntegralType s -> IntegralType t -> TermBound env s -> TermBound env t
castIntegral zero source target bound
  | (sourceMin, sourceMax) <- getBoundRange zero source bound
  , (targetMin, targetMax) <- intRange target
  , targetMin <= sourceMin -- Check if the source fits in the target
  , sourceMax <= targetMax
  = castTermBound bound -- It fits, we can preserve all information
  | otherwise
  -- It might not fit, we can't preserve bound information due to possible overflow or underflow
  = bottom zero $ SingleScalarType $ NumSingleType $ IntegralNumType target

intRange :: forall t. IntegralType t -> (Integer, Integer)
intRange tp
  | IntegralDict <- integralDict tp = (fromIntegral (minBound :: t), fromIntegral (maxBound :: t))

-- Returns Nothing if the value is above or below the valid range of this integral type
guardOverflow :: IntegralType t -> Integer -> Maybe Integer
guardOverflow tp x
  | x < a || x > b = Nothing
  | otherwise = Just x
  where
    (a, b) = intRange tp

saturate :: IntegralType t -> Integer -> Integer
saturate tp x = max a $ min b x
  where
    (a, b) = intRange tp
