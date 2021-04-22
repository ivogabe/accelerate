{-# LANGUAGE TupleSections       #-}
{-# LANGUAGE BangPatterns        #-}
{-# LANGUAGE CPP                 #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE PatternGuards       #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}
{-# LANGUAGE ViewPatterns        #-}
-- |
-- Module      : Data.Array.Accelerate.Trafo.Shrink
-- Copyright   : [2012..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--
-- The shrinking substitution arises as a restriction of beta-reduction to cases
-- where the bound variable is used zero (dead-code elimination) or one (linear
-- inlining) times. By simplifying terms, the shrinking reduction can expose
-- opportunities for further optimisation.
--
-- TODO: replace with a linear shrinking algorithm; e.g.
--
--   * Andrew Appel & Trevor Jim, "Shrinking lambda expressions in linear time".
--
--   * Nick Benton, Andrew Kennedy, Sam Lindley and Claudio Russo, "Shrinking
--     Reductions in SML.NET"
--

module Data.Array.Accelerate.Trafo.Exp.Shrink (

  -- Shrinking
  shrinkExp,
  shrinkFun,

  -- Occurrence counting
  usesOfExp, usesOfFun,

  arrayInstrsInExp, arrayInstrsInFun,

) where

import Data.Array.Accelerate.AST.Exp
import Data.Array.Accelerate.AST.Idx
import Data.Array.Accelerate.AST.LeftHandSide
import Data.Array.Accelerate.AST.Var
import Data.Array.Accelerate.Analysis.Match
import Data.Array.Accelerate.Error
import Data.Array.Accelerate.Representation.Type
import Data.Array.Accelerate.Trafo.Substitution

import qualified Data.Array.Accelerate.Debug.Internal.Stats                  as Stats

import Control.Applicative                                          hiding ( Const )
import Data.Maybe                                                   ( isJust )
import Data.Monoid
import Data.Semigroup
import Prelude                                                      hiding ( exp, seq )

data VarsRange env =
  VarsRange !(Exists (Idx env))     -- rightmost variable
            {-# UNPACK #-} !Int     -- count
            !(Maybe RangeTuple)     -- tuple

data RangeTuple
  = RTNil
  | RTSingle
  | RTPair !RangeTuple !RangeTuple

lhsVarsRange :: LeftHandSide s v env env' -> Either (env :~: env') (VarsRange env')
lhsVarsRange lhs = case rightIx lhs of
  Left eq -> Left eq
  Right ix -> let (n, rt) = go lhs
              in  Right $ VarsRange ix n rt
  where
    rightIx :: LeftHandSide s v env env' -> Either (env :~: env') (Exists (Idx env'))
    rightIx (LeftHandSideWildcard _) = Left Refl
    rightIx (LeftHandSideSingle _)   = Right $ Exists ZeroIdx
    rightIx (LeftHandSidePair l1 l2) = case rightIx l2 of
      Right ix  -> Right ix
      Left Refl -> rightIx l1

    go :: LeftHandSide s v env env' -> (Int, Maybe (RangeTuple))
    go (LeftHandSideWildcard TupRunit)   = (0,       Just RTNil)
    go (LeftHandSideWildcard _)          = (0,       Nothing)
    go (LeftHandSideSingle _)            = (1,       Just RTSingle)
    go (LeftHandSidePair l1 l2)          = (n1 + n2, RTPair <$> t1 <*> t2)
      where
        (n1, t1) = go l1
        (n2, t2) = go l2

weakenVarsRange :: LeftHandSide s v env env' -> VarsRange env -> VarsRange env'
weakenVarsRange lhs (VarsRange ix n t) = VarsRange (go lhs ix) n t
  where
    go :: LeftHandSide s v env env' -> Exists (Idx env) -> Exists (Idx env')
    go (LeftHandSideWildcard _) ix'          = ix'
    go (LeftHandSideSingle _)   (Exists ix') = Exists (SuccIdx ix')
    go (LeftHandSidePair l1 l2) ix'          = go l2 $ go l1 ix'

matchEVarsRange :: VarsRange env -> PreOpenExp arr env t -> Bool
matchEVarsRange (VarsRange (Exists first) _ (Just rt)) expr = isJust $ go (idxToInt first) rt expr
  where
    go :: Int -> RangeTuple -> PreOpenExp arr env t -> Maybe Int
    go i RTNil Nil = Just i
    go i RTSingle (Evar (Var _ ix))
      | checkIdx i ix = Just (i + 1)
    go i (RTPair t1 t2) (Pair e1 e2)
      | Just i' <- go i t2 e2 = go i' t1 e1
    go _ _ _ = Nothing

    checkIdx :: Int -> Idx env t ->  Bool
    checkIdx 0 ZeroIdx = True
    checkIdx i (SuccIdx ix) = checkIdx (i - 1) ix
    checkIdx _ _ = False
matchEVarsRange _ _ = False

varInRange :: VarsRange env -> Var s env t -> Maybe Usages
varInRange (VarsRange (Exists rangeIx) n _) (Var _ varIx) = case go rangeIx varIx of
    Nothing -> Nothing
    Just j  -> Just $ replicate j False ++ [True] ++ replicate (n - j - 1) False
  where
    -- `go ix ix'` checks whether ix <= ix' with recursion, and then checks
    -- whether ix' < ix + n in go'. Returns a Just if both checks
    -- are successful, containing an integer j such that ix + j = ix'.
    go :: Idx env u -> Idx env t -> Maybe Int
    go (SuccIdx ix) (SuccIdx ix') = go ix ix'
    go ZeroIdx      ix'           = go' ix' 0
    go _            ZeroIdx       = Nothing

    go' :: Idx env t -> Int -> Maybe Int
    go' _ j | j >= n    = Nothing
    go' ZeroIdx       j = Just j
    go' (SuccIdx ix') j = go' ix' (j + 1)

-- Describes how often the variables defined in a LHS are used together.
data Count
  = Impossible !Usages
      -- Cannot inline this definition. This happens when the definition
      -- declares multiple variables (the right hand side returns a tuple)
      -- and the variables are used seperately.
  | Infinity
      -- The variable is used in a loop. Inlining should only proceed if
      -- the computation is cheap.
  | Finite {-# UNPACK #-} !Int

type Usages = [Bool] -- Per variable a Boolean denoting whether that variable is used.

instance Semigroup Count where
  Impossible u1 <> Impossible u2 = Impossible $ zipWith (||) u1 u2
  Impossible u  <> Finite 0      = Impossible u
  Finite 0      <> Impossible u  = Impossible u
  Impossible u  <> _             = Impossible $ map (const True) u
  _             <> Impossible u  = Impossible $ map (const True) u
  Infinity      <> _             = Infinity
  _             <> Infinity      = Infinity
  Finite a      <> Finite b      = Finite $ a + b

instance Monoid Count where
  mempty = Finite 0

loopCount :: Count -> Count
loopCount (Finite n) | n > 0 = Infinity
loopCount c                  = c

shrinkLhs
    :: HasCallStack
    => Count
    -> LeftHandSide s t env1 env2
    -> Maybe (Exists (LeftHandSide s t env1))
shrinkLhs _ (LeftHandSideWildcard _) = Nothing -- We cannot shrink this
shrinkLhs (Finite 0)          lhs = Just $ Exists $ LeftHandSideWildcard $ lhsToTupR lhs -- LHS isn't used at all, replace with a wildcard
shrinkLhs (Impossible usages) lhs = case go usages lhs of
    (True , [], lhs') -> Just lhs'
    (False, [], _   ) -> Nothing -- No variables were dropped. Thus lhs == lhs'.
    _                 -> internalError "Mismatch in length of usages array and LHS"
  where
    go :: HasCallStack => Usages -> LeftHandSide s t env1 env2 -> (Bool, Usages, Exists (LeftHandSide s t env1))
    go us           (LeftHandSideWildcard tp) = (False, us, Exists $ LeftHandSideWildcard tp)
    go (True  : us) (LeftHandSideSingle tp)   = (False, us, Exists $ LeftHandSideSingle tp)
    go (False : us) (LeftHandSideSingle tp)   = (True , us, Exists $ LeftHandSideWildcard $ TupRsingle tp)
    go us           (LeftHandSidePair l1 l2)
      | (c2, us' , Exists l2') <- go us  l2
      , (c1, us'', Exists l1') <- go us' l1
      , Exists l2'' <- rebuildLHS l2'
      = let
          lhs'
            | LeftHandSideWildcard t1 <- l1'
            , LeftHandSideWildcard t2 <- l2'' = LeftHandSideWildcard $ TupRpair t1 t2
            | otherwise = LeftHandSidePair l1' l2''
        in
          (c1 || c2, us'', Exists lhs')
    go _ _ = internalError "Empty array, mismatch in length of usages array and LHS"
shrinkLhs _ _ = Nothing

-- The first LHS should be 'larger' than the second, eg the second may have
-- a wildcard if the first LHS does bind variables there, but not the other
-- way around.
--
strengthenShrunkLHS
    :: HasCallStack
    => LeftHandSide s t env1 env2
    -> LeftHandSide s t env1' env2'
    -> env1 :?> env1'
    -> env2 :?> env2'
strengthenShrunkLHS (LeftHandSideWildcard _) (LeftHandSideWildcard _) k = k
strengthenShrunkLHS (LeftHandSideSingle _)   (LeftHandSideSingle _)   k = \ix -> case ix of
  ZeroIdx     -> Just ZeroIdx
  SuccIdx ix' -> SuccIdx <$> k ix'
strengthenShrunkLHS (LeftHandSidePair lA hA) (LeftHandSidePair lB hB) k = strengthenShrunkLHS hA hB $ strengthenShrunkLHS lA lB k
strengthenShrunkLHS (LeftHandSideSingle _)   (LeftHandSideWildcard _) k = \ix -> case ix of
  ZeroIdx     -> Nothing
  SuccIdx ix' -> k ix'
strengthenShrunkLHS (LeftHandSidePair l h)   (LeftHandSideWildcard t) k = strengthenShrunkLHS h (LeftHandSideWildcard t2) $ strengthenShrunkLHS l (LeftHandSideWildcard t1) k
  where
    TupRpair t1 t2 = t
strengthenShrunkLHS (LeftHandSideWildcard _) _                        _ = internalError "Second LHS defines more variables"
strengthenShrunkLHS _                        _                        _ = internalError "Mismatch LHS single with LHS pair"


-- Shrinking
-- =========

-- The shrinking substitution for scalar expressions. This is a restricted
-- instance of beta-reduction to cases where the bound variable is used zero
-- (dead-code elimination) or one (linear inlining) times.
--
shrinkExp :: HasCallStack => PreOpenExp arr env t -> (Bool, PreOpenExp arr env t)
shrinkExp = Stats.substitution "shrinkE" . first getAny . shrinkE
  where
    -- If the bound variable is used at most this many times, it will be inlined
    -- into the body. In cases where it is not used at all, this is equivalent
    -- to dead-code elimination.
    --
    lIMIT :: Int
    lIMIT = 1

    cheap :: PreOpenExp arr env t -> Bool
    cheap (Evar _)       = True
    cheap (Pair e1 e2)   = cheap e1 && cheap e2
    cheap Nil            = True
    cheap Const{}        = True
    cheap PrimConst{}    = True
    cheap Undef{}        = True
    cheap (Coerce _ _ e) = cheap e
    cheap _              = False

    shrinkE :: HasCallStack => PreOpenExp arr env t -> (Any, PreOpenExp arr env t)
    shrinkE exp = case exp of
      Let (LeftHandSideSingle _) bnd@Evar{} body -> Stats.inline "Var"   . yes $ shrinkE (inline body bnd)
      Let lhs bnd body
        | shouldInline -> case inlineVars lhs (snd body') (snd bnd') of
            Just inlined -> Stats.betaReduce msg . yes $ shrinkE inlined
            _            -> internalError "Unexpected failure while trying to inline some expression."
        | Just (Exists lhs') <- shrinkLhs count lhs -> case strengthenE (strengthenShrunkLHS lhs lhs' Just) (snd body') of
           Just body'' -> (Any True, Let lhs' (snd bnd') body'')
           Nothing     -> internalError "Unexpected failure in strenthenE. Variable was analysed to be unused in usesOfExp, but appeared to be used in strenthenE."
        | otherwise    -> Let lhs <$> bnd' <*> body'
        where
          shouldInline = case count of
            Finite 0     -> False -- Handled by shrinkLhs
            Finite n     -> n <= lIMIT || cheap (snd bnd')
            Infinity     ->               cheap (snd bnd')
            Impossible _ -> False

          bnd'  = shrinkE bnd
          body' = shrinkE body

          -- If the lhs includes non-trivial wildcards (the last field of range is Nothing),
          -- then we cannot inline the binding. We can only check which variables are not used,
          -- to detect unused variables.
          --
          -- If the lhs does not include non-trivial wildcards (the last field of range is a Just),
          -- we can both analyse whether we can inline the binding, and check which variables are
          -- not used, to detect unused variables.
          --
          count = case lhsVarsRange lhs of
            Left _      -> Finite 0
            Right range -> usesOfExp range (snd body')

          msg = case count of
            Finite 0 -> "dead exp"
            _        -> "inline exp"   -- forced inlining when lIMIT > 1
      --
      Evar v                    -> pure (Evar v)
      Const t c                 -> pure (Const t c)
      Undef t                   -> pure (Undef t)
      Nil                       -> pure Nil
      Pair x y                  -> Pair <$> shrinkE x <*> shrinkE y
      VecPack   vec e           -> VecPack   vec <$> shrinkE e
      VecUnpack vec e           -> VecUnpack vec <$> shrinkE e
      IndexSlice x ix sh        -> IndexSlice x <$> shrinkE ix <*> shrinkE sh
      IndexFull x ix sl         -> IndexFull x <$> shrinkE ix <*> shrinkE sl
      ToIndex shr sh ix         -> ToIndex shr <$> shrinkE sh <*> shrinkE ix
      FromIndex shr sh i        -> FromIndex shr <$> shrinkE sh <*> shrinkE i
      Case e rhs def            -> Case <$> shrinkE e <*> sequenceA [ (t,) <$> shrinkE c | (t,c) <- rhs ] <*> shrinkMaybeE def
      Cond p t e                -> Cond <$> shrinkE p <*> shrinkE t <*> shrinkE e
      While p f x               -> While <$> shrinkF p <*> shrinkF f <*> shrinkE x
      PrimConst c               -> pure (PrimConst c)
      PrimApp f x               -> PrimApp f <$> shrinkE x
      ArrayInstr arr e          -> ArrayInstr arr <$> shrinkE e
      ShapeSize shr sh          -> ShapeSize shr <$> shrinkE sh
      Foreign repr ff f e       -> Foreign repr ff <$> shrinkF f <*> shrinkE e
      Coerce t1 t2 e            -> Coerce t1 t2 <$> shrinkE e

    shrinkF :: HasCallStack => PreOpenFun arr env t -> (Any, PreOpenFun arr env t)
    shrinkF = first Any . shrinkFun

    shrinkMaybeE :: HasCallStack => Maybe (PreOpenExp arr env t) -> (Any, Maybe (PreOpenExp arr env t))
    shrinkMaybeE Nothing  = pure Nothing
    shrinkMaybeE (Just e) = Just <$> shrinkE e

    first :: (a -> a') -> (a,b) -> (a',b)
    first f (x,y) = (f x, y)

    yes :: (Any, x) -> (Any, x)
    yes (_, x) = (Any True, x)

shrinkFun :: HasCallStack => PreOpenFun arr env f -> (Bool, PreOpenFun arr env f)
shrinkFun (Lam lhs f) = case lhsVarsRange lhs of
  Left Refl ->
    let b' = case lhs of
                LeftHandSideWildcard TupRunit -> b
                _                             -> True
    in (b', Lam (LeftHandSideWildcard $ lhsToTupR lhs) f')
  Right range ->
    let
      count = usesOfFun range f
    in case shrinkLhs count lhs of
        Just (Exists lhs') -> case strengthenE (strengthenShrunkLHS lhs lhs' Just) f' of
          Just f'' -> (True, Lam lhs' f'')
          Nothing  -> internalError "Unexpected failure in strenthenE. Variable was analysed to be unused in usesOfExp, but appeared to be used in strenthenE."
        Nothing -> (b, Lam lhs f')
  where
    (b, f') = shrinkFun f

shrinkFun (Body b) = Body <$> shrinkExp b

-- Occurrence Counting
-- ===================

-- Count the number of occurrences an in-scope scalar expression bound at the
-- given variable index recursively in a term.
--
usesOfExp :: forall arr env t. VarsRange env -> PreOpenExp arr env t -> Count
usesOfExp range = countE
  where
    countE :: PreOpenExp arr env e -> Count
    countE exp | matchEVarsRange range exp = Finite 1
    countE exp = case exp of
      Evar v -> case varInRange range v of
        Just cs                 -> Impossible cs
        Nothing                 -> Finite 0
      --
      Let lhs bnd body          -> countE bnd <> usesOfExp (weakenVarsRange lhs range) body
      Const _ _                 -> Finite 0
      Undef _                   -> Finite 0
      Nil                       -> Finite 0
      Pair e1 e2                -> countE e1 <> countE e2
      VecPack   _ e             -> countE e
      VecUnpack _ e             -> countE e
      IndexSlice _ ix sh        -> countE ix <> countE sh
      IndexFull _ ix sl         -> countE ix <> countE sl
      FromIndex _ sh i          -> countE sh <> countE i
      ToIndex _ sh e            -> countE sh <> countE e
      Case e rhs def            -> countE e  <> mconcat [ countE c | (_,c) <- rhs ] <> maybe (Finite 0) countE def
      Cond p t e                -> countE p  <> countE t <> countE e
      While p f x               -> countE x  <> loopCount (usesOfFun range p) <> loopCount (usesOfFun range f)
      PrimConst _               -> Finite 0
      PrimApp _ x               -> countE x
      ArrayInstr _ e            -> countE e
      ShapeSize _ sh            -> countE sh
      Foreign _ _ _ e           -> countE e
      Coerce _ _ e              -> countE e

usesOfFun :: VarsRange env -> PreOpenFun arr env f -> Count
usesOfFun range (Lam lhs f) = usesOfFun (weakenVarsRange lhs range) f
usesOfFun range (Body b)    = usesOfExp range b

arrayInstrsInExp :: PreOpenExp arr env t -> [Exists arr]
arrayInstrsInExp = (`travE` [])
  where
    travE :: PreOpenExp arr env e -> [Exists arr] -> [Exists arr]
    travE !exp !acc = case exp of
      Let _ bnd body             -> travE bnd $ travE body acc
      Evar _                     -> acc
      Const _ _                  -> acc
      Undef _                    -> acc
      Nil                        -> acc
      Pair x y                   -> travE x $ travE y acc
      VecPack   _ e              -> travE e acc
      VecUnpack _ e              -> travE e acc
      IndexSlice _ ix sh         -> travE ix $ travE sh acc
      IndexFull _ ix sl          -> travE ix $ travE sl acc
      ToIndex _ sh ix            -> travE sh $ travE ix acc
      FromIndex _ sh i           -> travE sh $ travE i acc
      Case e rhs def             -> travE e $ travAE rhs $ travME def acc
      Cond p t e                 -> travE p $ travE t $ travE e acc
      While p f x                -> travF p $ travF f $ travE x acc
      PrimConst _                -> acc
      PrimApp _ x                -> travE x acc
      ArrayInstr arr e           -> Exists arr : travE e acc
      ShapeSize _ sh             -> travE sh acc
      Foreign _ _ _ e            -> travE e acc
      Coerce _ _ e               -> travE e acc

    travME :: Maybe (PreOpenExp arr env e) -> [Exists arr] -> [Exists arr]
    travME Nothing  acc = acc
    travME (Just e) acc = travE e acc

    travAE :: [(TAG, PreOpenExp arr env b)] -> [Exists arr] -> [Exists arr]
    travAE []           acc = acc
    travAE ((_,e) : as) acc = travE e $ travAE as acc

    travF :: PreOpenFun arr env e -> [Exists arr] -> [Exists arr]
    travF (Body  e) = travE e
    travF (Lam _ f) = travF f

arrayInstrsInFun :: PreOpenFun arr env t -> [Exists arr]
arrayInstrsInFun (Body  e) = arrayInstrsInExp e
arrayInstrsInFun (Lam _ f) = arrayInstrsInFun f
