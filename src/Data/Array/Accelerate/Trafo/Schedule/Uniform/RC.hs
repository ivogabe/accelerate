{-# OPTIONS_HADDOCK hide #-}
-- |
-- Module      : Data.Array.Accelerate.Trafo.Schedule.Uniform.RC
-- Copyright   : [2012..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--
-- Transforms a 'UniformSchedule' into a 'UniformScheduleRC' by inserting
-- reference counting operations

module Data.Array.Accelerate.Trafo.Schedule.Uniform.RC (

  ConvertRC(..)

) where

import Data.Array.Accelerate.AST.Environment
import Data.Array.Accelerate.AST.Idx
import Data.Array.Accelerate.AST.IdxSet                             ( IdxSet, Present(..) )
import qualified Data.Array.Accelerate.AST.IdxSet                   as IdxSet
import Data.Array.Accelerate.AST.LeftHandSide
import Data.Array.Accelerate.AST.Schedule.Uniform
import Data.Array.Accelerate.Error
import Data.Array.Accelerate.Representation.Type
import Data.Array.Accelerate.Trafo.Substitution
import Data.Array.Accelerate.Trafo.Schedule.Uniform.Substitution    ()
import Data.Maybe                                                   ( fromMaybe )

{-------------------------------------------------------------------------------
  ConvertRC
-------------------------------------------------------------------------------}

-- | Converts a function without reference counting to a function with reference
-- counting if @rc ~ True@
class ConvertRC (rc :: Bool) where
  convertRC
    :: UniformScheduleFun     kernel () t
    -> UniformScheduleFun' rc kernel () t

instance ConvertRC False where
  convertRC = id

instance ConvertRC True where
  convertRC = transformFun

{-------------------------------------------------------------------------------
  Analysis
-------------------------------------------------------------------------------}

-- | Add reference counting to a schedule
transform :: Env Present env -> UniformSchedule kernel env -> UniformScheduleRC kernel env
transform env = \case
  Return ->
    release (releaseAll env) Return
  Alet lhs bnd next ->
    alet env lhs bnd (transform (pushLHS lhs env) next)
  Effect eff next ->
    effect env eff (transform env next)
  Acond cond SplitDefault true false next ->
    acond env cond (transform env true) (transform env false) (transform env next)
  Awhile SplitDefault SplitDefault io step initial next ->
    awhile env io (transformFun' env step) initial (transform env next)
  AwhileSeq SplitDefault SplitDefault io step initial next ->
    awhileSeq env io (transformFun' env step) initial (transform env next)
  Spawn SplitDefault a b ->
    spawn env (transform env a) (transform env b)

-- | Add reference counting to a function
--
-- The function owns the references to its arguments.
transformFun
  :: UniformScheduleFun   kernel () t
  -> UniformScheduleFunRC kernel () t
transformFun = transformFun' Empty

transformFun'
  :: Env Present env
  -> UniformScheduleFun   kernel env t
  -> UniformScheduleFunRC kernel env t
transformFun' env = \case
  Slam lhs f -> Slam lhs $ transformFun' (pushLHS lhs env) f
  Sbody body -> Sbody $ transform env body

-- | 'Release' smart constructor
--
-- * A 'Release' is omitted if no bindings are dropped.
-- * Consecutive 'Release's are merged.
release
  :: Subset env envSub
  -> UniformScheduleRC kernel envSub
  -> UniformScheduleRC kernel env
release = \case
  SubsetEnd -> id
  subset    -> \case
    Release subset' s -> Release (composeSubsets subset subset') s
    s                 -> Release subset s

-- | 'Effect' smart constructor
--
-- * 'Release's at the start of 'next' are optimised.
-- * A binding released in 'next' and not used in 'effect', is instead released
-- before the 'Effect'.
effect
  :: Env Present env
  -> Effect kernel env
  -> UniformScheduleRC kernel env
  -> UniformScheduleRC kernel env
effect env eff next
  | Exists subsetE <- restrict (effectFreeVars eff) env
  , Released subsetN next' <- leadingRelease next
  -- Even though Effect does not contain a Split, we can reuse the
  -- functionality of Splits to hoist Releases from next using 'hoist'.
  , Hoist subset split <- hoist env subsetE subsetN
  = release subset $
      Effect (weaken' (strengthenSubset subset) eff) $
        release (splitSubsetRight split) next'

-- | 'Alet' smart constructor
--
-- * 'Release's at the start of 'next' are optimised.
-- * A binding released in 'next' and not used in 'bnd', is instead released
-- before the 'Alet'.
alet
  :: Env Present env
  -> BLeftHandSide t env env'
  -> Binding env t
  -> UniformScheduleRC kernel env'
  -> UniformScheduleRC kernel env
alet env lhs bnd next
  -- Similar to 'effect', we use existing functionality via Split,
  -- even though Alet does not contain a split.
  | Exists subsetB <- restrict (bindingFreeVars bnd) env
  , Released subsetN next' <- leadingRelease next
  , SubsetHoistLHS subsetN' lhs' <- subsetHoistLHS lhs subsetN
  , Hoist subset split <- hoist env subsetB subsetN'
  , Exists lhs'' <- rebuildLHS lhs'
  = release subset $
    Alet lhs'' (weaken (strengthenSubset subset) bnd) $
      release (sinkSubsetWithLHS lhs' lhs'' (splitSubsetRight split)) next'

-- | Variant of 'sinkWithLHS' that works on a Subset instead of a weakening.
sinkSubsetWithLHS
  :: BLeftHandSide t env1 env1'
  -> BLeftHandSide t env2 env2'
  -> Subset env2  env1
  -> Subset env2' env1'
sinkSubsetWithLHS (LeftHandSideWildcard _) (LeftHandSideWildcard _) s = s
sinkSubsetWithLHS (LeftHandSideSingle _)   (LeftHandSideSingle _)   s = subsetKeep s
sinkSubsetWithLHS (LeftHandSidePair a1 b1) (LeftHandSidePair a2 b2) s = sinkSubsetWithLHS b1 b2 $ sinkSubsetWithLHS a1 a2 s
sinkSubsetWithLHS _ _ _ = internalError "left hand sides do not match"

-- | 'Acond' smart constructor
--
-- * 'Release's at the start of subterms are optimised.
-- * A binding released in both branches and next operation, but not used in the
--   conditional check, is instead released before the 'Acond'.
acond
  :: Env Present env
  -> ExpVar env PrimBool
  -> UniformScheduleRC kernel env
  -> UniformScheduleRC kernel env
  -> UniformScheduleRC kernel env
  -> UniformScheduleRC kernel env
acond env (Var tp idx) true false next
  | Released subsetT true'                <- leadingRelease true
  , Released subsetF false'               <- leadingRelease false
  , UnionSubset subsetB subsetT' subsetF' <- unionSubset subsetT subsetF
  , Released subsetN next'                <- leadingRelease next
  , Hoist' subset split subsetB' <-
      hoist' (IdxSet.singleton idx) env subsetB subsetN
  , cond'                                 <- Var tp $
      fromMaybe (internalError "condition is released") (subsetIdx subset idx)
  = release subset $
      Acond cond' split
        (release (composeSubsets subsetB' subsetT') true')
        (release (composeSubsets subsetB' subsetF') false')
        next'

-- | 'Awhile' smart constructor
awhile
  :: Env Present env
  -> InputOutputR input output
  -> UniformScheduleFunRC kernel env (input -> Output PrimBool -> output -> ())
  -> BaseVars env input
  -> UniformScheduleRC kernel env
  -> UniformScheduleRC kernel env
awhile env io step initial next
  | ReleasedFun subsetS step' <- leadingReleaseFun step
  , Exists subsetI <- restrict (IdxSet.fromVars initial) env
  , Released subsetN next' <- leadingRelease next
  , UnionSubset subsetSN subsetS' subsetN' <- unionSubset subsetS subsetN
  -- Create a split between initial and (step and next)
  , Hoist subset1 split1 <- hoist env subsetI subsetSN
  -- And then split step and next
  , Hoist subset2 split2 <- hoist (subsetEnv subsetSN env) subsetS' subsetN'
  , initial' <- mapTupR (weaken $ strengthenSubset subsetI) initial
  = case subset2 of
      SubsetEnd -> release subset1 $
        Awhile split1 split2 io step' initial' next'
      _ -> internalError "Expected subset2 to be SubsetEnd, since split1 should only pass variables to the right that are actually used in step or next"

awhileSeq
  :: Env Present env
  -> InputOutputR input output
  -> UniformScheduleFunRC kernel env (input -> OutputRef PrimBool -> output -> ())
  -> BaseVars env input
  -> UniformScheduleRC kernel env
  -> UniformScheduleRC kernel env
awhileSeq env io step initial next
  | ReleasedFun subsetS step' <- leadingReleaseFun step
  , Exists subsetI <- restrict (IdxSet.fromVars initial) env
  , Released subsetN next' <- leadingRelease next
  , UnionSubset subsetSN subsetS' subsetN' <- unionSubset subsetS subsetN
  -- Create a split between initial and (step and next)
  , Hoist subset1 split1 <- hoist env subsetI subsetSN
  -- And then split step and next
  , Hoist subset2 split2 <- hoist (subsetEnv subsetSN env) subsetS' subsetN'
  , initial' <- mapTupR (weaken $ strengthenSubset subsetI) initial
  = case subset2 of
      SubsetEnd -> release subset1 $
        AwhileSeq split1 split2 io step' initial' next'
      _ -> internalError "Expected subset2 to be SubsetEnd, since split1 should only pass variables to the right that are actually used in step or next"

-- | 'Spawn' smart constructor
--
-- * A binding released at the start of both subterms is instead released before
--   the 'Spawn'.
-- * If a binding is released at the start of a subterm, it is not passed to
--   that subterm.
spawn
  :: Env Present env
  -> UniformScheduleRC kernel env
  -> UniformScheduleRC kernel env
  -> UniformScheduleRC kernel env
spawn env a b
  | Released subsetL a' <- leadingRelease a
  , Released subsetR b' <- leadingRelease b
  , Hoist subset split <-
      hoist env subsetL subsetR
  = release subset $ Spawn split a' b'

-- | Compute subsets for two terms
--
-- Given a set of protected bindings, owned bindings, and subsets for each term,
-- this function computes the following:
--
-- 1. Initial subset: bindings kept by either subset, and protected bindings
-- 2. Split: split of the initial subset
-- 3. New left subset: left subset in the split
--
-- The computed subsets can also be thought of in terms of what is dropped:
--
-- 1. Initial subset: drops every binding dropped both subsets, unless protected
-- 2. Split: split of the initial subset
-- 3. New left subset: drops every protected binding that both subsets dropped,
--    but was kept as it was protected.
hoist'
  :: IdxSet env  -- Protected bindings
  -> Env Present env
  -> Subset env envL
  -> Subset env envR
  -> Hoist' env envL envR
hoist' protected (Push env _) subsetL subsetR
  | (isProtected, protected') <- unconsProtected protected
  = case viewSubset subsetL of
      ViewKeep subsetL' -> case viewSubset subsetR of
        ViewKeep subsetR' -> case hoist' protected' env subsetL' subsetR' of
          Hoist' subset split restL ->
            Hoist' (subsetKeep subset) (SplitBoth split) (subsetKeep restL)
        ViewDrop subsetR' -> case hoist' protected' env subsetL' subsetR' of
          Hoist' subset split restL ->
            Hoist' (subsetKeep subset) (SplitLeft split) (subsetKeep restL)
      ViewDrop subsetL' -> case viewSubset subsetR of
        ViewKeep subsetR' -> case hoist' protected' env subsetL' subsetR' of
          Hoist' subset split restL ->
            Hoist' (subsetKeep subset) (SplitRight split) restL
        ViewDrop subsetR' -> case hoist' protected' env subsetL' subsetR' of
          Hoist' subset split restL
            | isProtected ->
                Hoist' (subsetKeep subset) (SplitLeft split) (SubsetDrop restL)
            | otherwise ->
                Hoist' (SubsetDrop subset) split restL
hoist' _protected env SubsetEnd SubsetEnd =
  Hoist' SubsetEnd (splitBoth env) SubsetEnd

-- | Variant of hoist' without a protected set.
hoist
  :: Env Present env
  -> Subset env envL
  -> Subset env envR
  -> Hoist env envL envR
hoist env l r = case hoist' IdxSet.empty env l r of
  Hoist' subset split SubsetEnd -> Hoist subset split
  _ -> internalError "When protected = IdxSet.empty, the last subset should be SubsetEnd"

data Hoist' env envL' envR' where
  Hoist' :: Subset env env'
        -> Split True env' envL'' envR'
        -> Subset envL'' envL'
        -> Hoist' env envL' envR'

data Hoist env envL' envR' where
  Hoist :: Subset env env'
        -> Split True env' envL' envR'
        -> Hoist env envL' envR'

-- | Uncons the rightmost binding of a protected 'IdxSet'
--
-- This function returns whether the head bindings is protected and the rest of
-- the protected bindings.
unconsProtected :: IdxSet (env, t) -> (Bool, IdxSet env)
unconsProtected protected =
  (ZeroIdx `IdxSet.member` protected, IdxSet.drop protected)

viewSubset :: Subset (env, t) envSub -> SubsetView env t envSub
viewSubset = \case
  SubsetKeep subset -> ViewKeep subset
  SubsetDrop subset -> ViewDrop subset
  SubsetEnd         -> ViewKeep SubsetEnd

data SubsetView env t envSub where
  ViewKeep :: Subset env envSub -> SubsetView env t (envSub, t)
  ViewDrop :: Subset env envSub -> SubsetView env t envSub

-- | Construct a 'Subset' that releases all owned bindings
releaseAll :: Env Present env -> Subset env ()
releaseAll = \case
  Push e _ -> SubsetDrop (releaseAll e)
  Empty -> SubsetEnd

-- | Restrict owned bindings by the given set
--
-- All other owned bindings are released.
restrict :: IdxSet env -> Env Present env -> Exists (Subset env)
restrict set = \case
  Empty -> Exists SubsetEnd
  Push env _
    | Exists subset <- restrict (IdxSet.drop set) env ->
      if ZeroIdx `IdxSet.member` set then
        Exists $ subsetKeep subset
      else
        Exists $ SubsetDrop subset

pushLHS :: LeftHandSide s t env env' -> Env Present env -> Env Present env'
pushLHS (LeftHandSideSingle _)   env = Push env Present
pushLHS (LeftHandSideWildcard _) env = env
pushLHS (LeftHandSidePair l1 l2) env = pushLHS l2 $ pushLHS l1 env

-- | Construct a 'Split' that passes all bindings to both sides
splitBoth :: Env Present env -> Split True env env env
splitBoth = \case
  Push env _ -> SplitBoth (splitBoth env)
  Empty      -> SplitEnd

strengthenSubset :: Subset env envSub -> env :> envSub
strengthenSubset subset = Weaken $ \idx ->
  fromMaybe (internalError "Index missing after subset") (subsetIdx subset idx)
