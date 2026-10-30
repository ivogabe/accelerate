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

  ConvertRC(..),
  analyse, analyseFun,

) where

import Data.Array.Accelerate.AST.Environment
import Data.Array.Accelerate.AST.Idx
import Data.Array.Accelerate.AST.IdxSet                             ( IdxSet )
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
  convertRC = analyseFun

{-------------------------------------------------------------------------------
  Analysis
-------------------------------------------------------------------------------}

-- | Add reference counting to a schedule
analyse
  :: Env f env  -- ^ Full structure of the environment (values not used)
  -> UniformSchedule   kernel env
  -> UniformScheduleRC kernel env
analyse env schedule
  | Analysis _used build <- analyse' schedule
  = build (ownedAll env)

analyse' :: UniformSchedule kernel env -> Analysis kernel env
analyse' = \case
  Return -> Analysis IdxSet.empty $ \owned ->
    release (ownedReleaseAll owned) Return
  Alet lhs bnd next
    | Analysis used build <- analyse' next
    -> let used' = bindingFreeVars bnd `IdxSet.union` IdxSet.drop' lhs used
       in  analysis used' $ \owned -> case ownedLHS lhs owned of
            OwnedLHS lhs' owned' ->
              Alet lhs' (weaken (ownedWeaken owned) bnd) (build owned')
  Effect effect next
    | Analysis used build <- analyse' next
    -> let used' = effectFreeVars effect `IdxSet.union` used
       in  analysis used' $ \owned ->
            Effect (weaken' (ownedWeaken owned) effect) (build owned)
  Acond cond SplitDefault true false next
    | Analysis usedT buildT <- analyse' true
    , Analysis usedF buildF <- analyse' false
    , Analysis usedN buildN <- analyse' next
    -> let usedC = IdxSet.union usedT usedF
           used' = IdxSet.insertVar cond $ IdxSet.union usedC usedN
       in  analysis used' $ \owned ->
            acond
              (weaken (ownedWeaken owned) cond)
              owned
              (buildT owned)
              (buildF owned)
              (buildN owned)
  Awhile SplitDefault SplitDefault io step initial next
    | Analysis used build <- analyse' next
    -> let usedS  = funFreeVars step
           usedS' = usedS `IdxSet.union` used
           usedI  = IdxSet.fromVars initial
           used'  = usedI `IdxSet.union` usedS'
       in  analysis used' $ \owned ->
            case ownedSplit usedI usedS' owned of
              OwnedSplit split1 ownedI owned' ->
                case ownedSplit usedS used owned' of
                  OwnedSplit split2 ownedS ownedN ->
                    Awhile split1 split2 io
                      (analyseFun' ownedS step)
                      (mapTupR (weaken (ownedWeaken ownedI)) initial)
                      (build ownedN)
  AwhileSeq SplitDefault SplitDefault io step initial next
    | Analysis used build <- analyse' next
    -> let usedS  = funFreeVars step
           usedS' = usedS `IdxSet.union` used
           usedI  = IdxSet.fromVars initial
           used'  = usedI `IdxSet.union` usedS'
       in  analysis used' $ \owned ->
            case ownedSplit usedI usedS' owned of
              OwnedSplit split1 ownedI owned' ->
                case ownedSplit usedS used owned' of
                  OwnedSplit split2 ownedS ownedN ->
                    AwhileSeq split1 split2 io
                      (analyseFun' ownedS step)
                      (mapTupR (weaken (ownedWeaken ownedI)) initial)
                      (build ownedN)
  Spawn SplitDefault a b
    | Analysis usedA buildA <- analyse' a
    , Analysis usedB buildB <- analyse' b
    -> let used' = usedA `IdxSet.union` usedB
       in  analysis used' $ \owned ->
            spawn owned (buildA owned) (buildB owned)

-- | Add reference counting to a function
--
-- The function owns the references to its arguments.
analyseFun
  :: UniformScheduleFun   kernel () t
  -> UniformScheduleFunRC kernel () t
analyseFun = analyseFun' OwnedEnd

analyseFun'
  :: OwnedEnv env envRC
  -> UniformScheduleFun   kernel env   t
  -> UniformScheduleFunRC kernel envRC t
analyseFun' owned = \case
  Slam lhs f
    | OwnedLHS lhs' owned' <- ownedLHS lhs owned
    -> Slam lhs' (analyseFun' owned' f)
  Sbody body
    | Analysis _used build <- analyse' body
    -> Sbody (build owned)

-- | Construct an 'Analysis' that first releases unused owned bindings
analysis
  :: IdxSet env
  -> (forall envRC. OwnedEnv env envRC -> UniformScheduleRC kernel envRC)
  -> Analysis kernel env
analysis used build = Analysis used $ \owned ->
  case restrict used owned of
    Restrict subset owned' -> release subset (build owned')

data Analysis kernel env where
  Analysis
    :: IdxSet env
    -- ^ Bindings used in the term
    -> (forall envRC. OwnedEnv env envRC -> UniformScheduleRC kernel envRC)
    -- ^ Construct the term with reference counting given currently owned
    -- bindings (superset of bindings used in the term)
    -> Analysis kernel env

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

-- | 'Acond' smart constructor
--
-- * 'Release's at the start of subterms are optimised.
-- * A binding released in both branches and next operation, but not used in the
--   conditional check, is instead released before the 'Acond'.
acond
  :: ExpVar env PrimBool
  -> OwnedEnv env' env
  -> UniformScheduleRC kernel env
  -> UniformScheduleRC kernel env
  -> UniformScheduleRC kernel env
  -> UniformScheduleRC kernel env
acond (Var tp idx) owned true false next
  | Released subsetT true'                <- leadingRelease true
  , Released subsetF false'               <- leadingRelease false
  , UnionSubset subsetB subsetT' subsetF' <- unionSubset subsetT subsetF
  , Released subsetN next'                <- leadingRelease next
  , Hoist subset split subsetB' subsetN'  <-
      hoist (IdxSet.singleton idx) owned subsetB subsetN
  , cond'                                 <- Var tp $
      fromMaybe (internalError "condition is released") (subsetIdx subset idx)
  = release subset $
      Acond cond' split
        (release (composeSubsets subsetB' subsetT') true')
        (release (composeSubsets subsetB' subsetF') false')
        (release subsetN' next')

-- | 'Spawn' smart constructor
--
-- * A binding released at the start of both subterms is instead released before
--   the 'Spawn'.
-- * If a binding is released at the start of a subterm, it is not passed to
--   that subterm.
spawn
  :: OwnedEnv env' env
  -> UniformScheduleRC kernel env
  -> UniformScheduleRC kernel env
  -> UniformScheduleRC kernel env
spawn owned a b
  | Released subsetL a'                  <- leadingRelease a
  , Released subsetR b'                  <- leadingRelease b
  , Hoist subset split subsetL' subsetR' <-
      hoist IdxSet.empty owned subsetL subsetR
  = release subset $ Spawn split (release subsetL' a') (release subsetR' b')

-- | Compute subsets for two terms
--
-- Given a set of protected bindings, owned bindings, and subsets for each term,
-- this function computes the following:
--
-- 1. Initial subset: bindings kept by either subset, and protected bindings
-- 2. Split: split of the initial subset
-- 3. New left subset: left subset in the split
-- 4. New right subset: right subset in the split
--
-- The computed subsets can also be thought of in terms of what is dropped:
--
-- 1. Initial subset: drops every binding dropped both subsets, unless protected
-- 2. Split: split of the initial subset
-- 3. New left subset: drops every protected binding that both subsets dropped
-- 4. New right subset: drops every protected binding dropped by right subset
hoist
  :: IdxSet env  -- Protected bindings
  -> OwnedEnv env' env
  -> Subset env envL
  -> Subset env envR
  -> Hoist env envL envR
hoist protected (OwnedKeep owned) subsetL subsetR
  | (isProtected, protected') <- unconsProtected protected
  = case viewSubset subsetL of
      ViewKeep subsetL' -> case viewSubset subsetR of
        ViewKeep subsetR' -> case hoist protected' owned subsetL' subsetR' of
          Hoist subset split restL restR ->
            Hoist (subsetKeep subset) (SplitBoth split) (subsetKeep restL) (subsetKeep restR)
        ViewDrop subsetR' -> case hoist protected' owned subsetL' subsetR' of
          Hoist subset split restL restR ->
            Hoist (subsetKeep subset) (SplitLeft split) (subsetKeep restL) restR
      ViewDrop subsetL' -> case viewSubset subsetR of
        ViewKeep subsetR' -> case hoist protected' owned subsetL' subsetR' of
          Hoist subset split restL restR ->
            Hoist (subsetKeep subset) (SplitRight split) restL (subsetKeep restR)
        ViewDrop subsetR' -> case hoist protected' owned subsetL' subsetR' of
          Hoist subset split restL restR
            | isProtected ->
                Hoist (subsetKeep subset) (SplitLeft split) (SubsetDrop restL) restR
            | otherwise ->
                Hoist (SubsetDrop subset) split restL restR
hoist protected (OwnedSkip owned) subsetL subsetR =
  hoist protected owned subsetL subsetR
hoist _protected owned SubsetEnd SubsetEnd =
  Hoist SubsetEnd (ownedSplitBoth owned) SubsetEnd SubsetEnd

data Hoist env envL' envR' where
  Hoist :: Subset env env'
        -> Split True env' envL'' envR''
        -> Subset envL'' envL'
        -> Subset envR'' envR'
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

{-------------------------------------------------------------------------------
  OwnedEnv
-------------------------------------------------------------------------------}

-- | Subset of bindings in an environment that are owned
--
-- 'Subset' cannot be used because this must specify membership across all
-- bindings in the environment, not just the rightmost.  This type is isomorphic
-- to 'Data.Array.Accelerate.Trafo.LiveVars.ReEnv'.
data OwnedEnv env envRC where
  OwnedKeep :: OwnedEnv env envRC -> OwnedEnv (env, t) (envRC, t)
  OwnedSkip :: OwnedEnv env envRC -> OwnedEnv (env, t)  envRC
  OwnedEnd  :: OwnedEnv () ()

-- | Construct an 'OwnedEnv' where all bindings are owned
ownedAll :: Env f env -> OwnedEnv env env
ownedAll = \case
  Push env _ -> OwnedKeep (ownedAll env)
  Empty      -> OwnedEnd

-- | Construct a weakening of owned bindings
ownedWeaken :: OwnedEnv env envRC -> env :> envRC
ownedWeaken owned = Weaken $ \idx -> case ownedIdx owned idx of
  Just idx' -> idx'
  Nothing   -> internalError "binding is not owned"

ownedIdx :: OwnedEnv env envRC -> env :?> envRC
ownedIdx = \case
  OwnedKeep owned -> \case
    SuccIdx idx -> SuccIdx <$> ownedIdx owned idx
    ZeroIdx     -> Just ZeroIdx
  OwnedSkip owned -> \case
    SuccIdx idx -> ownedIdx owned idx
    ZeroIdx     -> Nothing
  OwnedEnd        -> \case
    VoidIdx x   -> x

-- | Construct a 'Subset' that releases all owned bindings
ownedReleaseAll :: OwnedEnv env envRC -> Subset envRC ()
ownedReleaseAll = \case
  OwnedKeep owned -> SubsetDrop (ownedReleaseAll owned)
  OwnedSkip owned -> ownedReleaseAll owned
  OwnedEnd        -> SubsetEnd

-- | Restrict owned bindings by the given set
--
-- All other owned bindings are released.
restrict :: IdxSet env -> OwnedEnv env envRC -> Restrict env envRC
restrict set = \case
  OwnedEnd        -> Restrict SubsetEnd OwnedEnd
  OwnedKeep owned -> case restrict (IdxSet.drop set) owned of
    Restrict subset owned'
      | ZeroIdx `IdxSet.member` set ->
        Restrict (subsetKeep subset) (OwnedKeep owned')
      | otherwise ->
        Restrict (SubsetDrop subset) (OwnedSkip owned')
  OwnedSkip owned -> case restrict (IdxSet.drop set) owned of
    Restrict subset owned'
      | ZeroIdx `IdxSet.member` set ->
        internalError "used binding is not owned"
      | otherwise ->
        Restrict subset (OwnedSkip owned')

data Restrict env envRC where
  Restrict
    :: Subset   envRC envRCSub
    -> OwnedEnv env   envRCSub
    -> Restrict env   envRC

-- | Bindings introduced by an LHS are owned
ownedLHS
  :: BLeftHandSide t env env'
  -> OwnedEnv env envRC
  -> OwnedLHS t env' envRC
ownedLHS (LeftHandSideWildcard tp) owned =
  OwnedLHS (LeftHandSideWildcard tp) owned
ownedLHS (LeftHandSideSingle tp) owned =
  OwnedLHS (LeftHandSideSingle tp) (OwnedKeep owned)
ownedLHS (LeftHandSidePair l1 l2) owned
  | OwnedLHS l1' owned1 <- ownedLHS l1 owned
  , OwnedLHS l2' owned2 <- ownedLHS l2 owned1
  = OwnedLHS (LeftHandSidePair l1' l2') owned2

data OwnedLHS t env' envRC where
  OwnedLHS
    :: BLeftHandSide t envRC envRC'
    -> OwnedEnv        env'  envRC'
    -> OwnedLHS      t env'  envRC

-- | Split owned bindings
--
-- Bindings used by neither are associated with the left (conditional).
ownedSplit
  :: IdxSet     env  -- ^ Bindings used on the left (conditional)
  -> IdxSet     env  -- ^ Bindings used on the right (continuation)
  -> OwnedEnv   env envRC
  -> OwnedSplit env envRC
ownedSplit setL setR = \case
  OwnedKeep owned ->
    case ownedSplit (IdxSet.drop setL) (IdxSet.drop setR) owned of
      OwnedSplit split ownedL ownedR
        | not (ZeroIdx `IdxSet.member` setR) ->
          OwnedSplit (SplitLeft  split) (OwnedKeep ownedL) (OwnedSkip ownedR)
        | ZeroIdx `IdxSet.member` setL ->
          OwnedSplit (SplitBoth  split) (OwnedKeep ownedL) (OwnedKeep ownedR)
        | otherwise ->
          OwnedSplit (SplitRight split) (OwnedSkip ownedL) (OwnedKeep ownedR)
  OwnedSkip owned ->
    case ownedSplit (IdxSet.drop setL) (IdxSet.drop setR) owned of
      OwnedSplit split ownedL ownedR
        | ZeroIdx `IdxSet.member` setL || ZeroIdx `IdxSet.member` setR ->
          internalError "used binding is not owned"
        | otherwise ->
          OwnedSplit split (OwnedSkip ownedL) (OwnedSkip ownedR)
  OwnedEnd        -> OwnedSplit SplitEnd OwnedEnd OwnedEnd

data OwnedSplit env envRC where
  OwnedSplit
    :: Split True envRC envRCL envRCR
    -> OwnedEnv env envRCL
    -> OwnedEnv env envRCR
    -> OwnedSplit env envRC

-- | Construct a 'Split' that passes owned bindings to both sides
ownedSplitBoth :: OwnedEnv env envRC -> Split True envRC envRC envRC
ownedSplitBoth = \case
  OwnedKeep owned -> SplitBoth (ownedSplitBoth owned)
  OwnedSkip owned -> ownedSplitBoth owned
  OwnedEnd        -> SplitEnd
