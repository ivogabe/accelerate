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
import Data.Array.Accelerate.Trafo.Schedule.Uniform.Substitution   ()

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
    , Analysis usedK buildK <- analyse' next
    -> let used' =
            IdxSet.insertVar cond $ IdxSet.unions [usedT, usedF, usedK]
           usedC = IdxSet.union usedT usedF
       in  analysis used' $ \owned -> case ownedSplit usedC usedK owned of
            OwnedSplit split ownedC' ownedK' ->
              Acond
                (weaken (ownedWeaken owned) cond)
                split
                (buildT ownedC')
                (buildF ownedC')
                (buildK ownedK')
  Awhile SplitDefault SplitDefault io step initial next
    | Analysis used build <- analyse' next
    -> let usedStep  = funFreeVars step
           usedStep' = usedStep `IdxSet.union` used
           usedInit  = IdxSet.fromVars initial
           used'     = usedInit `IdxSet.union` usedStep'
       in  analysis used' $ \owned ->
            case ownedSplit usedInit usedStep' owned of
              OwnedSplit split1 ownedInit owned' ->
                case ownedSplit usedStep used owned' of
                  OwnedSplit split2 ownedStep ownedNext ->
                    Awhile split1 split2 io
                      (analyseFun' ownedStep step)
                      (mapTupR (weaken (ownedWeaken ownedInit)) initial)
                      (build ownedNext)
  AwhileSeq SplitDefault SplitDefault io step initial next
    | Analysis used build <- analyse' next
    -> let usedStep  = funFreeVars step
           usedStep' = usedStep `IdxSet.union` used
           usedInit  = IdxSet.fromVars initial
           used'     = usedInit `IdxSet.union` usedStep'
       in  analysis used' $ \owned ->
            case ownedSplit usedInit usedStep' owned of
              OwnedSplit split1 ownedInit owned' ->
                case ownedSplit usedStep used owned' of
                  OwnedSplit split2 ownedStep ownedNext ->
                    AwhileSeq split1 split2 io
                      (analyseFun' ownedStep step)
                      (mapTupR (weaken (ownedWeaken ownedInit)) initial)
                      (build ownedNext)
  Spawn SplitDefault a b
    | Analysis usedA buildA <- analyse' a
    , Analysis usedB buildB <- analyse' b
    -> let used' = usedA `IdxSet.union` usedB
       in  analysis used' $ \owned ->
            spawn (ownedSplitBoth owned) (buildA owned) (buildB owned)

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

-- | 'SubsetKeep' smart constructor
--
-- A 'SubsetKeep' is only needed when later bindings are dropped.
subsetKeep :: Subset env envSub -> Subset (env, t) (envSub, t)
subsetKeep = \case
  SubsetEnd -> SubsetEnd
  subset    -> SubsetKeep subset

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
    Release subset' s -> Release (subset >.> subset') s
    s                 -> Release subset s
  where
    (>.>)
      :: Subset env    envSub
      -> Subset envSub envSubSub
      -> Subset env    envSubSub
    SubsetEnd     >.> s2            = s2
    s1            >.> SubsetEnd     = s1
    SubsetDrop s1 >.> s2            = SubsetDrop (s1 >.> s2)
    SubsetKeep s1 >.> SubsetDrop s2 = SubsetDrop (s1 >.> s2)
    SubsetKeep s1 >.> SubsetKeep s2 = subsetKeep (s1 >.> s2)

-- | 'Spawn' smart constructor
--
-- * A binding released at the start of both subterms is instead released before
--   the 'Spawn'.
-- * A binding released at the start of a subterm is not passed to that subterm.
-- * If a binding is passed to both subterms, it does not need to be retained
--   and released.
spawn
  :: Split True env envL envR
  -> UniformScheduleRC kernel envL
  -> UniformScheduleRC kernel envR
  -> UniformScheduleRC kernel env
spawn split a b
  | Released subsetL a' <- leadingRelease a
  , Released subsetR b' <- leadingRelease b
  , Hoist subset split' <- hoist split subsetL subsetR
  = release subset (Spawn split' a' b')

leadingRelease :: UniformScheduleRC kernel env -> Released kernel env
leadingRelease = \case
  Release subset s -> Released subset s
  s                -> Released SubsetEnd s

data Released kernel env where
  Released
    :: Subset env envSub
    -> UniformScheduleRC kernel envSub
    -> Released kernel env

-- | Transform a 'Split' followed by a 'Subset' on both sides to a 'Subset'
-- followed by a 'Split'
hoist
  :: Split True env envL envR
  -> Subset envL envL'
  -> Subset envR envR'
  -> Hoist env envL' envR'
hoist (SplitLeft split) subsetL subsetR = case viewSubset subsetL of
  ViewKeep subsetL' -> case hoist split subsetL' subsetR of
    Hoist subset split' -> Hoist (subsetKeep subset) (SplitLeft split')
  ViewDrop subsetL' -> case hoist split subsetL' subsetR of
    Hoist subset split' -> Hoist (SubsetDrop subset) split'
hoist (SplitRight split) subsetL subsetR = case viewSubset subsetR of
  ViewKeep subsetR' -> case hoist split subsetL subsetR' of
    Hoist subset split' -> Hoist (subsetKeep subset) (SplitRight split')
  ViewDrop subsetR' -> case hoist split subsetL subsetR' of
    Hoist subset split' -> Hoist (SubsetDrop subset) split'
hoist (SplitBoth split) subsetL subsetR = case viewSubset subsetL of
  ViewKeep subsetL' -> case viewSubset subsetR of
    ViewKeep subsetR' -> case hoist split subsetL' subsetR' of
      Hoist subset split' -> Hoist (subsetKeep subset) (SplitBoth split')
    ViewDrop subsetR' -> case hoist split subsetL' subsetR' of
      Hoist subset split' -> Hoist (subsetKeep subset) (SplitLeft split')
  ViewDrop subsetL' -> case viewSubset subsetR of
    ViewKeep subsetR' -> case hoist split subsetL' subsetR' of
      Hoist subset split' -> Hoist (subsetKeep subset) (SplitRight split')
    ViewDrop subsetR' -> case hoist split subsetL' subsetR' of
      Hoist subset split' -> Hoist (SubsetDrop subset) split'
hoist SplitEnd SubsetEnd SubsetEnd = Hoist SubsetEnd SplitEnd

data Hoist env envL envR where
  Hoist
    :: Subset env env'
    -> Split True env' envL envR
    -> Hoist env envL envR

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
ownedWeaken owned = Weaken $ \ix -> case ownedIdx owned ix of
  Just ix' -> ix'
  Nothing  -> internalError "binding is not owned"

ownedIdx :: OwnedEnv env envRC -> Idx env t -> Maybe (Idx envRC t)
ownedIdx = \case
  OwnedKeep owned -> \case
    SuccIdx ix -> SuccIdx <$> ownedIdx owned ix
    ZeroIdx    -> Just ZeroIdx
  OwnedSkip owned -> \case
    SuccIdx ix -> ownedIdx owned ix
    ZeroIdx    -> Nothing
  OwnedEnd        -> \case
    VoidIdx x -> x

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
    Restrict subset owned' -> Restrict subset (OwnedSkip owned')

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
      OwnedSplit split ownedL ownedR ->
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
