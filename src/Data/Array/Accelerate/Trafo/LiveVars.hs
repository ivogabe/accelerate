{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE MultiWayIf          #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}
{-# OPTIONS_HADDOCK hide #-}
-- |
-- Module      : Data.Array.Accelerate.Trafo.LiveVars
-- Copyright   : [2012..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--
-- Utilties for creating a dead variable / (strongly) live
-- variable analysis on one of our IRs.
--

module Data.Array.Accelerate.Trafo.LiveVars
  -- ANALYSIS
  -- Liveness env
  ( LivenessEnv, emptyLivenessEnv
  , lEnvPush, lEnvPushLHS
  -- Constraints
  , addLiveImplies, addLiveImplications
  , setLive, setIdxSetLive, setVarsLive
  -- Strengthen liveness env
  , lEnvStrengthen, lEnvStrengthenLHS, lEnvStrengthenLHSReturn, LHSLiveness
  , ReturnImplication(..), ReturnImplications, returnImplicationsLive
  , returnImplicationWeakenByLHS, returnImplicationsWeakenByLHS
  , returnVars, returnIndices
  -- Sub-tuples
  , SubTupR(..), subTupR, subTupRpair, subTupUnit, subTupPreserves, subTupDistribute
  , DeclareSubVars(..), declareSubVars, DeclareMissingVars(..), declareMissingVars
  , DeclareMissingDistributedVars(..), declareMissingDistributedVars
  -- TRANSFORMATION
  -- Main types
  , LVAnalysis(..), LVAnalysisFun(..), LVAnalysis'(..)
  -- Index transformation
  , ReEnv(..), reEnvIdx, reEnvIndices, reEnvIndices', reEnvVar, reEnvVars
  -- Bindings
  , bind, BindLiveness(..), bindSub, BindLivenessSub(..)
  -- Utilities
  , allDead, expectJust
  , subTupExp, subTupFun
  , composeSubTupR, subTup, subTupDBuf
  ) where

import Data.Maybe (fromMaybe, mapMaybe, isNothing)
import Control.DeepSeq (NFData (rnf))
import Data.Type.Equality

import Data.Array.Accelerate.AST.Idx
import Data.Array.Accelerate.AST.IdxSet ( IdxSet(..) )
import Data.Array.Accelerate.AST.Var
import Data.Array.Accelerate.AST.LeftHandSide
import qualified Data.Array.Accelerate.AST.IdxSet as IdxSet
import Data.Array.Accelerate.AST.Environment
import Data.Array.Accelerate.AST.Exp
import Data.Array.Accelerate.Representation.Type
import Data.Array.Accelerate.Array.Buffer
import Data.Array.Accelerate.Trafo.Var
import Data.Array.Accelerate.Trafo.Exp.Substitution
import Data.Array.Accelerate.Trafo.Substitution
import Data.Array.Accelerate.Error

-- ANALYSIS

-- During the analysis, a variable is either known to be live, or unknown
-- whether it is live or dead. In the last case, we store two sets:
-- * 'implies': the set of variables that are live if this variable appears to be live
-- * 'implied-by': if any implied-by variable is live, then this variable is live
--
-- Note that type argument 't' is not used, but it is needed to give Liveness
-- the correct kind to be used in 'Env', as defined in 'LivenessEnv'.
data Liveness env t where
  Live :: Liveness env t

  -- Not sure if this is live, but if it is then the given set of indices is also live,
  -- i.e. the liveness of this variable implies the liveness of others.
  Unknown
    :: IdxSet env -- implies
    -> IdxSet env -- implied by
    -> Liveness env t

dead :: Liveness env t
dead = Unknown IdxSet.empty IdxSet.empty

data LivenessEnv env where
  LEmpty :: LivenessEnv ()
  LPush
    :: LivenessEnv env
    -> Liveness env t
    -> LivenessEnv (env, t)

emptyLivenessEnv :: LivenessEnv ()
emptyLivenessEnv = LEmpty

lEnvPush :: LivenessEnv env -> LivenessEnv (env, t)
lEnvPush env = LPush env dead

lEnvPushLHS :: LeftHandSide s t env1 env2 -> LivenessEnv env1 -> LivenessEnv env2
lEnvPushLHS (LeftHandSideSingle _)       env = lEnvPush env
lEnvPushLHS (LeftHandSideWildcard _)     env = env
lEnvPushLHS (LeftHandSidePair lhs1 lhs2) env = lEnvPushLHS lhs2 $ lEnvPushLHS lhs1 env

-- If idx1 is live, then idx2 is live
addLiveImplies :: Idx env s -> Idx env t -> LivenessEnv env -> LivenessEnv env
addLiveImplies = \idx1 idx2 env -> fromMaybe (setLive idx2 env) $ go idx1 idx2 env
  where
    go :: Idx env s -> Idx env t -> LivenessEnv env -> Maybe (LivenessEnv env)
    go ZeroIdx ZeroIdx env = Just env -- Trivial constraint, always satisfied
    go (SuccIdx idx1) (SuccIdx idx2) (LPush env l) = (`LPush` l) <$> go idx1 idx2 env
    go ZeroIdx (SuccIdx idx) (LPush env l) = case l of
      Live -> Nothing
      Unknown implies impliedBy ->
        Just $ LPush env $ Unknown (IdxSet.insert idx implies) impliedBy
    go (SuccIdx idx) ZeroIdx (LPush env l)
      | isLive idx env = Nothing
      | otherwise = case l of
          Live -> Just $ LPush env Live
          Unknown implies impliedBy ->
            Just $ LPush env $ Unknown implies $ IdxSet.insert idx impliedBy

-- If any of impliedBy becomes live, then implies are live.
addLiveImplications :: IdxSet env -> IdxSet env -> LivenessEnv env -> LivenessEnv env
addLiveImplications impliedBy implies env
  | anyIsLive impliedBy env
  = setIdxSetLive implies env
  | otherwise
  = addLiveImplicationsCurrentlyUnknown impliedBy implies env

-- If any of impliedBy becomes live, then implies are live.
-- Assumes that all indices in impliedBy are currently Unknown.
addLiveImplicationsCurrentlyUnknown :: IdxSet env -> IdxSet env -> LivenessEnv env -> LivenessEnv env
-- Base case / Early out
addLiveImplicationsCurrentlyUnknown (IdxSet PEnd) _ env = env
addLiveImplicationsCurrentlyUnknown _ (IdxSet PEnd) env = env
-- Recursive
addLiveImplicationsCurrentlyUnknown impliedBy implies (LPush env l) = LPush (addLiveImplicationsCurrentlyUnknown (IdxSet.drop impliedBy) (IdxSet.drop implies) env) l'
  where
    l' = case l of
      Unknown implies' impliedBy' ->
        Unknown
          (if ZeroIdx `IdxSet.member` impliedBy
            then IdxSet.drop implies `IdxSet.union` implies'
            else implies')
          (if ZeroIdx `IdxSet.member` implies
            then IdxSet.drop impliedBy `IdxSet.union` impliedBy'
            else impliedBy')
      Live 
        | ZeroIdx `IdxSet.member` impliedBy -> error "`Unknown` may not point to an already live variable"
        | otherwise -> Live

setLive :: Idx env s -> LivenessEnv env -> LivenessEnv env
setLive = \idx env -> uncurry setIdxSetLive $ go idx env
  where
    go :: Idx env s -> LivenessEnv env -> (IdxSet env, LivenessEnv env)
    go (SuccIdx idx) (LPush env l) = case l of
      Live -> (IdxSet.skip newSet, LPush env' Live)
      Unknown implies impliedBy
        | idx `IdxSet.member` impliedBy ->
          -- This variable may be present in the implied-by set of other variables,
          -- hence we need to add it to the IdxSet and potentially mark other variables
          -- live in the next iteration of setIdxSetLive.
          (IdxSet.push $ implies `IdxSet.union` newSet, LPush env' Live)
        | otherwise ->
          (IdxSet.skip $ newSet, LPush env' $ Unknown (IdxSet.remove idx implies) impliedBy)
      where
        (newSet, env') = go idx env
    go ZeroIdx (LPush env l) = case l of
      Live -> (IdxSet.empty, LPush env Live)
      Unknown implies _ -> (IdxSet.skip implies, LPush env Live)

setIdxSetLive :: IdxSet env -> LivenessEnv env -> LivenessEnv env
setIdxSetLive = \set env ->
  if IdxSet.null set then env else uncurry setIdxSetLive $ go set env
  where
    go :: IdxSet env -> LivenessEnv env -> (IdxSet env, LivenessEnv env)
    go (IdxSet PEnd) env = (IdxSet.empty, env)
    go liveSet (LPush env l) = case l of
      Live -> (IdxSet.skip newSet, LPush env' Live)
      Unknown implies impliedBy
        -- Does this variable become live?
        | ZeroIdx `IdxSet.member` liveSet || IdxSet.overlaps tailLiveSet impliedBy ->
          -- This variable may be present in the implied-by set of other variables,
          -- hence we need to add it to the IdxSet and potentially mark other variables
          -- live in the next iteration of setIdxSetLive.
          (IdxSet.push $ implies `IdxSet.union` newSet, LPush env' Live)
        | otherwise ->
          (IdxSet.skip newSet, LPush env' $ Unknown (implies IdxSet.\\ tailLiveSet) impliedBy)
      where
        tailLiveSet = IdxSet.drop liveSet
        (newSet, env') = go tailLiveSet env

setVarsLive :: Vars s env t -> LivenessEnv env -> LivenessEnv env
setVarsLive = setIdxSetLive . IdxSet.fromVars

isLive :: Idx env t -> LivenessEnv env -> Bool
isLive (SuccIdx idx) (LPush env _) = isLive idx env
isLive ZeroIdx       (LPush _   l) = case l of
  Live -> True
  _ -> False

anyIsLive :: IdxSet env -> LivenessEnv env -> Bool
anyIsLive (IdxSet PEnd) _ = False
anyIsLive indices (LPush _ Live)
  | ZeroIdx `IdxSet.member` indices = True
anyIsLive indices (LPush env _) = anyIsLive (IdxSet.drop indices) env

-- Drops one entry of the liveness env.
-- Propagates the constraints imposed by the first entry on the remaining entries in the environment.
-- Returns Nothing if this variable is definitely live, or Just impliedBy if it is only live if one of the indices in impliedBy is live.
lEnvStrengthen :: LivenessEnv (env1, t) -> (Maybe (IdxSet env1), LivenessEnv env1)
lEnvStrengthen = \case
  LPush env Live -> (Nothing, env)
  LPush env (Unknown implies impliedBy) -> (Just impliedBy, addLiveImplicationsCurrentlyUnknown impliedBy implies env)

-- Extension of LeftHandSide
-- Data structure to remember data between a call to 'lEnvStrengthenLHS' and 'bind'
data LHSLiveness s t env1 env2 where
  LHSLivenessSingle
    :: Maybe (IdxSet env1) -- Nothing if it is definitely live, or Just impliedBy if it is only live if one of the indices in impliedBy is live.
    -> s t
    -> LHSLiveness s t env1 (env1, t)
  LHSLivenessWildcard
    :: TupR s t
    -> LHSLiveness s t env1 env1
  LHSLivenessPair
    :: LHSLiveness s t1       env1 env2
    -> LHSLiveness s t2       env2 env3
    -> LHSLiveness s (t1, t2) env1 env3

lEnvStrengthenLHS :: LeftHandSide s t env1 env2 -> LivenessEnv env2 -> (LHSLiveness s t env1 env2, LivenessEnv env1)
lEnvStrengthenLHS lhs env = case lhs of
  LeftHandSideWildcard tp -> (LHSLivenessWildcard tp, env)
  LeftHandSideSingle tp
    | (m, env') <- lEnvStrengthen env
    -> (LHSLivenessSingle m tp, env')
  LeftHandSidePair lhs1 lhs2
    | (lhs2', env')  <- lEnvStrengthenLHS lhs2 env
    , (lhs1', env'') <- lEnvStrengthenLHS lhs1 env'
    -> (LHSLivenessPair lhs1' lhs2', env'')

lEnvStrengthenLHSReturn :: LeftHandSide s t env1 env2 -> LivenessEnv env2 -> (LHSLiveness s t env1 env2, LivenessEnv env1, ReturnImplications env1 t)
lEnvStrengthenLHSReturn lhs env = case lhs of
  LeftHandSideWildcard tp -> (LHSLivenessWildcard tp, env, mapTupR (const returnImplicationDead) tp)
  LeftHandSideSingle tp
    | (m, env') <- lEnvStrengthen env
    -> (LHSLivenessSingle m tp, env', TupRsingle $ maybe ReturnLive ReturnImpliedBy m)
  LeftHandSidePair lhs1 lhs2
    | (lhs2', env',  r2) <- lEnvStrengthenLHSReturn lhs2 env
    , (lhs1', env'', r1) <- lEnvStrengthenLHSReturn lhs1 env'
    -> (LHSLivenessPair lhs1' lhs2', env'', TupRpair r1 (mapTupR (returnImplicationStrengthenByLHS lhs1') r2))

-- ANALYSIS for languages with a return value

data ReturnImplication env t
  -- If any of the variables in the set is live,
  -- then the returned value is live.
  = ReturnImpliedBy (IdxSet env)
  -- This return value is always live
  | ReturnLive
type ReturnImplications env = TupR (ReturnImplication env)

returnImplicationsLive :: ReturnImplications env t
returnImplicationsLive = TupRsingle ReturnLive

flattenReturnImplications :: ReturnImplications env t -> ReturnImplication env t
flattenReturnImplications TupRunit = returnImplicationDead
flattenReturnImplications (TupRsingle ret) = ret
flattenReturnImplications (TupRpair r1 r2) = case (flattenReturnImplications r1, flattenReturnImplications r2) of
  (ReturnLive, _) -> ReturnLive
  (_, ReturnLive) -> ReturnLive
  (ReturnImpliedBy a, ReturnImpliedBy b) -> ReturnImpliedBy $ IdxSet.union a b

returnImplicationDead :: ReturnImplication env t
returnImplicationDead = ReturnImpliedBy IdxSet.empty

returnImplicationStrengthenByLHS :: LHSLiveness s t env1 env2 -> ReturnImplication env2 u -> ReturnImplication env1 u
returnImplicationStrengthenByLHS _ ReturnLive = ReturnLive
returnImplicationStrengthenByLHS lhs' (ReturnImpliedBy impliedBy1) = go lhs' impliedBy1
  where
    go :: LHSLiveness s' t' env1 env2 -> IdxSet env2 -> ReturnImplication env1 t
    go (LHSLivenessSingle m _) impliedBy
      | ZeroIdx `IdxSet.member` impliedBy =
        case m of 
          Nothing -> ReturnLive
          Just impliedBy' -> ReturnImpliedBy $ IdxSet.drop impliedBy `IdxSet.union` impliedBy'
      | otherwise = ReturnImpliedBy $ IdxSet.drop impliedBy
    go (LHSLivenessWildcard _) impliedBy = ReturnImpliedBy impliedBy
    go (LHSLivenessPair lhs1 lhs2) impliedBy = case go lhs2 impliedBy of
      ReturnLive -> ReturnLive
      ReturnImpliedBy i -> go lhs1 i

returnImplicationWeakenByLHS :: LeftHandSide s t env1 env2 -> ReturnImplication env1 u -> ReturnImplication env2 u
returnImplicationWeakenByLHS _ ReturnLive = ReturnLive
returnImplicationWeakenByLHS l (ReturnImpliedBy impliedBy) = ReturnImpliedBy $ IdxSet.skip' l impliedBy

returnImplicationsWeakenByLHS :: LeftHandSide s t env1 env2 -> ReturnImplications env1 u -> ReturnImplications env2 u
returnImplicationsWeakenByLHS lhs = mapTupR (returnImplicationWeakenByLHS lhs)

returnVars :: Distributes s => ReturnImplications env t -> Vars s env t -> LivenessEnv env -> LivenessEnv env
returnVars (TupRsingle ReturnLive) vars = setVarsLive vars
returnVars (TupRsingle (ReturnImpliedBy impliedBy)) vars = addLiveImplications impliedBy $ IdxSet.fromVars vars
returnVars TupRunit TupRunit = id
returnVars (TupRpair r1 r2) (TupRpair v1 v2) = returnVars r1 v1 . returnVars r2 v2
returnVars TupRunit (TupRsingle tp) = unitImpossible tp
returnVars TupRpair{} (TupRsingle tp) = pairImpossible tp

returnIndices :: ReturnImplications env t -> IdxSet env -> LivenessEnv env -> LivenessEnv env
returnIndices ret indices = case flattenReturnImplications ret of
  ReturnLive -> setIdxSetLive indices
  ReturnImpliedBy impliedBy -> addLiveImplications impliedBy indices

data SubTupR t t' where
  SubTupRskip :: SubTupR t ()

  SubTupRkeep :: SubTupR t t

  SubTupRpair :: SubTupR t1 t1'
              -> SubTupR t2 t2'
              -> SubTupR (t1, t2) (t1', t2')

instance NFData (SubTupR t t') where
  rnf SubTupRskip = ()
  rnf SubTupRkeep = ()
  rnf (SubTupRpair s1 s2) = rnf s1 `seq` rnf s2

composeSubTupR :: SubTupR b c -> SubTupR a b -> SubTupR a c
composeSubTupR bc SubTupRkeep = bc
composeSubTupR SubTupRkeep ab = ab
composeSubTupR SubTupRskip SubTupRskip = SubTupRskip
composeSubTupR SubTupRskip _ = SubTupRskip
composeSubTupR (SubTupRpair bc bc') (SubTupRpair ab ab') = subTupRpair (composeSubTupR bc ab) (composeSubTupR bc' ab')

subTupRpair :: SubTupR t1 t1'  -> SubTupR t2 t2' -> SubTupR (t1, t2) (t1', t2')
subTupRpair SubTupRkeep SubTupRkeep = SubTupRkeep
subTupRpair s t = SubTupRpair s t

subTupR :: SubTupR t t' -> TupR s t -> TupR s t'
subTupR SubTupRskip         _                = TupRunit
subTupR SubTupRkeep         t                = t
subTupR (SubTupRpair s1 s2) (TupRpair t1 t2) = subTupR s1 t1 `TupRpair` subTupR s2 t2
subTupR _                   _                = internalError "Tuple mismatch"

subTup :: SubTupR t t' -> t -> t'
subTup SubTupRskip _ = ()
subTup SubTupRkeep t = t
subTup (SubTupRpair l r) (t1, t2) = (subTup l t1, subTup r t2)

subTupUnit :: SubTupR () t' -> t' :~: ()
subTupUnit SubTupRskip = Refl
subTupUnit SubTupRkeep = Refl

-- Checks whether the SubTup preserves the entire tuple.
-- This function needs a 'TupR s t' to check whether 'SubTupRskip' is used on
-- '()'. On a unit, SubTupRskip and SubTupRkeep have the same meaning.
--
subTupPreserves :: TupR s t -> SubTupR t t' -> Maybe (t' :~: t)
subTupPreserves TupRunit s = Just $ subTupUnit s
subTupPreserves (TupRpair t1 t2) (SubTupRpair s1 s2)
  | Just Refl <- subTupPreserves t1 s1
  , Just Refl <- subTupPreserves t2 s2 = Just Refl
subTupPreserves _ _ = Nothing

-- 's' is ambiguous, so explicit type annotation is needed.
subTupDistribute :: forall s t t'. SubTupR t t' -> SubTupR (Distribute s t) (Distribute s t')
subTupDistribute SubTupRskip = SubTupRskip
subTupDistribute SubTupRkeep = SubTupRkeep
subTupDistribute (SubTupRpair s1 s2) = subTupDistribute @s s1 `SubTupRpair` subTupDistribute @s s2

-- TRANSFORMATION

data ReEnv env subenv where
  ReEnvEnd  :: ReEnv () ()
  ReEnvSkip :: ReEnv env subenv -> ReEnv (env, t) subenv
  ReEnvKeep :: ReEnv env subenv -> ReEnv (env, t) (subenv, t)

reEnvIdx :: ReEnv env subenv -> env :?> subenv
reEnvIdx (ReEnvKeep _) ZeroIdx      = Just ZeroIdx
reEnvIdx (ReEnvKeep r) (SuccIdx ix) = SuccIdx <$> reEnvIdx r ix
reEnvIdx (ReEnvSkip r) (SuccIdx ix) = reEnvIdx r ix
reEnvIdx _             _            = Nothing

reEnvIndices :: ReEnv env subenv -> [Exists (Idx env)] -> [Exists (Idx subenv)]
reEnvIndices re = mapMaybe $ \(Exists idx) -> Exists <$> reEnvIdx re idx

reEnvIndices' :: ReEnv env subenv -> [Idx env t] -> [Idx subenv t]
reEnvIndices' re = mapMaybe $ reEnvIdx re

reEnvVar :: ReEnv env subenv -> Var s env t -> Maybe (Var s subenv t)
reEnvVar re (Var tp idx) = Var tp <$> reEnvIdx re idx

reEnvVars :: ReEnv env subenv -> Vars s env t -> Maybe (Vars s subenv t)
reEnvVars re = traverseTupR $ reEnvVar re

-- Fuse with lEnvStrengthenLHS (to be implemented) or let lEnvStrengthenLHS return its intermediate values in some data structure
-- Is that data structure just something like (TupR Liveness), but then with some fixes for proper environment?
bind :: LHSLiveness s t env env' -> ReEnv env subenv -> BindLiveness s t env' subenv
bind lhs re = case lhs of
  LHSLivenessSingle mImplied tp
    -- Was this variable already known to be live (mImplied == Nothing),
    -- or is one of the implied-by variables live (mImplied == Just implied && check re implied)?
    | maybe True (isImpliedLive re) mImplied ->
      BindLiveness (LeftHandSideSingle tp) $ ReEnvKeep re
    | otherwise ->
      BindLiveness (LeftHandSideWildcard $ TupRsingle tp) $ ReEnvSkip re
  LHSLivenessWildcard tp ->
    BindLiveness (LeftHandSideWildcard tp) re
  LHSLivenessPair lhs1 lhs2
    | BindLiveness lhs1' re1 <- bind lhs1 re
    , BindLiveness lhs2' re2 <- bind lhs2 re1
    -> BindLiveness (leftHandSidePair lhs1' lhs2') re2

-- Given an implied-by set, checks if the variabble is live according to the ReEnv.
-- That is, it checks if one of the indices in the IdxSet is live in ReEnv.
isImpliedLive :: ReEnv env1 subenv1 -> IdxSet env1 -> Bool
isImpliedLive _ (IdxSet PEnd) = False
isImpliedLive (ReEnvKeep env) impliedBy
  | ZeroIdx `IdxSet.member` impliedBy = True -- One of the members of impliedBy is live
  | otherwise = isImpliedLive env $ IdxSet.drop impliedBy
isImpliedLive (ReEnvSkip env) impliedBy = isImpliedLive env $ IdxSet.drop impliedBy

-- Captures the existentional subenv'
data BindLiveness s t env' subenv where
  BindLiveness
    :: LeftHandSide s t subenv subenv'
    -> ReEnv env' subenv'
    -> BindLiveness s t env' subenv

bindSub :: LHSLiveness s t env env' -> ReEnv env subenv -> BindLivenessSub s t env' subenv
bindSub lhs re = case lhs of
  LHSLivenessSingle mImplied tp
    -- Was this variable already known to be live (mImplied == Nothing),
    -- or is one of the implied-by variables live (mImplied == Just implied && check re implied)?
    | maybe True (isImpliedLive re) mImplied ->
      BindLivenessSub
        SubTupRkeep
        (LeftHandSideSingle tp)
        (LeftHandSideSingle tp)
        (ReEnvKeep re)
    | otherwise ->
      BindLivenessSub
        SubTupRskip
        (LeftHandSideWildcard $ TupRsingle tp)
        (LeftHandSideWildcard TupRunit)
        (ReEnvSkip re)
  LHSLivenessWildcard tp ->
    BindLivenessSub
      SubTupRskip
      (LeftHandSideWildcard tp)
      (LeftHandSideWildcard TupRunit)
      re
  LHSLivenessPair lhs1 lhs2
    | BindLivenessSub subTup1 lhs1Full lhs1Sub re1 <- bindSub lhs1 re
    , BindLivenessSub subTup2 lhs2Full lhs2Sub re2 <- bindSub lhs2 re1
    -> if
        | LeftHandSideWildcard _ <- lhs1Sub
        , LeftHandSideWildcard _ <- lhs2Sub ->
          BindLivenessSub
            SubTupRskip
            (leftHandSidePair lhs1Full lhs2Full)
            (LeftHandSideWildcard TupRunit)
            re2

        | SubTupRkeep <- subTup1
        , SubTupRkeep <- subTup2
        , lhs' <- leftHandSidePair lhs1Full lhs2Full ->
          BindLivenessSub
            SubTupRkeep
            lhs'
            lhs'
            re2

        | otherwise ->
          BindLivenessSub
            (SubTupRpair subTup1 subTup2)
            (leftHandSidePair lhs1Full lhs2Full)
            (leftHandSidePair lhs1Sub lhs2Sub)
            re2

-- Captures the existentionals subenv' and t'
data BindLivenessSub s t env' subenv where
  BindLivenessSub
    :: SubTupR t t'
    -> LeftHandSide s t  subenv subenv'
    -> LeftHandSide s t' subenv subenv'
    -> ReEnv env' subenv'
    -> BindLivenessSub s t env' subenv

-- For an IR parameterized over the result type, implement a function of this
-- type:
--
-- stronglyLiveVariables :: LivenessEnv env -> ReturnImplications env t -> SomeAcc env t -> LVAnalysis SomeAcc env t
--
-- If the IR does have a result type, but we cannot change that type, then use:
--
-- stronglyLiveVariables :: LivenessEnv env -> ReturnImplications env t -> SomeAcc env t -> LVAnalysisFun SomeAcc env t
--
-- For an IR which is not parameterized over the result type, but only over the
-- environment, implement a function of this type:
--
-- stronglyLiveVariables :: LivenessEnv env -> SomeAcc env -> LVAnalysis' SomeAcc env

-- If this part of the returned value is returned, then this set of variables is live
data LVAnalysis ir env t where
  LVAnalysis
    :: LivenessEnv env
    -- Depending on the binding, it may or may not be possible to restrict the
    -- term to only the used parts of the tuple.
    -> (forall subenv t'. ReEnv env subenv -> SubTupR t t' -> Either (ir subenv t) (ir subenv t'))
    -> LVAnalysis ir env t

data LVAnalysisFun ir env t where
  LVAnalysisFun
    :: LivenessEnv env
    -> (forall subenv. ReEnv env subenv -> ir subenv t)
    -> LVAnalysisFun ir env t

data LVAnalysis' ir env where
  LVAnalysis'
    :: LivenessEnv env
    -> (forall subenv. ReEnv env subenv -> ir subenv)
    -> LVAnalysis' ir env

allDead :: ReEnv env subenv -> IdxSet env -> Bool
allDead re set = all (\(Exists idx) -> isNothing $ reEnvIdx re idx) $ IdxSet.toList set

expectJust :: HasCallStack => Maybe a -> a
expectJust (Just a) = a
expectJust Nothing  = internalError "Substitution in live variable analysis failed. A variable which was assumed to be dead appeared to be live."

-- Utilities for expressions
subTupExp :: IsArrayInstr arr => SubTupR t t' -> PreOpenExp arr env t -> PreOpenExp arr env t'
subTupExp SubTupRkeep expr = expr
subTupExp SubTupRskip _    = Nil
subTupExp s      expr
  | DeclareSubVars lhs _ vars <- declareSubVars (expType expr) s
  = Let lhs expr $ expVars $ vars weakenId

subTupFun :: IsArrayInstr arr => SubTupR t t' -> PreOpenFun arr env (s -> t) -> PreOpenFun arr env (s -> t')
subTupFun s (Lam lhs (Body body)) = Lam lhs $ Body $ subTupExp s body
subTupFun _ _ = internalError "Expected unary function"

subTupDBuf :: SubTupR t t' -> TupR s (Distribute Buffer t) -> TupR s (Distribute Buffer t')
subTupDBuf SubTupRskip         _                = TupRunit
subTupDBuf SubTupRkeep         t                = t
subTupDBuf (SubTupRpair s1 s2) (TupRpair t1 t2) = subTupDBuf s1 t1 `TupRpair` subTupDBuf s2 t2
subTupDBuf _                   _                = internalError "Tuple mismatch"

data DeclareSubVars s t t' env where
  DeclareSubVars :: LeftHandSide s t env env'
                 -> (env :> env')
                 -> (forall env''. env' :> env'' -> Vars s env'' t')
                 -> DeclareSubVars s t t' env

declareSubVars :: TupR s t -> SubTupR t t' -> DeclareSubVars s t t' env
declareSubVars tp SubTupRkeep
  | DeclareVars lhs k vars <- declareVars tp = DeclareSubVars lhs k vars
declareSubVars tp SubTupRskip
  = DeclareSubVars (LeftHandSideWildcard tp) weakenId (const TupRunit)
declareSubVars (TupRpair t1 t2) (SubTupRpair s1 s2)
  | DeclareSubVars lhs1 subst1 a1 <- declareSubVars t1 s1
  , DeclareSubVars lhs2 subst2 a2 <- declareSubVars t2 s2
  = DeclareSubVars (LeftHandSidePair lhs1 lhs2) (subst2 .> subst1) $ \k -> a1 (k .> subst2) `TupRpair` a2 k
declareSubVars _ _ = internalError "Tuple mismatch"

data DeclareMissingVars s t t' env where
  -- Captures existentials env' and t''.
  DeclareMissingVars :: LeftHandSide s t'' env env'
                     -> (env :> env')
                     -> (forall env''. env' :> env'' -> Vars s env'' t)
                     -> DeclareMissingVars s t t' env

declareMissingVars :: TupR s t -> SubTupR t t' -> Vars s env t' -> DeclareMissingVars s t t' env
declareMissingVars _  SubTupRkeep vars = DeclareMissingVars (LeftHandSideWildcard TupRunit) weakenId (\k -> mapTupR (weaken k) vars)
declareMissingVars tp SubTupRskip _
  | DeclareVars lhs k value <- declareVars tp
  = DeclareMissingVars lhs k value
declareMissingVars (TupRpair t1 t2) (SubTupRpair s1 s2) (TupRpair v1 v2)
  | DeclareMissingVars lhs1 subst1 value1 <- declareMissingVars t1 s1 v1
  , DeclareMissingVars lhs2 subst2 value2 <- declareMissingVars t2 s2 (mapTupR (weaken subst1) v2)
  = DeclareMissingVars (LeftHandSidePair lhs1 lhs2) (subst2 .> subst1) $ \k -> value1 (k .> subst2) `TupRpair` value2 k
declareMissingVars _ _ _ = internalError "Tuple mismatch"

data DeclareMissingDistributedVars f s' s t t' env where
  -- Captures existentials env' and t''.
  DeclareMissingDistributedVars
    :: TupR s' t''
    -> LeftHandSide s (Distribute f t'') env env'
    -> (env :> env')
    -> (forall env''. env' :> env'' -> Vars s env'' (Distribute f t))
    -> DeclareMissingDistributedVars f s' s t t' env

-- 'f' is ambiguous
declareMissingDistributedVars
  :: forall f s' s t t' env.
     TupR s' t -> TupR s (Distribute f t) -> SubTupR t t' -> Vars s env (Distribute f t') -> DeclareMissingDistributedVars f s' s t t' env
declareMissingDistributedVars _ _ SubTupRkeep vars
  = DeclareMissingDistributedVars TupRunit (LeftHandSideWildcard TupRunit) weakenId (\k -> mapTupR (weaken k) vars)
declareMissingDistributedVars tp tp' SubTupRskip _
  | DeclareVars lhs k value <- declareVars tp'
  = DeclareMissingDistributedVars tp lhs k value
declareMissingDistributedVars (TupRpair t1 t2) (TupRpair t1' t2') (SubTupRpair s1 s2) (TupRpair v1 v2)
  | DeclareMissingDistributedVars st1 lhs1 subst1 value1 <- declareMissingDistributedVars @f t1 t1' s1 v1
  , DeclareMissingDistributedVars st2 lhs2 subst2 value2 <- declareMissingDistributedVars @f t2 t2' s2 (mapTupR (weaken subst1) v2)
  = DeclareMissingDistributedVars (TupRpair st1 st2) (LeftHandSidePair lhs1 lhs2) (subst2 .> subst1) $ \k -> value1 (k .> subst2) `TupRpair` value2 k
declareMissingDistributedVars _ _ _ _ = internalError "Tuple mismatch"
