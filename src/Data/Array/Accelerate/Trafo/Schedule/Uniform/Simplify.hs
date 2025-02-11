{-# LANGUAGE ConstraintKinds     #-}
{-# LANGUAGE EmptyCase           #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE MultiWayIf          #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE PatternGuards       #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TupleSections       #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE TypeOperators       #-}
{-# LANGUAGE ViewPatterns        #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# OPTIONS_HADDOCK hide #-}
-- |
-- Module      : Data.Array.Accelerate.Trafo.Schedule.Uniform.Simplify
-- Copyright   : [2012..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.Trafo.Schedule.Uniform.Simplify (
  -- Construction DSL
  BuildSchedule, BuildScheduleFun, funConstruct,
  buildAcond, buildAwhile, buildEffect, buildSpawn,
  buildLet, buildReturn, buildSeq,
  buildFunBody, buildFunLam,
  BuildEnv(BEmpty),

  lhsSignal, lhsRef,

  -- Optimize
  simplify
) where

import Data.Array.Accelerate.AST.Environment
import Data.Array.Accelerate.AST.Idx
import Data.Array.Accelerate.AST.LeftHandSide
import Data.Array.Accelerate.AST.Schedule.Uniform
import Data.Array.Accelerate.Analysis.Match
import Data.Array.Accelerate.Error
import Data.Array.Accelerate.Representation.Type
import Data.Array.Accelerate.Trafo.Exp.Substitution
import Data.Array.Accelerate.Trafo.Substitution             hiding ( weakenArrayInstr )
import Data.Array.Accelerate.Trafo.Schedule.Uniform.Substitution ()
import Data.Array.Accelerate.Trafo.SkipEnvironment (Skip'(..), skipWeakenIdx')
import Data.Maybe
import Data.List
    ( isSubsequenceOf,
      sort )

-- TODO: Move fork combining and/or InfoEnv into this utility?
data BuildSchedule kernel env =
  BuildSchedule{
    -- Sorted, without duplicates
    directlyAwaits :: [Idx env Signal],
    -- The SignalResolvers that this term resolves at the end of its execution.
    -- 'End' here is the place where the Continuation would be placed
    -- (as 'end' is otherwise ambiguous if the term has Spawns).
    -- Sorted, without duplicates
    finallyResolves :: [Idx env SignalResolver],
    trivial :: Bool,
    -- How deep Awhile(Seq)s are nested within this term
    awhileHeight :: Int,
    -- Constructs a schedule, but doesn't wait on the directlyAwaits signals.
    -- constructFull adds that.
    construct
      :: forall env'.
         env :> env'
      -> BuildEnv env'
      -> Postponed kernel env'
      -> Continuation kernel env'
      -> UniformSchedule kernel env'
  }

instance Sink' (BuildSchedule kernel) where
  weaken' k schedule =
    BuildSchedule{
      directlyAwaits = sort $ map (weaken k) $ directlyAwaits schedule,
      finallyResolves = sort $ map (weaken k) $ finallyResolves schedule,
      trivial = trivial schedule,
      awhileHeight = awhileHeight schedule,
      construct = \k' -> construct schedule (k' .> k)
    }

data BuildScheduleFun kernel env t where
  BuildBody
    :: BuildSchedule kernel env
    -> BuildScheduleFun kernel env ()

  BuildLam
    :: BLeftHandSide t env env'
    -> BuildScheduleFun kernel env' f
    -> BuildScheduleFun kernel env (t -> f)

funConstruct :: BuildScheduleFun kernel env t -> env :> env' -> BuildEnv env' -> UniformScheduleFun kernel env' t
funConstruct (BuildBody body) k env = Sbody $ constructFull body k env nothingPostponed ContinuationEnd
funConstruct (BuildLam lhs f) k env
  | Exists lhs' <- rebuildLHS lhs
  = Slam lhs' $ funConstruct f (sinkWithLHS lhs lhs' k) $ buildEnvSkip lhs' env

funAwhileHeight :: BuildScheduleFun kernel env t -> Int
funAwhileHeight (BuildBody b) = awhileHeight b
funAwhileHeight (BuildLam _ f) = funAwhileHeight f

funDirectlyAwaits :: BuildScheduleFun kernel env t -> [Idx env Signal]
funDirectlyAwaits (BuildBody b) = directlyAwaits b
funDirectlyAwaits (BuildLam lhs f) = mapMaybe (strengthenWithLHS lhs) $ funDirectlyAwaits f

instance Sink (BuildScheduleFun kernel) where
  weaken k (BuildBody body) = BuildBody $ weaken' k body
  weaken k (BuildLam lhs f)
    | Exists lhs' <- rebuildLHS lhs
    = BuildLam lhs' $ weaken (sinkWithLHS lhs lhs' k) f

data BuildSpawn kernel env =
  BuildSpawn{
    -- The signals that this term resolves at the end.
    -- Corresponds with finallyResolves, but the SignalResolvers are converted to Signals.
    spawnFinallyResolves :: [Idx env Signal],
    spawnTerm :: BuildSchedule kernel env
  }

instance Sink' (BuildSpawn kernel) where
  weaken' k (BuildSpawn signals schedule) = BuildSpawn (map (weaken k) signals) (weaken' k schedule)

data Postponed kernel env = Postponed
  [BuildSpawn kernel env] -- The terms that should be spawned before doing serious work, in reverse order
  [Idx env SignalResolver] -- The SignalResolvers that should be resolved before doing serious work

nothingPostponed :: Postponed kernel env
nothingPostponed = Postponed [] []

instance Sink' (Postponed kernel) where
  weaken' k (Postponed spawns resolvers) = Postponed
    (map (weaken' k) spawns)
    (map (weaken k) resolvers)

-- Constructs a schedule, and waits on the directlyAwaits signals.
constructFull
  :: BuildSchedule kernel env
  -> env :> env'
  -> BuildEnv env'
  -> Postponed kernel env'
  -> Continuation kernel env'
  -> UniformSchedule kernel env'
constructFull schedule k env postponed cont
  | null $ directlyAwaits schedule = construct schedule k env postponed cont
  | signals' <-
    -- Don't wait on already resolved signals
    sortedDedup
      $ sort
      $ filter (\idx -> not (isResolved idx env))
      $ map (weaken k)
      $ directlyAwaits schedule
  , env' <- markResolved signals' env =
    if null signals' then
      construct schedule k env' postponed cont
    else
      case findDependingSpawn postponed signals' of
        Nothing ->
          placePostponed postponed env
            $ Effect (SignalAwait signals')
            $ construct schedule k env' nothingPostponed cont
        Just (BuildSpawn _ prepend, postponed') ->
          constructFull prepend weakenId env postponed' $ ContinuationDo k schedule weakenId cont

placePostponed :: Postponed kernel env -> BuildEnv env -> UniformSchedule kernel env -> UniformSchedule kernel env
placePostponed (Postponed spawns resolvers) env next = 
  foldl
    (\other (BuildSpawn _ term) -> spawnAndRotate (constructFull term weakenId env nothingPostponed ContinuationEnd) other)
    next'
    spawns
  where
    next'
      | [] <- resolvers = next
      | otherwise = Effect (SignalResolve resolvers) next

spawnAndRotate :: UniformSchedule kernel env -> UniformSchedule kernel env -> UniformSchedule kernel env
spawnAndRotate (Spawn a b) c = Spawn a $ spawnAndRotate b c
spawnAndRotate a Return = a
spawnAndRotate a (Effect eff@(SignalResolve _) Return) = Effect eff $ a
spawnAndRotate a b = Spawn a b

resolveSignalsInPostponed :: [Idx env Signal] -> [Idx env SignalResolver] -> Postponed kernel env -> Postponed kernel env
resolveSignalsInPostponed signals newResolvers (Postponed spawns resolvers) = Postponed
  (map (\(BuildSpawn r s) -> BuildSpawn r s{ directlyAwaits = filter (`notElem` signals) $ directlyAwaits s }) spawns)
  (newResolvers ++ resolvers)

spawnPostponed :: forall kernel env. BuildSpawn kernel env -> Postponed kernel env -> Postponed kernel env
spawnPostponed spawn (Postponed spawns resolvers)
  | Just spawns' <- tryCombine spawns = Postponed spawns' resolvers
  | otherwise = Postponed (spawn : spawns) resolvers
  where
    -- Tries to combine 'spawn' with a BuildSpawn in spawns.
    tryCombine :: [BuildSpawn kernel env] -> Maybe [BuildSpawn kernel env]
    tryCombine [] = Nothing -- It wasn't possible to combine it.
    tryCombine (x:xs)
      -- If 'spawn' waits on a result of 'x'
      | shouldCombine x spawn
      = Just $ combine x spawn : xs

      -- If 'x' waits on a result of 'spawn'
      | shouldCombine spawn x
      = Just $ combine spawn x : xs

      | otherwise
      = (x:) <$> tryCombine xs

    shouldCombine :: BuildSpawn kernel env -> BuildSpawn kernel env -> Bool
    shouldCombine before after
      -- If 'after' waits on a result of 'before'
      = not (null $ spawnFinallyResolves before `sortedIntersection` directlyAwaits (spawnTerm after))
      -- If 'before' is trivial and does not wait on other signals than 'after'
      || trivial (spawnTerm before) && directlyAwaits (spawnTerm before) `isSubsequenceOf` directlyAwaits (spawnTerm after)

    combine :: BuildSpawn kernel env -> BuildSpawn kernel env -> BuildSpawn kernel env
    combine first second = BuildSpawn
      (spawnFinallyResolves first)
      (buildSeq (spawnTerm first) (buildSpawnReturn $ spawnTerm second))

-- Finds a spawned term, on which the next term (given by the directly-awaits
-- list) directly depends on.
findDependingSpawn :: forall kernel env. Postponed kernel env -> [Idx env Signal] -> Maybe (BuildSpawn kernel env, Postponed kernel env)
findDependingSpawn (Postponed spawns resolvers) nextDirectlyAwaits = case go spawns of
  Just (y, ys) -> Just (y, Postponed ys resolvers)
  Nothing -> Nothing
  where
    go :: [BuildSpawn kernel env] -> Maybe (BuildSpawn kernel env, [BuildSpawn kernel env])
    go (x:xs)
      | not $ null $ spawnFinallyResolves x `sortedIntersection` nextDirectlyAwaits
        = Just (x, xs)
      | otherwise = case go xs of
        Nothing -> Nothing
        Just (y, ys) -> Just (y, x:ys)
    go [] = Nothing

data BuildEnv env where
  BEmpty :: BuildEnv ()
  BPush  :: BuildEnv env -> BuildEnvInfo env t -> BuildEnv (env, t)

data BuildEnvInfo env t where
  -- No information available.
  INone
    :: BuildEnvInfo env t

  -- This SignalResolver resolves the Signal at the next index in the environment.
  IResolvesNext
    :: BuildEnvInfo (env, Signal) SignalResolver

  -- This Signal is resolved.
  IResolved
    :: BuildEnvInfo env Signal
  
  -- This OutputRef writes to the Ref at the next index in the environment.
  IWritesNext
    :: BuildEnvInfo (env, Ref t) (OutputRef t)
  
  -- This Ref contains the value of the specified variable.
  IRefContains
    :: Idx env t
    -> BuildEnvInfo env (Ref t)

  -- This variable has the value of the given Refs.
  -- Only for Buffer and Scalar variables.
  IValue
    :: [Idx env (Ref t)]
    -> BuildEnvInfo env t

data BuildEnvPrj t where
  BuildEnvPrj :: BuildEnvInfo env t -> BuildEnvPrj t

buildEnvPrj :: Idx env t -> BuildEnv env -> BuildEnvPrj t
buildEnvPrj ZeroIdx       (BPush _   v) = BuildEnvPrj v
buildEnvPrj (SuccIdx idx) (BPush env _) = buildEnvPrj idx env

data BuildEnvPrj' env t where
  BuildEnvPrj' :: Skip env env' -> BuildEnvInfo env' t -> BuildEnvPrj' env t

buildEnvPrj' :: Idx env t -> BuildEnv env -> BuildEnvPrj' env t
buildEnvPrj' = go SkipNone
  where
    go :: Skip env env' -> Idx env' t -> BuildEnv env' -> BuildEnvPrj' env t
    go skip ZeroIdx       (BPush _   v) = BuildEnvPrj' (SkipSucc skip) v
    go skip (SuccIdx idx) (BPush env _) = go (SkipSucc skip) idx env

findSignal :: Idx env SignalResolver -> BuildEnv env -> Maybe (Idx env Signal)
findSignal idx env = case buildEnvPrj' idx env of
  BuildEnvPrj' skip IResolvesNext -> Just $ weaken (skipWeakenIdx skip) ZeroIdx
  _ -> Nothing

findRef :: Idx env (OutputRef t) -> BuildEnv env -> Maybe (Idx env (Ref t))
findRef idx env = case buildEnvPrj' idx env of
  BuildEnvPrj' skip IWritesNext -> Just $ weaken (skipWeakenIdx skip) ZeroIdx
  _ -> Nothing

-- Given a sorted list of unique signals, marks those signals as resolved in the BuildEnv.
markResolved :: [Idx env Signal] -> BuildEnv env -> BuildEnv env
markResolved [] env = env
markResolved signals (BPush env info)
  | ZeroIdx : signals' <- signals
    = BPush (markResolved (map unSucc signals') env) IResolved
  | otherwise
    = BPush (markResolved (map unSucc signals) env) info
  where
    unSucc :: Idx (env, t) s -> Idx env s
    unSucc ZeroIdx = internalError "markResolved: input was not sorted or contains duplicates"
    unSucc (SuccIdx idx) = idx
markResolved (s:_) BEmpty = case s of {}

isResolved :: Idx env Signal -> BuildEnv env -> Bool
isResolved signal env
  | BuildEnvPrj IResolved <- buildEnvPrj signal env = True
  | otherwise = False

markRefValue :: Idx env (Ref t) -> Idx env t -> BuildEnv env -> BuildEnv env
markRefValue (SuccIdx refIdx) (SuccIdx valueIdx) (BPush env info) = BPush (markRefValue refIdx valueIdx env) info
markRefValue ZeroIdx (SuccIdx valueIdx) (BPush env _) = BPush env (IRefContains valueIdx)
markRefValue (SuccIdx refIdx) ZeroIdx (BPush env info) = BPush env $ case info of
  INone
    -> IValue [refIdx]
  IValue refs
    -> IValue (refIdx : refs)
  _ -> info

-- Finds the value of a reference, if available
findRefValue :: Idx env (Ref t) -> BuildEnv env -> Maybe (Idx env t)
findRefValue = go SkipNone
  where
    go :: Skip env env' -> Idx env' (Ref t) -> BuildEnv env' -> Maybe (Idx env t)
    go skip ZeroIdx (BPush _ info) = case info of
      IRefContains value -> Just $ weaken (skipWeakenIdx $ SkipSucc skip) value
      _ -> Nothing
    go skip (SuccIdx refIdx) (BPush env info)
      | IValue refs <- info
      , Refl : _ <- mapMaybe (matchIdx refIdx) refs = Just $ weaken (skipWeakenIdx skip) ZeroIdx
      | otherwise = go (SkipSucc skip) refIdx env

data Continuation kernel env where
  ContinuationEnd
    :: Continuation kernel env

  ContinuationDo
    :: env1 :> env
    -> BuildSchedule kernel env1
    -> env2 :> env
    -> Continuation kernel env2
    -> Continuation kernel env

instance Sink' (Continuation kernel) where
  weaken' _ ContinuationEnd = ContinuationEnd
  weaken' k1 (ContinuationDo k2 b k3 c) = ContinuationDo (k1 .> k2) b (k1 .> k3) c

buildReturn :: BuildSchedule kernel env
buildReturn = BuildSchedule{
    directlyAwaits = [],
    finallyResolves = [],
    trivial = True,
    awhileHeight = 0,
    construct = \_ env postponed -> \case
      ContinuationEnd -> placePostponed postponed env Return
      ContinuationDo k2 build k3 cont -> constructFull build k2 env postponed $ weaken' k3 cont
  }

buildLet
  :: forall kernel t env1 env2.
     BLeftHandSide t env1 env2
  -> Binding env1 t
  -> BuildSchedule kernel env2
  -> BuildSchedule kernel env1
buildLet lhs binding body
  | trivialBinding binding =
    BuildSchedule{
      directlyAwaits = map (fromMaybe (internalError "Illegal schedule: deadlock") . strengthenWithLHS lhs) $ directlyAwaits body,
      finallyResolves = mapMaybe (strengthenWithLHS lhs) $ finallyResolves body,
      trivial = trivial body,
      awhileHeight = awhileHeight body,
      construct = constructLet False
    }
  | otherwise =
    BuildSchedule{
      directlyAwaits = [],
      finallyResolves = mapMaybe (strengthenWithLHS lhs) $ finallyResolves body,
      trivial = False,
      awhileHeight = awhileHeight body,
      construct = constructLet True
    }
  where
    constructLet
      :: Bool
      -> env1 :> env1'
      -> BuildEnv env1'
      -> Postponed kernel env1'
      -> Continuation kernel env1'
      -> UniformSchedule kernel env1'
    constructLet shouldAwait k env postponed cont
      -- Eliminate this let-binding, if it reads from a Ref, and we already know the value of that Ref.
      | RefRead refVar <- binding
      , Just valueIdx <- findRefValue (weaken k $ varIdx refVar) env
      , LeftHandSideSingle _ <- lhs =
        -- Note that RefRead is a trivial binding, so shouldAwait is False
        construct body (weakenReplace valueIdx k) env postponed cont
      | Exists lhs' <- rebuildLHS lhs
      , k' <- sinkWithLHS lhs lhs' k
      , binding' <- weaken k binding =
        placePostponed (if shouldAwait then postponed else nothingPostponed) env
          $ Alet lhs' binding'
          $ constructFull (if shouldAwait then body else body{ directlyAwaits = [] }) k'
            (buildEnvExtend lhs' binding' env)
            (if shouldAwait then nothingPostponed else weaken' (weakenWithLHS lhs') postponed)
          $ weaken' (weakenWithLHS lhs') cont

buildLetNewSignal :: String -> [Idx env SignalResolver] -> BuildSchedule kernel ((env, Signal), SignalResolver) -> BuildSchedule kernel env
buildLetNewSignal comment resolvers body =
  -- NewSignal is trivial
  BuildSchedule{
    directlyAwaits = map (fromMaybe (internalError "Illegal schedule: deadlock") . strengthenWithLHS lhs) $ directlyAwaits body,
    finallyResolves = mapMaybe (strengthenWithLHS lhs) $ finallyResolves body,
    trivial = trivial body,
    awhileHeight = awhileHeight body,
    construct = \k env postponed cont -> if
      | otherSignal : _ <- mapMaybe (\idx -> k >:> idx `findSignal` env) resolvers
      , k' <- sink $ weakenReplace otherSignal k ->
        -- Remove the index for the signal.
        -- Replace all occurrences of that signal with 'otherSignal',
        -- as their resolvers are resolved at the same time.
        Alet lhsResolver (NewSignal comment)
          $ construct body k'
            (buildEnvExtend lhsResolver (NewSignal comment) env)
            (weaken' (weakenSucc weakenId) postponed)
          $ weaken' (weakenSucc weakenId) cont
      | k' <- sink $ sink k ->
        Alet lhs (NewSignal comment)
          $ construct body k'
            (buildEnvExtend lhs (NewSignal comment) env)
            (weaken' (weakenSucc $ weakenSucc weakenId) postponed)
          $ weaken' (weakenSucc $ weakenSucc weakenId) cont
  }
  where
    lhs = LeftHandSideSingle BaseRsignal `LeftHandSidePair` LeftHandSideSingle BaseRsignalResolver
    lhsResolver = LeftHandSideWildcard (TupRsingle BaseRsignal) `LeftHandSidePair` LeftHandSideSingle BaseRsignalResolver

buildEnvExtend :: BLeftHandSide t env1 env2 -> Binding env1 t -> BuildEnv env1 -> BuildEnv env2
buildEnvExtend (LeftHandSidePair (LeftHandSideSingle _) (LeftHandSideSingle _)) (NewSignal _) env =
  env `BPush` INone `BPush` IResolvesNext
buildEnvExtend (LeftHandSidePair (LeftHandSideSingle _) (LeftHandSideSingle _)) (NewRef _) env =
  env `BPush` INone `BPush` IWritesNext
buildEnvExtend (LeftHandSideSingle _) (RefRead refVar) env = env `BPush` IValue [varIdx refVar]
buildEnvExtend lhs _ env = buildEnvSkip lhs env

buildEnvSkip :: BLeftHandSide t env1 env2 -> BuildEnv env1 -> BuildEnv env2
buildEnvSkip lhs env = case lhs of
  LeftHandSideWildcard _ -> env
  LeftHandSideSingle _
    -> env `BPush` INone
  LeftHandSidePair lhs1 lhs2
    -> buildEnvSkip lhs2 $ buildEnvSkip lhs1 $ env

buildEffect
  :: forall kernel env.
     Effect kernel env
  -> BuildSchedule kernel env
  -> BuildSchedule kernel env
buildEffect (SignalResolve []) next = next
buildEffect (SignalResolve resolvers) next =
  BuildSchedule{
    directlyAwaits = [],
    finallyResolves =
      if trivial next && null (directlyAwaits next) then
        resolvers' `mergeDedup` finallyResolves next
      else
        finallyResolves next,
    trivial = trivial next && null (directlyAwaits next),
    awhileHeight = awhileHeight next,
    construct = \k env postponed cont ->
      let
        resolvers'' = map (weaken k) resolvers'
        signals = sort $ mapMaybe (\r -> findSignal r env) resolvers''
        env' = markResolved signals env
      in
        constructFull next k env' (resolveSignalsInPostponed signals resolvers'' postponed) cont
  }
  where
    resolvers' = sort resolvers
buildEffect (SignalAwait signals) next =
  BuildSchedule{
    directlyAwaits = sort signals `mergeDedup` directlyAwaits next,
    finallyResolves = finallyResolves next,
    trivial = trivial next,
    awhileHeight = awhileHeight next,
    construct = \k env postponed cont -> construct next k env postponed cont
  }
buildEffect effect next
  | canPostpone =
    BuildSchedule{
      directlyAwaits = directlyAwaits next,
      finallyResolves = finallyResolves next,
      trivial = effectIsTrivial && trivial next,
      awhileHeight = awhileHeight next,
      construct = \k env postponed cont ->
        Effect (weaken' k effect)
          $ construct next k (updateEnv k env) postponed cont
    }
  | otherwise =
    BuildSchedule{
      directlyAwaits = [],
      finallyResolves = finallyResolves next,
      trivial = effectIsTrivial && trivial next,
      awhileHeight = awhileHeight next,
      construct = \k env postponed cont ->
        placePostponed (if effectIsTrivial then nothingPostponed else postponed) env
          $ Effect (weaken' k effect)
          $ constructFull next k (updateEnv k env) (if effectIsTrivial then postponed else nothingPostponed) cont
    }
  where
    effectIsTrivial = trivialEffect effect
    -- Write may be postponed: a write doesn't do synchronisation,
    -- that is done by a signal(resolver).
    canPostpone
      | RefWrite{} <- effect = True
      | otherwise = False
    updateEnv :: env :> env' -> BuildEnv env' -> BuildEnv env'
    updateEnv k env = case effect of
      RefWrite outRefVar valueVar 
        | Just refIdx <- findRef (k >:> varIdx outRefVar) env
          -> markRefValue refIdx (k >:> varIdx valueVar) env
      _ -> env

buildSeq :: BuildSchedule kernel env -> BuildSchedule kernel env -> BuildSchedule kernel env
buildSeq a b =
  BuildSchedule {
    directlyAwaits = directlyAwaits a,
    finallyResolves =
      if trivial b && isSubseq then
        finallyResolves a `mergeDedup` finallyResolves b
      else
        finallyResolves b,
    trivial = trivial a && trivial b && isSubseq,
    awhileHeight = awhileHeight a `max` awhileHeight b,
    construct = \k env postponed cont ->
      construct a k env postponed $ ContinuationDo k b weakenId cont
  }
  where
    isSubseq = directlyAwaits b `isSubsequenceOf` directlyAwaits a

buildSpawn :: BuildSchedule kernel env -> BuildSchedule kernel env -> BuildSchedule kernel env
buildSpawn a b
  | trivial a && directlyAwaits a `isSubsequenceOf` directlyAwaits b =
    buildSeq a b
  | trivial b && directlyAwaits b `isSubsequenceOf` directlyAwaits a =
    buildSeq b a
  | otherwise =
    BuildSchedule{
      directlyAwaits = directlyAwaits a `sortedIntersection` directlyAwaits b,
      -- Only return the resolved signals at the place where the continuation is placed.
      -- We thus ignore 'a' here.
      finallyResolves = finallyResolves b,
      -- TODO: Make trivial if 'b' is trivial?
      -- Might be a problem if the then later on (in construct) make the Spawn sequential (the true case in the if below).
      -- We could perhaps add a condition to not make the Spawn sequential if 'b' is trivial and there is some continuation,
      -- but that might still be fragile.
      trivial = False,
      awhileHeight = awhileHeight a `max` awhileHeight b,
      construct = \k env postponed cont ->
        let
          aResolves = sort $ mapMaybe ((`findSignal` env) . weaken k) $ finallyResolves a
          a' = a{directlyAwaits = directlyAwaits a `sortedMinus` directlyAwaits b}
          b' = b{directlyAwaits = directlyAwaits b `sortedMinus` directlyAwaits a}
        in
          if not $ null (aResolves `sortedIntersection` map (weaken k) (directlyAwaits b)) then
            constructFull a' k env postponed $ ContinuationDo k b' weakenId cont
          else
            constructFull b' k env (spawnPostponed (BuildSpawn aResolves $ weaken' k a') postponed) cont
    }

-- Builds a term of the form 'Spawn a Return'.
-- This is a separate function from buildSpawn, as 'buildSpawn a Return' will be simplified to 'a'.
-- This is sometimes not desired, like in spawnPostponed,
-- where we must have term 'a' be spawned, to set things like 'finallyResolves' without taking 'a' into account.
-- It must also guarantee that the continuation is placed in parallel with 'a', instead of after 'a'.
-- 'buildSpawn a Return' fails to provide that.
buildSpawnReturn :: BuildSchedule kernel env -> BuildSchedule kernel env
buildSpawnReturn a =
  BuildSchedule{
    directlyAwaits = [],
    finallyResolves = [],
    trivial = True,
    awhileHeight = awhileHeight a,
    construct = \k env postponed cont ->
      let
        aResolves = sort $ mapMaybe ((`findSignal` env) . weaken k) $ finallyResolves a
      in
        constructFull buildReturn k env (spawnPostponed (BuildSpawn aResolves $ weaken' k a) postponed) cont
  }

buildAcond
  :: ExpVar env PrimBool
  -> BuildSchedule kernel env -- True branch
  -> BuildSchedule kernel env -- False branch
  -> BuildSchedule kernel env -- Operations after the if-then-else
  -> BuildSchedule kernel env
buildAcond var true false next =
  BuildSchedule{
    directlyAwaits = directlyAwaits true `sortedIntersection` directlyAwaits false,
    finallyResolves = finallyResolves next,
    trivial = False,
    awhileHeight = awhileHeight true `max` awhileHeight false `max` awhileHeight next,
    construct = \k env postponed cont ->
      placePostponed postponed env
        $ Acond
          (weaken k var)
          (constructFull  true{directlyAwaits = directlyAwaits true `sortedMinus` directlyAwaits false} k env nothingPostponed ContinuationEnd)
          (constructFull false{directlyAwaits = directlyAwaits false `sortedMinus` directlyAwaits true} k env nothingPostponed ContinuationEnd)
          (constructFull next k env nothingPostponed cont)
  }

buildAwhile
  :: InputOutputR input output
  -> BuildScheduleFun kernel env (input -> Output PrimBool -> output -> ())
  -> BaseVars env input
  -> BuildSchedule kernel env -- Operations after the while loop
  -> BuildSchedule kernel env
buildAwhile io step initial next =
  BuildSchedule{
    -- TODO: Also check if the function directly awaits parts of the input, and take the accompanying signals from 'initial'
    directlyAwaits = funDirectlyAwaits step,
    finallyResolves = finallyResolves next,
    trivial = False,
    awhileHeight = (funAwhileHeight step + 1) `max` awhileHeight next,
    construct = \k env postponed cont ->
      placePostponed postponed env
        -- If a this awhile contains another awhile, downgrade this awhile to an awhile-seq.
        -- Nested awhiles would exponentially blow up the memory required to
        -- store the space of this program.
        $ if funAwhileHeight step > 0 then
            let
              env' = env `BPush` IResolved `BPush` INone
              k' = weakenSucc' $ weakenSucc' k
              step' = downgradeAwhileFun (SuccIdx ZeroIdx) $ weaken k' step
            in
              await (weaken k <$> varsGetSignals initial)
                $ Alet lhsSignal (NewSignal "Signal for awhile to awhile-seq downgrade")
                $ Effect (SignalResolve [ZeroIdx])
                $ AwhileSeq
                  (ioRemoveSignal io)
                  (funConstruct step' weakenId env')
                  (mapTupR (weaken k') $ varsRemoveSignal initial)
                  (constructFull next k' env' nothingPostponed $ weaken' (weakenSucc $ weakenSucc weakenId) cont)
          else
            Awhile
              io
              (funConstruct step k env)
              (mapTupR (weaken k) initial)
              (constructFull next k env nothingPostponed cont)
  }

buildAwhileSeq
  -- Should not contain InputOutputRsignal
  :: InputOutputR input output
  -> BuildScheduleFun kernel env (input -> OutputRef PrimBool -> output -> ())
  -> BaseVars env input
  -> BuildSchedule kernel env -- Operations after the while loop
  -> BuildSchedule kernel env
buildAwhileSeq io step initial next =
  BuildSchedule{
    directlyAwaits = funDirectlyAwaits step,
    finallyResolves = finallyResolves next,
    trivial = False,
    awhileHeight = (funAwhileHeight step + 1) `max` awhileHeight next,
    construct = \k env postponed cont ->
      placePostponed postponed env
        $ AwhileSeq
          io
          (funConstruct step k env)
          (mapTupR (weaken k) initial)
          (constructFull next k env nothingPostponed cont)
  }

downgradeAwhileFun
  :: forall kernel env input output.
     Idx env Signal -- Index to a resolved signal
  -> BuildScheduleFun kernel env (input -> (SignalResolver, OutputRef PrimBool) -> output -> ())
  -> BuildScheduleFun kernel env (NoSignal input -> OutputRef PrimBool -> NoSignal output -> ())
downgradeAwhileFun signalIdx (BuildLam lhsInput (BuildLam lhsBool (BuildLam lhsOutput (BuildBody f))))
  | Exists lhsInput' <- lhsRemoveSignal lhsInput
  , kInput <- declareRemovedSignal lhsInput lhsInput' signalIdx weakenId
  , Exists lhsBoolOutput' <- lhsRemoveSignal (LeftHandSidePair lhsBool lhsOutput)
  , DeclareRemovedResolvers termOutput kOutput <-
      declareRemovedResolvers @kernel
        (LeftHandSidePair lhsBool lhsOutput)
        lhsBoolOutput'
        kInput
  , LeftHandSidePair lhsBool' lhsOutput' <- lhsBoolOutput'
  = BuildLam lhsInput'
  $ BuildLam (lhsSnd lhsBool')
  $ BuildLam lhsOutput'
  $ BuildBody
  $ termOutput
  $ weaken' kOutput f
  where
    lhsSnd :: BLeftHandSide ((), b) e1 e2 -> BLeftHandSide b e1 e2
    lhsSnd (LeftHandSidePair LeftHandSideWildcard{} l) = l
    lhsSnd (LeftHandSideWildcard (TupRpair _ t)) = LeftHandSideWildcard t
    lhsSnd _ = internalError "Pair impossible"
downgradeAwhileFun _ _ = internalError "Fun impossible"

buildFunLam
  :: BLeftHandSide t env1 env2
  -> BuildScheduleFun kernel env2 f
  -> BuildScheduleFun kernel env1 (t -> f)
buildFunLam = BuildLam

buildFunBody :: BuildSchedule kernel env -> BuildScheduleFun kernel env ()
buildFunBody = BuildBody

lhsSignal :: BLeftHandSide (Signal, SignalResolver) fenv ((fenv, Signal), SignalResolver)
lhsSignal = LeftHandSidePair (LeftHandSideSingle BaseRsignal) (LeftHandSideSingle BaseRsignalResolver)

lhsRef :: GroundR tp -> LeftHandSide BaseR (Ref tp, OutputRef tp) fenv ((fenv, Ref tp), OutputRef tp)
lhsRef tp = LeftHandSidePair (LeftHandSideSingle $ BaseRref tp) (LeftHandSideSingle $ BaseRrefWrite tp)

-- Assumes that the input arrays are sorted,
-- with no duplicates.
-- Creates a sorted list containing all elements of the two input list.
-- If an element is present in both input lists, it will be added only
-- once to the output.
mergeDedup :: Ord a => [a] -> [a] -> [a]
mergeDedup as@(a:as') bs@(b:bs')
  | a == b    = a : mergeDedup as' bs'
  | a <  b    = a : mergeDedup as' bs
  | otherwise = b : mergeDedup as  bs'
mergeDedup as [] = as
mergeDedup [] bs = bs

sortedDedup :: Eq a => [a] -> [a]
sortedDedup = \case
  [] -> []
  a : as -> go a as
  where
    go x (y:ys)
      | x == y = go x ys
      | otherwise = x : go y ys
    go x [] = [x]

-- Constructs the intersection of two lists,
-- assuming they are sorted and have no duplicates.
sortedIntersection :: Ord a => [a] -> [a] -> [a]
sortedIntersection as@(a:as') bs@(b:bs')
  | a == b    = a : sortedIntersection as' bs'
  | a <  b    = sortedIntersection as' bs
  | otherwise = sortedIntersection as  bs'
sortedIntersection _ _ = []

-- Constructs the difference of two lists,
-- assuming they are sorted and have no duplicates.
-- It returns all elements present in the first list,
-- but not in the second
sortedMinus :: Ord a => [a] -> [a] -> [a]
sortedMinus as@(a:as') bs@(b:bs')
  | a == b    = sortedMinus as' bs'
  | a <  b    = a : sortedMinus as' bs
  | otherwise = sortedMinus as  bs'
sortedMinus as [] = as
sortedMinus [] _  = []

-- Simplify schedule, by rebuilding it using the build functions
simplify :: UniformScheduleFun kernel () t -> UniformScheduleFun kernel () t
simplify f = funConstruct (rebuildFun f) weakenId BEmpty

rebuildFun :: UniformScheduleFun kernel env t -> BuildScheduleFun kernel env t
rebuildFun (Slam lhs f) = buildFunLam lhs $ rebuildFun f
rebuildFun (Sbody body) = buildFunBody $ snd $ rebuild body

rebuild :: UniformSchedule kernel env -> (SignalAnalysis env, BuildSchedule kernel env)
rebuild = \case
  Return -> (SEmpty, buildReturn)
  Alet lhs bnd body
    | (analysis, body') <- rebuild body ->
      ( analysisDrop lhs analysis
      , rebuildLet lhs bnd analysis body'
      )
  Effect eff next
    | (analysis, next') <- rebuild next ->
      ( analyseEffect eff `analysisJoin` analysis
      , buildEffect eff next'
      )
  Acond var true false next
    | (aTrue, true') <- rebuild true
    , (aFalse, false') <- rebuild false
    , (aNext, next') <- rebuild next ->
      ( analysisMeet aTrue aFalse `analysisJoin` aNext
      , buildAcond var true' false' next'
      )
  Awhile io f input next
    | (analysis, next') <- rebuild next ->
      ( analysis
      , buildAwhile io (rebuildFun f) input next'
      )
  AwhileSeq io f input next
    | (analysis, next') <- rebuild next ->
      ( analysis
      , buildAwhileSeq io (rebuildFun f) input next'
      )
  Spawn term1 term2
    | (analysis1, term1') <- rebuild term1
    , (analysis2, term2') <- rebuild term2 ->
      ( analysisJoin analysis1 analysis2
      , buildSpawn term1' term2'
      )

rebuildLet
  :: BLeftHandSide t env env'
  -> Binding env t
  -> SignalAnalysis env'
  -> BuildSchedule kernel env'
  -> BuildSchedule kernel env
rebuildLet (LeftHandSidePair LeftHandSideSingle{} LeftHandSideSingle{}) (NewSignal comment) (SPush _ (SIResolvedWith resolvers)) body = buildLetNewSignal comment (map unSucc resolvers) body
  where
    unSucc :: Idx (env, Signal) SignalResolver -> Idx env SignalResolver
    unSucc (SuccIdx idx) = idx
rebuildLet lhs bnd _ body = buildLet lhs bnd body

-- Signal analysis
data SignalAnalysis env where
  SEmpty :: SignalAnalysis env
  SPush  :: SignalAnalysis env -> SignalInfo env t -> SignalAnalysis (env, t)

spush :: SignalAnalysis env -> SignalInfo env t -> SignalAnalysis (env, t)
spush SEmpty SINone = SEmpty
spush env info = SPush env info

data SignalInfo env t where
  -- This SignalResolver is resolved at the same time as the given list of SignalResolvers.
  SIResolvedWith
    :: [Idx env SignalResolver]
    -> SignalInfo env SignalResolver

  SINone
    :: SignalInfo env t

analysisDrop :: LeftHandSide s t env env' -> SignalAnalysis env' -> SignalAnalysis env
analysisDrop _ SEmpty = SEmpty
analysisDrop LeftHandSideWildcard{} env = env
analysisDrop LeftHandSideSingle{} (SPush env _) = env
analysisDrop (LeftHandSidePair lhs1 lhs2) env = analysisDrop lhs1 $ analysisDrop lhs2 env

-- Use this when two terms are both executed, for instance in a spawn
analysisJoin :: SignalAnalysis env -> SignalAnalysis env -> SignalAnalysis env
analysisJoin SEmpty env = env
analysisJoin env SEmpty = env
analysisJoin (SPush as a) (SPush bs b) = analysisJoin as bs `SPush` signalInfoJoin a b

signalInfoJoin :: SignalInfo env t -> SignalInfo env t -> SignalInfo env t
signalInfoJoin SINone info = info
signalInfoJoin info SINone = info
signalInfoJoin (SIResolvedWith as) (SIResolvedWith bs) = SIResolvedWith $ as `mergeDedup` bs

-- Use this when only one of the two terms is executed, for instance in an if-then-else
analysisMeet :: SignalAnalysis env -> SignalAnalysis env -> SignalAnalysis env
analysisMeet SEmpty _ = SEmpty
analysisMeet _ SEmpty = SEmpty
analysisMeet (SPush as a) (SPush bs b) = analysisMeet as bs `SPush` signalInfoMeet a b

signalInfoMeet :: SignalInfo env t -> SignalInfo env t -> SignalInfo env t
signalInfoMeet SINone _ = SINone
signalInfoMeet _ SINone = SINone
signalInfoMeet (SIResolvedWith as) (SIResolvedWith bs) = SIResolvedWith $ as `sortedIntersection` bs

analyseEffect :: Effect kernel env -> SignalAnalysis env
analyseEffect (SignalResolve resolvers) = analyseSignalResolve resolvers
analyseEffect _ = SEmpty

analyseSignalResolve :: [Idx env SignalResolver] -> SignalAnalysis env
analyseSignalResolve = const SEmpty -- go . sort
  where
    -- input is sorted from low indices to high indices
    go :: [Idx env SignalResolver] -> SignalAnalysis env
    go [] = SEmpty
    go [_] = SEmpty
    go (ZeroIdx : ids) = go ids' `SPush` SIResolvedWith ids'
      where ids' = map unSucc ids
    go ids@(SuccIdx _ : _) = go (map unSucc ids) `spush` SINone

    unSucc :: Idx (env, s) t -> Idx env t
    unSucc (SuccIdx idx) = idx
    unSucc ZeroIdx = internalError "Expected non-zero index. Is the list of indices sorted and unique?"

-- Removes Signals from the InputOutputR of an awhile loop
ioRemoveSignal :: InputOutputR input output -> InputOutputR (NoSignal input) (NoSignal output)
ioRemoveSignal InputOutputRsignal = InputOutputRunit
ioRemoveSignal (InputOutputRref tp) = InputOutputRref tp
ioRemoveSignal InputOutputRunit = InputOutputRunit
ioRemoveSignal (InputOutputRpair a b) = ioRemoveSignal a `InputOutputRpair` ioRemoveSignal b

typeRemoveSignal :: BasesR input -> BasesR (NoSignal input)
typeRemoveSignal TupRunit = TupRunit
typeRemoveSignal (TupRsingle t) = case t of
  BaseRsignal -> TupRunit
  BaseRsignalResolver -> TupRunit
  BaseRref _ -> TupRsingle t
  BaseRrefWrite _ -> TupRsingle t
  _ -> internalError "Only expected Signals, SignalResolvers, and Refs"
typeRemoveSignal (TupRpair t1 t2) = typeRemoveSignal t1 `TupRpair` typeRemoveSignal t2

lhsRemoveSignal :: BLeftHandSide input env1 env2 -> Exists (BLeftHandSide (NoSignal input) env3)
lhsRemoveSignal (LeftHandSideWildcard tp) = Exists $ LeftHandSideWildcard $ typeRemoveSignal tp
lhsRemoveSignal (LeftHandSideSingle tp) = case tp of
  BaseRsignal -> Exists $ LeftHandSideWildcard TupRunit
  BaseRsignalResolver -> Exists $ LeftHandSideWildcard TupRunit
  BaseRref _ -> Exists $ LeftHandSideSingle tp
  BaseRrefWrite _ -> Exists $ LeftHandSideSingle tp
  _ -> internalError "Only expected Signals, SignalResolvers, and Refs"
lhsRemoveSignal (LeftHandSidePair lhs1 lhs2)
  | Exists lhs1' <- lhsRemoveSignal lhs1
  , Exists lhs2' <- lhsRemoveSignal lhs2
  = Exists $ LeftHandSidePair lhs1' lhs2'

varsRemoveSignal :: BaseVars env input -> BaseVars env (NoSignal input)
varsRemoveSignal TupRunit = TupRunit
varsRemoveSignal vars@(TupRsingle (Var t _)) = case t of
  BaseRsignal -> TupRunit
  BaseRsignalResolver -> TupRunit
  BaseRref _ -> vars
  BaseRrefWrite _ -> vars
  _ -> internalError "Only expected Signals, SignalResolvers, and Refs"
varsRemoveSignal (TupRpair v1 v2) = varsRemoveSignal v1 `TupRpair` varsRemoveSignal v2

varsGetSignals :: BaseVars env input -> [Idx env Signal]
varsGetSignals (TupRsingle (Var BaseRsignal idx)) = [idx]
varsGetSignals (TupRpair v1 v2) = varsGetSignals v1 ++ varsGetSignals v2
varsGetSignals _ = [] -- TupRunit or TupRsingle of a different type

type family NoSignal input where
  NoSignal Signal = ()
  NoSignal SignalResolver = ()
  NoSignal (a, b) = (NoSignal a, NoSignal b)
  NoSignal input = input

-- Substitutes the uses of a removed Signal variable to a newly introduced
-- Signal, that is directly resolved.
-- This is needed for converting an awhile to an awhile-seq.
-- Only call this function on the input of the body of an awhile loop.
-- This function expects that the left hand side only binds Refs and Signals.
-- Furthermore, it expects that 'Exists lhsNew = lhsRemoveSignal lhsOld'.
-- The newly introduced Signal (and SignalResolver) should eventually be
-- removed. The Signal is directly resolved, and our optimizer will thus
-- remove SignalAwaits waiting on that signal. This will make the variables
-- dead, and strongly live variable analysis will then remove it.
-- We go via this indirection, since BuildSchedule cannot remove variables;
-- it can only rename variables.
declareRemovedSignal
  :: forall env0 env1 env1' env2' t.
     BLeftHandSide t env0 env1
  -> BLeftHandSide (NoSignal t) env0 env1'
  -> Idx env0 Signal -- Index of a resolved signal
  -> env1' :> env2'
  -> env1 :> env2'
declareRemovedSignal lhsOld lhsNew signalIdx k =
  go lhsOld lhsNew k (k .> weakenWithLHS lhsNew)
  where
    go
      :: BLeftHandSide s envA envB
      -> BLeftHandSide (NoSignal s) envA' envB'
      -> envB' :> env2'
      -> envA :> env2'
      -> envB :> env2'
    -- A preserved variable.
    go (LeftHandSideSingle t) (LeftHandSideSingle _) kB' kA = case t of
      BaseRref _ -> weakenReplace (weaken kB' ZeroIdx) kA
      _ -> internalError "Signal impossible, other types not expected"
    -- A removed Signal. Use the newly introduced signal instead.
    go (LeftHandSideSingle BaseRsignal) (LeftHandSideWildcard _) _ kA =
      weakenReplace (weaken (k .> weakenWithLHS lhsNew) signalIdx) kA
    go (LeftHandSidePair old1 old2) (LeftHandSidePair new1 new2) kB' kA =
      go old2 new2 kB' $ go old1 new1 (kB' .> weakenWithLHS new2) kA
    go (LeftHandSideWildcard _) (LeftHandSideWildcard _) _ kA = kA
    go _ _ _ _ = internalError "LeftHandSide mismatch"

-- Similar to declareRemovedSignal, but
-- 1. This function is about removed SignalResolvers.
-- 2. This function operates on the output and thus expects OutputRefs instead of Refs
-- 3. Instead of defining one SignalResolver and using that for each removed variable,
--    we must now define one SignalResolver per variable.
declareRemovedResolvers
  :: forall kernel env0 env0' env1 env1' t.
     BLeftHandSide t env0 env1
  -> BLeftHandSide (NoSignal t) env0' env1'
  -> env0 :> env0'
  -> DeclareRemovedResolvers kernel env1 env1'
declareRemovedResolvers lhsOld lhsNew k =
  bindResolvers removed $ \skip term resolvers ->
    DeclareRemovedResolvers
      term
      $ snd $ go resolvers lhsOld lhsNew
        (skipWeakenIdx' skip)
        (skipWeakenIdx' skip .> weakenWithLHS lhsNew .> k)
  where
    removed = lhsSize lhsOld - lhsSize lhsNew

    bindResolvers
      :: Int
      -> (forall env2'.
          Skip' env2' env1'
          -> (BuildSchedule kernel env2' -> BuildSchedule kernel env1')
          -> [Idx env2' SignalResolver]
          -> DeclareRemovedResolvers kernel env1 env1')
      -> DeclareRemovedResolvers kernel env1 env1'
    bindResolvers 0 f = f SkipNone' id []
    bindResolvers n f = bindResolvers (n - 1) $ \skip term resolvers ->
      f
        (SkipSucc' skip)
        (term . buildLet lhsOnlyResolver (NewSignal "SignalResolver for awhile to awhile-seq downgrade"))
        (ZeroIdx : map SuccIdx resolvers)
      where
        lhsOnlyResolver :: BLeftHandSide (Signal, SignalResolver) e (e, SignalResolver)
        lhsOnlyResolver = LeftHandSideWildcard (TupRsingle BaseRsignal) `LeftHandSidePair` LeftHandSideSingle BaseRsignalResolver

    go
      :: [Idx env2' SignalResolver]
      -> BLeftHandSide s envA envB
      -> BLeftHandSide (NoSignal s) envA' envB'
      -> envB' :> env2'
      -> envA :> env2'
      -> ([Idx env2' SignalResolver], envB :> env2')
    go resolvers (LeftHandSideSingle t) (LeftHandSideSingle _) kB' kA = case t of
      BaseRrefWrite _ -> (resolvers, weakenReplace (weaken kB' ZeroIdx) kA)
      _ -> internalError "SignalResolver impossible, other types not expected"
    -- A removed Resolver. Use a newly introduced resolver instead.
    go resolvers (LeftHandSideSingle BaseRsignalResolver) (LeftHandSideWildcard _) _ kA = case resolvers of
      [] -> internalError "Not enough new SignalResolvers"
      r:rs -> (rs, weakenReplace r kA)
    go resolvers (LeftHandSidePair old1 old2) (LeftHandSidePair new1 new2) kB' kA
      | (resolvers1, kA1) <- go resolvers old1 new1 (kB' .> weakenWithLHS new2) kA
      = go resolvers1 old2 new2 kB' kA1
    go resolvers (LeftHandSideWildcard _) (LeftHandSideWildcard _) _ kA = (resolvers, kA)
    go _ _ _ _ _ = internalError "LeftHandSide mismatch"

-- Captures existential env2'
data DeclareRemovedResolvers kernel env1 env1' where
  DeclareRemovedResolvers
    :: (BuildSchedule kernel env2' -> BuildSchedule kernel env1')
    -> env1 :> env2'
    -> DeclareRemovedResolvers kernel env1 env1'
