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
      construct = \k' -> construct schedule (k' .> k)
    }

newtype BuildScheduleFun kernel env t =
  BuildScheduleFun{
    funConstruct
      :: forall env'.
         env :> env'
      -> BuildEnv env'
      -> UniformScheduleFun kernel env' t
  }

data BuildSpawn kernel env =
  BuildSpawn{
    -- The signals that this term resolves at the end.
    -- Corresponds with finallyResolves, but the SignalResolvers are converted to Signals.
    spawnFinallyResolves :: [Idx env Signal],
    spawnTerm :: (BuildSchedule kernel env)
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
    filter (\idx -> not (isResolved idx env))
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
      (spawnFinallyResolves second)
      (buildSeq (spawnTerm first) (spawnTerm second))

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
    = BPush (markResolved (map forceWeaken signals') env) IResolved
  | otherwise
    = BPush (markResolved (map forceWeaken signals) env) info
  where
    forceWeaken :: Idx (env, t) s -> Idx env s
    forceWeaken ZeroIdx = internalError "markResolved: input was not sorted or contains duplicates"
    forceWeaken (SuccIdx idx) = idx
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
      trivial = trivialBinding binding && trivial body,
      construct = constructLet False
    }
  | otherwise =
    BuildSchedule{
      directlyAwaits = [],
      finallyResolves = mapMaybe (strengthenWithLHS lhs) $ finallyResolves body,
      trivial = False,
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
    trivial = False,
    construct = \k env postponed cont ->
      let
        resolvers'' = map (weaken k) resolvers'
        signals = mapMaybe (\r -> findSignal r env) resolvers''
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
    construct = \k env postponed cont -> construct next k env postponed cont
  }
buildEffect effect next
  | canPostpone =
    BuildSchedule{
      directlyAwaits = directlyAwaits next,
      finallyResolves = finallyResolves next,
      trivial = effectIsTrivial && trivial next,
      construct = \k env postponed cont ->
        Effect (weaken' k effect)
          $ construct next k (updateEnv k env) postponed cont
    }
  | otherwise =
    BuildSchedule{
      directlyAwaits = [],
      finallyResolves = finallyResolves next,
      trivial = effectIsTrivial && trivial next,
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
      trivial = False,
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
    directlyAwaits = [], -- TODO: Compute this based on the use of the initial state and free variables of step.
    finallyResolves = finallyResolves next,
    trivial = False,
    construct = \k env postponed cont ->
      placePostponed postponed env
        $ Awhile
          io
          (funConstruct step k env)
          (mapTupR (weaken k) initial)
          (constructFull next k env nothingPostponed cont)
  }

buildFunLam
  :: BLeftHandSide t env1 env2
  -> BuildScheduleFun kernel env2 f
  -> BuildScheduleFun kernel env1 (t -> f)
buildFunLam lhs body =
  BuildScheduleFun{
    funConstruct = \k env -> case rebuildLHS lhs of
      Exists lhs' -> Slam lhs' $ funConstruct body (sinkWithLHS lhs lhs' k) (buildEnvSkip lhs' env)
  }

buildFunBody :: BuildSchedule kernel env -> BuildScheduleFun kernel env ()
buildFunBody body =
  BuildScheduleFun{
    funConstruct = \k env -> Sbody $ constructFull body k env nothingPostponed ContinuationEnd
  }

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
rebuildFun (Sbody body) = buildFunBody $ rebuild body

rebuild :: UniformSchedule kernel env -> BuildSchedule kernel env
rebuild = \case
  Return -> buildReturn
  Alet lhs bnd body ->
    buildLet lhs bnd $ rebuild body
  Effect eff next ->
    buildEffect eff $ rebuild next
  Acond var true false next ->
    buildAcond var (rebuild true) (rebuild false) (rebuild next)
  Awhile io f input next ->
    buildAwhile io (rebuildFun f) input (rebuild next)
  Spawn a b ->
    buildSpawn (rebuild a) (rebuild b)
