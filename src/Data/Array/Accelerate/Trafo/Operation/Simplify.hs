{-# LANGUAGE EmptyCase           #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}
{-# OPTIONS_HADDOCK hide #-}
-- |
-- Module      : Data.Array.Accelerate.Trafo.Operation.Simplify
-- Copyright   : [2012..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.Trafo.Operation.Simplify (
  simplify, simplifyFun, SimplifyOperation(..), CopyOperation(..), isNoOp,
  copyOperationsForArray, detectMapCopies, detectBackpermuteCopies
) where

import Data.Array.Accelerate.AST.Environment
import Data.Array.Accelerate.AST.Idx
import Data.Array.Accelerate.AST.IdxSet                     ( IdxSet )
import qualified Data.Array.Accelerate.AST.IdxSet           as IdxSet
import Data.Array.Accelerate.AST.LeftHandSide
import Data.Array.Accelerate.AST.Operation
import Data.Array.Accelerate.Error
import Data.Array.Accelerate.Array.Buffer
import Data.Array.Accelerate.Type
import Data.Array.Accelerate.Representation.Type
import Data.Array.Accelerate.Representation.Array
import Data.Array.Accelerate.Analysis.Match
import qualified Data.Array.Accelerate.Trafo.Exp.Simplify   as Exp
import Data.Array.Accelerate.Trafo.Exp.Substitution
import Data.Array.Accelerate.Trafo.Var
import Data.Array.Accelerate.Trafo.Substitution             hiding ( weakenArrayInstr )
import Data.Array.Accelerate.Trafo.WeakenedEnvironment
import Data.Array.Accelerate.Trafo.Operation.Substitution
import Data.Array.Accelerate.Trafo.LiveVars                 ( SubTupR(..), subTupR, subTupRpair, subTupPreserves )
import Data.Maybe                                           ( mapMaybe )
import Data.List                                            ( foldl' )
import Data.Text                                            ( Text )
import Control.Monad
import Data.Functor.Identity

class SimplifyOperation op where
  detectCopy :: op f -> Args env f -> [CopyOperation env]
  detectCopy _ _ = []

data CopyOperation env where
  CopyOperation
    :: Idx env (Buffer t) -- input
    -> Idx env (Buffer t) -- output
    -> CopyOperation env

isNoOp :: SimplifyOperation op => op f -> Args env f -> Bool
-- An operation is a no-op if all outputs are copies of themselves.
-- For instance, 'map id xs xs' is a no-op.
-- This pattern is created by in-place updates, on the copy of the defaults
-- array of a permute.
isNoOp op args = all (\(Exists idx) -> idx `IdxSet.member` copied) $ argsOutputs args
  where
    copied = IdxSet.fromList
      $ map (\(CopyOperation idx _) -> Exists idx)
      $ filter (\(CopyOperation i o) -> i == o)
      $ detectCopy op args

copyOperationsForArray :: forall env sh sh' t. Arg env (In sh t) -> Arg env (Out sh' t) -> [CopyOperation env]
copyOperationsForArray (ArgArray _ (ArrayR _ tp) _ input) (ArgArray _ _ _ output) = go tp input output []
  where
    go :: forall s. TypeR s -> GroundVars env (Buffers s) -> GroundVars env (Buffers s) -> [CopyOperation env] -> [CopyOperation env]
    go (TupRpair t1 t2) (TupRpair i1 i2) (TupRpair o1 o2) = go t1 i1 o1 . go t2 i2 o2
    go (TupRsingle t) (TupRsingle (Var _ input')) (TupRsingle (Var _ output'))
      | Refl <- reprIsSingle @ScalarType @s @Buffer t = (CopyOperation input' output' :)
    go _ _ _ = id

detectMapCopies :: forall genv sh t s. Args genv (Fun' (t -> s) -> In sh t -> Out sh s -> ()) -> [CopyOperation genv]
detectMapCopies (ArgFun (Lam lhs (Body body)) :>: ArgArray _ _ _ input :>: ArgArray _ _ _ output :>: ArgsNil)
  = detectMapCopies' lhs body input output
detectMapCopies (ArgFun (Body f) :>: _ ) = functionImpossible $ expType f
detectMapCopies (ArgFun (Lam _ (Lam _ _)) :>: _ :>: ArgArray _ (ArrayR _ tp) _ _ :>: ArgsNil)
  = functionImpossible tp

detectMapCopies' :: forall genv env t s. ELeftHandSide t () env -> OpenExp env genv s -> GroundVars genv (Buffers t) -> GroundVars genv (Buffers s) -> [CopyOperation genv]
detectMapCopies' lhs body input output = go Just body output []
  where
    go :: forall env' s'. env' :?> env -> OpenExp env' genv s' -> GroundVars genv (Buffers s') -> [CopyOperation genv] -> [CopyOperation genv]
    go k (Assume _ e2) o = go k e2 o
    go k (Pair e1 e2) (TupRpair o1 o2) = go k e1 o1 . go k e2 o2
    go k (Let lhs' _ expr) output'     = go (strengthenWithLHS lhs' >=> k) expr output'
    go k (Evar (Var tp idx)) (TupRsingle (Var _ output'))
      | Just idx' <- k idx -- Check if index is bound by the function (opposed to local binding)
      , Refl <- reprIsSingle @ScalarType @s' @Buffer tp
      = (CopyOperation (findInput idx') output' :)
    go _ _ _ = id

    findInput :: Idx env t' -> Idx genv (Buffer t')
    findInput idx = case findInput' lhs input idx of
      Right buffer -> buffer
      Left idx' -> case idx' of {}

    findInput' :: forall u env1 env2 t'. ELeftHandSide u env1 env2 -> GroundVars genv (Buffers u) -> Idx env2 t' -> Either (Idx env1 t') (Idx genv (Buffer t'))
    findInput' (LeftHandSideWildcard _) _ idx = Left idx
    findInput' (LeftHandSideSingle tp) (TupRsingle (Var _ buffer)) idx = case idx of
      SuccIdx idx' -> Left idx'
      ZeroIdx
        | Refl <- reprIsSingle @ScalarType @u @Buffer tp -> Right buffer
    findInput' (LeftHandSidePair l1 l2) (TupRpair in1 in2) idx = case findInput' l2 in2 idx of
      Left idx' -> findInput' l1 in1 idx'
      Right buffer -> Right buffer
    findInput' _ _ _ = internalError "Tuple mismatch"

detectBackpermuteCopies :: forall env sh sh' t. Args env (Fun' (sh' -> sh) -> In sh t -> Out sh' t -> ()) -> [CopyOperation env]
detectBackpermuteCopies (ArgFun f :>: input@(ArgArray _ _ sh _) :>: output@(ArgArray _ _ sh' _) :>: ArgsNil)
  | Just Refl <- matchVars sh sh'
  , Just Refl <- isIdentity f = copyOperationsForArray input output
detectBackpermuteCopies _ = []

-- TODO for Fences: Add a way to store that one variable implies that another
-- variable is also resolved. Eg in 'let e2 = fence { e1 } assert e0 >= 0', we
-- know that after a fence on e2, e1 is also resolved.
data Info env t where
  -- | This variable has a known value
  InfoConst    :: IdxSet env -- The set of variables one should synchronise with in a Fence
               -> ScalarType t
               -> t
               -> Info env t -- A constant scalar
  -- | This variable is alias of another variable
  InfoAlias    :: IdxSet env -- The set of variables one should synchronise with in a Fence
               -> Idx env t
               -> Info env t
  -- | This is a buffer with undefined content (e.g. directly after an Alloc)
  InfoUndef    :: Info env (Buffer t)
  -- | Information on a buffer
  InfoBuffer   :: Maybe (Idx env t) -- In case of a Unit, the index of the scalar variable that it contains.
               -- Copy of another buffer. This is similar to an alias, but a buffer may only
               -- be a copy of another buffer temporarily. A write to the original or copy
               -- causes that they aren't copies any more. Hence we also keep track in
               -- InfoBuffer of the buffers it was copied to.
               -> Maybe (Idx env (Buffer t))
               -> [Idx env (Buffer t)] -- List of buffers where this buffer is copied to
               -> Info env (Buffer t)
  -- | This variable is resolved, as enforced by a Fence
  InfoResolved :: Info env t
  -- | No information available
  InfoNone     :: Info env t

newtype InfoEnv env = InfoEnv { unInfoEnv :: WEnv Info env }

emptySimplifyEnv :: InfoEnv ()
emptySimplifyEnv = InfoEnv wempty

instance Sink Info where
  weaken k (InfoAlias set idx) = InfoAlias (IdxSet.map (weaken k) set) $ weaken k idx
  weaken k (InfoConst set t c) = InfoConst (IdxSet.map (weaken k) set) t c
  weaken k (InfoBuffer unitScalar copyOf copied) = InfoBuffer (fmap (weaken k) unitScalar) (fmap (weaken k) copyOf) (fmap (weaken k) copied)
  weaken _ InfoUndef = InfoUndef
  weaken _ InfoResolved = InfoResolved
  weaken _ InfoNone = InfoNone

infoFor :: Idx env t -> InfoEnv env -> Info env t
infoFor ix (InfoEnv env) = wprj ix env

-- Substitutions for aliasing.
-- This substitution only assures that we use the original declaration instead
-- of the alias. It does not remove the definition of the alias, a later pass
-- should remove that (with a (strongly) live variable analysis).
--
-- These substitutions might only be sound after synchronising with certain
-- variables. Function 'syncSubstitute' returns the set of these variables.
-- This is needed to ensure that the right assertions are evaluated before
-- using the substituted variable. This occurs for instance in this program:
--
-- let x = { fence c; return y }
--
-- Here we may substitute x with y, if we put a fence on c.
--
substitute :: InfoEnv env -> env :> env
substitute env = Weaken $ \idx -> case infoFor idx env of
  InfoAlias _ idx' -> idx'
  InfoBuffer _ (Just idx') _ -> idx'
  _              -> idx

substituteUnlessResolved :: InfoEnv env -> Exists (Idx env) -> Maybe (Exists (Idx env))
substituteUnlessResolved env (Exists idx) = case infoFor idx env of
  InfoConst _ _ _ -> Nothing
  InfoResolved -> Nothing
  InfoAlias _ idx' -> Just $ Exists idx'
  InfoBuffer _ (Just idx') _ -> Just $ Exists idx'
  _ -> Just $ Exists idx

-- When reading from an array, we can read from another buffer with the same
-- contents. The index of such copy is stored in InfoBuffer. When writing we
-- cannot do that. Note that after a write, the information about the copy
-- is removed in 'invalidate'.
--
substituteOutput :: InfoEnv env -> env :> env
substituteOutput env = Weaken $ \idx -> case infoFor idx env of
  InfoAlias _ idx' -> idx'
  _                -> idx

-- The variables one should synchronise with, for 'substitute' to be sound.
-- These variables should be passed to Fence.
--
syncSubstitute :: InfoEnv env -> Idx env t -> IdxSet env
syncSubstitute env idx = case infoFor idx env of
  InfoConst set _ _ -> set
  InfoAlias set _ -> set
  _ -> IdxSet.empty

syncSubstitutes :: InfoEnv env -> IdxSet env -> IdxSet env
syncSubstitutes env vars =
  IdxSet.unions
    $ map
      (\case
        Exists (InfoAlias set _) -> set
        _ -> IdxSet.empty
      )
    $ wprjSet vars (unInfoEnv env)

simplifyFun :: SimplifyOperation op => OperationAfun op () t -> OperationAfun op () t
simplifyFun fun = snd (simplifyFun' fun) emptySimplifyEnv

-- Returns a set of array variables which may have been written to, and a the simplified function (given an InfoEnv)
simplifyFun' :: SimplifyOperation op => OperationAfun op env t -> (IdxSet env, InfoEnv env -> OperationAfun op env t)
simplifyFun' (Alam lhs f) =
  (IdxSet.drop' lhs set, \env -> Alam lhs $ f' $ bindEnv lhs env)
  where
    (set, f') = simplifyFun' f
simplifyFun' (Abody body)  = (set, \env -> Abody $ body' env)
  where
    (set, body') = simplify' (TupRsingle Shared) body

simplifyFunWithUniqueness :: SimplifyOperation op => Uniquenesses t -> OperationAfun op env (t -> t) -> (IdxSet env, InfoEnv env -> OperationAfun op env (t -> t))
simplifyFunWithUniqueness uniquenesses (Alam lhs (Abody body)) =
  ( IdxSet.drop' lhs set
  , \env -> Alam lhs $ Abody $ body' $ bindEnv lhs env
  )
  where
    (set, body') = simplify' uniquenesses body
simplifyFunWithUniqueness _ (Abody body) = groundFunctionImpossible $ groundsR body
simplifyFunWithUniqueness _ (Alam lhs (Alam _ _)) = groundFunctionImpossible $ lhsToTupR lhs

simplify :: SimplifyOperation op => OperationAcc op () t -> OperationAcc op () t
simplify acc = snd (simplify' (TupRsingle Shared) acc) emptySimplifyEnv

-- Returns the simplified program and a set of array variables which may have been written to
simplify' :: SimplifyOperation op => Uniquenesses t -> OperationAcc op env t -> (IdxSet env, InfoEnv env -> OperationAcc op env t)
simplify' uniquenesses = \case
  Exec op args
    | output <- outputArrays args ->
      ( outputArrays args
      , \env ->
        let
          fenceSet = syncSubstitutes env $ IdxSet.fromVarList $ argsVars args
          args' = mapArgs (simplifyArg env) args
        in
          if isUndefCopy env output $ detectCopy op args then
            Return TupRunit
          else
            fence fenceSet $ Exec op args')
  Return vars ->
    -- Note that we do not need to check for writes to variables here.
    -- This construct may cause aliassing of variables, but an aliassed
    -- variable cannot be unique and thus we do not need to signal the
    -- original variable as mutated if it's returned.
    ( variableIndices uniquenesses vars
    , \env ->
      fence (syncSubstitutes env $ IdxSet.fromVars vars)
        $ Return $ simplifyReturnVars env uniquenesses vars
    )
  Manifest var -> ( IdxSet.empty, const $ Manifest var )
  Compute expr ->
    ( IdxSet.empty
    , \env ->
      fence (syncSubstitutes env $ IdxSet.fromVarList $ expGroundVars expr)
        $ compute $ simplifyExp env expr
    )
  Alet lhs us bnd body ->
    let
      (setBnd, bnd') = simplify' us bnd
      (setBody, body') = simplify' uniquenesses body
    in
      ( setBnd `IdxSet.union` IdxSet.drop' lhs setBody
      , \env ->
          let
            bnd'' = bnd' env
            env' = bindingEnv setBnd IdxSet.empty lhs bnd'' (invalidate setBnd env)
          in alet' lhs us bnd'' (body' env')
      )
  Alloc shr tp sh ->
    ( IdxSet.empty
    , \env ->
      fence (syncSubstitutes env $ IdxSet.fromVars sh)
        $ Alloc shr tp $ mapTupR (weaken $ substitute env) sh
    )
  Use tp 1 buffer ->
    ( IdxSet.empty
    , const
      $ Alet (LeftHandSideSingle (GroundRscalar tp)) (TupRsingle Shared) (Compute $ Const tp $ indexBuffer tp buffer 0)
      $ Unit (Var tp ZeroIdx)
    )
  Use tp n buffer -> (IdxSet.empty, const $ Use tp n buffer)
  Unit var ->
    ( IdxSet.empty
    , \env ->
      fence (syncSubstitute env $ varIdx var)
        $ Unit $ weaken (substitute env) var
    )
  Acond cond true false ->
    let
      (setT, true')  = simplify' uniquenesses true
      (setF, false') = simplify' uniquenesses false
      set = IdxSet.union setT setF
    in
      ( set
      , \env -> case infoFor (varIdx cond) env of
        InfoConst d _ 0  -> fence d $ false' env
        InfoConst d _ _  -> fence d $ true'  env
        InfoAlias d ix -> fence d $ Acond (cond{varIdx = ix}) (true' env) (false' env)
        _              -> Acond cond (true' env) (false' env)
      )

  Awhile us cond step initial ->
    let
      (setC, cond') = simplifyFun' cond
      (setS, step') = simplifyFunWithUniqueness us step
      set = setC `IdxSet.union` setS `IdxSet.union` variableIndices us initial
    in
      ( set
      , \env ->
          let
            env' = invalidate set env
          in
            fence (syncSubstitutes env $ IdxSet.fromVars initial)
              $ awhileSimplifyInvariant us (cond' env') (step' env') $ simplifyReturnVars env us initial
      )

  Atrace msg t ->
    let
      set = arrayDescriptorsIdxSet t
    in
      ( set
      , \env ->
        fence (syncSubstitutes env set)
        $ Atrace msg $ simplifyArrayDescriptor env t
    )

  Aassert msg cond ->
    ( IdxSet.empty
    , \env ->
      fence (syncSubstitutes env $ IdxSet.fromVarList $ expGroundVars cond)
        $ assert msg $ simplifyExp env cond
    )

  Aassume cond ->
    ( IdxSet.empty
    , \env ->
      fence (syncSubstitutes env $ IdxSet.fromVarList $ expGroundVars cond)
        $ assume $ simplifyExp env cond)

-- Mark all deps as evaluated in the environment
-- Remove deps from the list if they were already evaluated.
  Fence deps next ->
    let
      (set, next') = simplify' uniquenesses next
    in
      ( set
      , \env ->
          let
            deps' = IdxSet.union (syncSubstitutes env deps) $ IdxSet.fromList $ mapMaybe (substituteUnlessResolved env) $ IdxSet.toList deps
            env' = InfoEnv $ wupdateSetWeakened
              (\_ -> \case
                InfoNone -> InfoResolved
                info -> info
              )
              deps'
              $ unInfoEnv env
          in
            fence
              deps'
              (next' env')
      )

simplifyArrayDescriptor :: InfoEnv env -> ArrayDescriptors env t -> ArrayDescriptors env t
simplifyArrayDescriptor env = mapTupR (\(ArrayDescriptor shr sh buffers) -> ArrayDescriptor shr (mapTupR (weaken $ substitute env) sh) (mapTupR (weaken $ substitute env) buffers))

-- Given an environment, the set of updated variables and a list of copies of
-- an operation, checks whether the operation copies all its outputs from
-- undefined buffers.
--
-- This is specifically needed for permute, as it is common to use
-- `generate .. (const undef)` as defaults array. Permute introduces a map to
-- copy the defaults array and make it unique. The generate is already removed
-- in an earlier pass, and the map will be removed here.
isUndefCopy :: InfoEnv env -> IdxSet env -> [CopyOperation env] -> Bool
isUndefCopy env outputs copies
  = outputs == IdxSet.fromList (map (\(CopyOperation _ o) -> Exists o) copies)
  && all (\(CopyOperation i _) -> isUndef $ infoFor i env) copies
  where
    isUndef InfoUndef = True
    isUndef _ = False

variableIndices :: Uniquenesses t -> GroundVars env t -> IdxSet env
variableIndices (TupRsingle Unique) (TupRsingle var) = IdxSet.singleton $ varIdx var
variableIndices (TupRpair u1 u2) (TupRpair v1 v2) = variableIndices u1 v1 `IdxSet.union` variableIndices u2 v2
variableIndices _ _ = IdxSet.empty

simplifyReturnVars :: InfoEnv env -> Uniquenesses t -> GroundVars env t -> GroundVars env t
simplifyReturnVars env (TupRpair u1 u2) (TupRpair v1 v2) =
  simplifyReturnVars env u1 v1 `TupRpair` simplifyReturnVars env u2 v2
simplifyReturnVars env (TupRsingle Shared) v = mapTupR (weaken $ substitute env) v
simplifyReturnVars env (TupRsingle Unique) v = mapTupR (weaken $ substituteOutput env) v
simplifyReturnVars _   TupRunit _ = TupRunit
simplifyReturnVars _   _ _ = internalError "Tuple mismatch"

findConstant :: forall env env' t. WEnv' Info env' env -> ScalarType t -> t -> Maybe (Idx env t)
findConstant env tp1 value1 = go env
  where
    go :: WEnv' Info env2 env1 -> Maybe (Idx env1 t)
    go WEmpty = Nothing
    go (WPushA _e (InfoConst d tp2 value2))
      | IdxSet.null d
      , Just idx <- tryMatch tp2 value2 = Just idx
    go (WPushB _e (InfoConst d tp2 value2))
      | IdxSet.null d
      , Just idx <- tryMatch tp2 value2 = Just idx
    go (WPushA e _) = SuccIdx <$> go e
    go (WPushB e _) = SuccIdx <$> go e
    go (WWeaken _ e) = go e

    tryMatch :: ScalarType s -> s -> Maybe (Idx (env3, s) t)
    tryMatch tp2 value2
      | Just Refl <- matchScalarType tp1 tp2
      = case tp1 of
          SingleScalarType t
            | SingleDict <- singleDict t -- Gives 'Eq t'
            , value1 == value2 -> Just ZeroIdx
          VectorScalarType (VectorType _ t)
            | SingleDict <- singleDict t
            , value1 == value2 -> Just ZeroIdx
          _ -> Nothing
      | otherwise = Nothing

bindingEnv :: forall op t env env'. SimplifyOperation op => IdxSet env -> IdxSet env -> GLeftHandSide t env env' -> OperationAcc op env t -> InfoEnv env -> InfoEnv env'
bindingEnv _ fenceSet lhs (Compute expr) (InfoEnv environment) = InfoEnv $ go weakenId lhs expr environment
  where
    go :: env :> env1 -> GLeftHandSide s env1 env2 -> Exp env s -> WEnv' Info env1 env1 -> WEnv' Info env2 env2
    go k (LeftHandSideSingle _) e env
      | ArrayInstr (Parameter var) _ <- e = wpush env $ weaken (weakenSucc' k) $ InfoAlias fenceSet $ varIdx var
      | Const tp c <- e = case findConstant env tp c of
        Just idx -> wpush env $ InfoAlias (IdxSet.map (weaken (weakenSucc' k)) fenceSet) $ SuccIdx idx
        Nothing -> wpush env $ InfoConst (IdxSet.map (weaken (weakenSucc' k)) fenceSet) tp c
      | otherwise = wpush env InfoNone

    go k (LeftHandSidePair l1 l2) (Pair e1 e2) env
      = go (weakenWithLHS l1 .> k) l2 e2 $ go k l1 e1 env

    go _k (LeftHandSideWildcard _) _ env = env

    go _ l _ env = goUnknown l env

    goUnknown :: GLeftHandSide s env1 env2 -> WEnv' Info env1 env1 -> WEnv' Info env2 env2
    goUnknown (LeftHandSideSingle _)   env = wpush env InfoNone
    goUnknown (LeftHandSideWildcard _) env = env
    goUnknown (LeftHandSidePair l1 l2) env = goUnknown l2 $ goUnknown l1 env
bindingEnv _ fenceSet lhs (Return variables) (InfoEnv environment) = InfoEnv $ weaken (weakenWithLHS lhs) $ go lhs variables environment
  where
    go :: GLeftHandSide s env1 env2 -> GroundVars env s -> WEnv' Info env env1 -> WEnv' Info env env2
    go (LeftHandSideSingle _)   (TupRsingle (Var _ ix)) env = wpush' env $ InfoAlias fenceSet ix
    go (LeftHandSidePair l1 l2) (TupRpair v1 v2)        env = go l2 v2 $ go l1 v1 env
    go (LeftHandSideWildcard _) _                       env = env
    go _                        _                       _   = internalError "Tuple mismatch"
bindingEnv _ fenceSet (LeftHandSideSingle _) Alloc{} (InfoEnv env)
  | IdxSet.null fenceSet = InfoEnv $ wpush env InfoUndef
bindingEnv _ fenceSet (LeftHandSideSingle _) (Unit (Var _ idx)) (InfoEnv env)
  | IdxSet.null fenceSet = InfoEnv $ wpush env $ InfoBuffer (Just $ SuccIdx idx) Nothing []
bindingEnv outputs fenceSet (LeftHandSideWildcard _) (Exec op args) env
  | IdxSet.null fenceSet = foldl' addCopy env $ detectCopy op args
    where
      addCopy :: InfoEnv env -> CopyOperation env -> InfoEnv env
      addCopy env' (CopyOperation input output)
        | input `IdxSet.member` outputs = env' -- The operation both reads and writes to 'input'. We cannot register input and output as copies, as input will get different values
        | otherwise = InfoEnv $ wupdate markCopy input $ wupdate (const $ InfoBuffer Nothing (Just input) []) output $ unInfoEnv env'
        where
          markCopy (InfoBuffer unitScalar copyOf list) = InfoBuffer unitScalar copyOf (output : list)
          markCopy (InfoAlias _ _) = internalError "Operation contains aliased variable, which should be substituted already"
          markCopy _ = (InfoBuffer Nothing Nothing [output])
bindingEnv outputs fenceSet lhs (Fence deps next) env
  = bindingEnv outputs (IdxSet.union fenceSet deps) lhs next env
bindingEnv _ _ lhs _ env = bindEnv lhs env

-- Updates the InfoEnv, with the information that the buffers in 'indices' may
-- have been updated. This breaks the 'is-copy-of' relation between buffers.
invalidate :: forall env. IdxSet env -> InfoEnv env -> InfoEnv env
invalidate indices infoEnv@(InfoEnv env1) =
  InfoEnv
    $ wupdateSetWeakened dropCopyTo indicesCopiesOf
    $ wupdateSetWeakened dropCopyOf indicesCopiedTo
    $ wremoveSet InfoNone indices' env1
  where
    indices' :: IdxSet env
    indices' = IdxSet.map (weaken $ substituteOutput infoEnv) indices

    findCopies :: Exists (Idx env) -> (IdxSet env, IdxSet env)
    findCopies (Exists idx) = case infoFor idx infoEnv of
      InfoAlias _ _ -> internalError "Alias should be substituted already"
      InfoBuffer _ (Just idx') copies -> (IdxSet.singleton idx', IdxSet.fromList' copies)
      _ -> (IdxSet.empty, IdxSet.empty)

    (indicesCopiesOf', indicesCopiedTo') = unzip $ map findCopies $ IdxSet.toList indices'
    indicesCopiesOf = IdxSet.unions indicesCopiesOf'
    indicesCopiedTo = IdxSet.unions indicesCopiedTo'

    -- Forgets that this buffer is a copy of a buffer in indices'.
    dropCopyOf :: env' :> env -> Info env' t -> Info env' t
    dropCopyOf _ (InfoBuffer unitScalar _ c)
      = InfoBuffer unitScalar Nothing c
    dropCopyOf _ _ = error "TODO WALL: NON-EXHAUSTIVE PATTERN MATCH"

    -- Forgets that this buffer is copied to buffers in indices'
    dropCopyTo :: env' :> env -> Info env' t -> Info env' t
    dropCopyTo k (InfoBuffer unitScalar copyOf copiedTo')
      = InfoBuffer unitScalar copyOf $ filter (\idx -> not $ k >:> idx `IdxSet.member` indices) copiedTo'
    dropCopyTo _ _ = error "TODO WALL: NON-EXHAUSTIVE PATTERN MATCH"

outputArrays :: Args env args -> IdxSet env
outputArrays = IdxSet.fromList . mapMaybe f . argsVars
  where
    f :: Exists (Var AccessGroundR env) -> Maybe (Exists (Idx env))
    f (Exists (Var (AccessGroundRbuffer In _) _)) = Nothing
    f (Exists (Var (AccessGroundRbuffer _ _) idx)) = Just (Exists idx) -- Out or Mut
    f _ = Nothing

simplifyExp :: forall env t. InfoEnv env -> Exp env t -> Exp env t
simplifyExp env = Exp.simplifyExp . runIdentity . rebuildArrayInstrOpenExp (simplifyArrayInstr env)

simplifyExpFun :: forall env t. InfoEnv env -> Fun env t -> Fun env t
simplifyExpFun env = Exp.simplifyFun . runIdentity . rebuildArrayInstrFun (simplifyArrayInstr env)

simplifyArrayInstr :: InfoEnv env -> RebuildArrayInstr Identity (ArrayInstr env) (ArrayInstr env)
simplifyArrayInstr env instr@(Parameter (Var tp idx)) = case infoFor idx env of
  InfoAlias _ idx' -> simplifyArrayInstr env (Parameter $ Var tp idx')
  InfoConst _ _ c  -> Identity $ const $ Const tp c
  InfoBuffer _ _ _ -> bufferImpossible tp
  _                -> Identity $ \arg -> ArrayInstr instr arg
simplifyArrayInstr env instr@(Index (Var tp idx)) = case infoFor idx env of
  InfoAlias _ idx' -> simplifyArrayInstr env (Index $ Var tp idx')
  InfoBuffer (Just idx') _ _ -> Identity $ const $ runIdentity (simplifyArrayInstr env $ Parameter $ Var eltTp idx') Nil -- Unit
  InfoBuffer _ (Just idx') _  -> simplifyArrayInstr env (Index $ Var tp idx') -- Copy
  InfoUndef -> Identity $ const $ Undef eltTp
  _              -> Identity $ \arg -> ArrayInstr instr arg
  where
    eltTp = case tp of
      GroundRscalar t -> bufferImpossible t
      GroundRbuffer t -> t

simplifyArg :: InfoEnv env -> Arg env t -> Arg env t
simplifyArg env (ArgVar var)  = ArgVar $ mapTupR (weaken $ substitute env) var
simplifyArg env (ArgExp expr) = ArgExp $ simplifyExp env expr
simplifyArg env (ArgFun fun)  = ArgFun $ simplifyExpFun env fun
simplifyArg env (ArgArray m repr sh buffers)
  = ArgArray m repr (mapTupR (weaken $ substitute env) sh) (mapTupR (weaken $ substituteBuffer env) buffers)
  where
    -- Output buffers may not be substituted by buffers with the same content.
    substituteBuffer
      | In <- m = substitute
      | Out <- m = substituteOutput
      | Mut <- m = const weakenId

bindEnv :: GLeftHandSide t env env' -> InfoEnv env -> InfoEnv env'
bindEnv lhs (InfoEnv env') = InfoEnv $ go lhs $ weaken k env'
  where
    k = weakenWithLHS lhs

    go :: GLeftHandSide t env1 env1' -> WEnv' Info env' env1 -> WEnv' Info env' env1'
    go (LeftHandSideWildcard _) env1 = env1
    go (LeftHandSideSingle _)   env1 = wpush' env1 InfoNone
    go (LeftHandSidePair l1 l2) env1 = go l2 $ go l1 env1

unionSubTupR :: SubTupR t s -> SubTupR t s' -> Exists (SubTupR t)
unionSubTupR SubTupRskip s = Exists s
unionSubTupR s SubTupRskip = Exists s
unionSubTupR (SubTupRpair l1 r1) (SubTupRpair l2 r2)
  | Exists l <- unionSubTupR l1 l2
  , Exists r <- unionSubTupR r1 r2
  = Exists $ subTupRpair l r
unionSubTupR _ _ = Exists SubTupRkeep

-- Detects which parts of the state of an awhile loop are invariant and
-- transforms the program accordingly.
-- For instance, if the state of an awhile loop contains an array whose
-- shape doesn't change throughout the execution of the awhile loop,
-- it will remove the shape from the state of the loop and always refer
-- to the initial shape of the array.
awhileSimplifyInvariant
  :: Uniquenesses a
  -> PreOpenAfun op env (a -> PrimBool)
  -> PreOpenAfun op env (a -> a)
  -> GroundVars     env a
  -> PreOpenAcc  op env a
awhileSimplifyInvariant us cond step initial = case awhileDropInvariantFun initial step of
  Exists SubTupRkeep -> Awhile us cond step initial
  Exists sub
    | Just Refl <- subTupPreserves tp sub -> Awhile us cond step initial
    | DeclareVars lhs k value <- declareVars $ subTupR sub tp ->
      alet' lhs (subTupR sub us)
        (Awhile (subTupR sub us)
          (subTupFunctionArgument sub initial cond)
          (subTupFunctionArgument sub initial $ subTupFunctionResult sub step)
          (subTupR sub initial))
        (Return $ subTupResult sub (mapTupR (weaken k) initial) (value weakenId))
  where
    tp = case cond of
      Alam lhs _ -> lhsToTupR lhs
      Abody body -> groundFunctionImpossible $ groundsR body

awhileDropInvariantFun :: GroundVars env t -> OperationAfun op env (t -> t) -> Exists (SubTupR t)
awhileDropInvariantFun initial (Alam lhs (Abody body)) =
  awhileDropInvariant (mapTupR (weaken $ weakenWithLHS lhs) initial) (lhsMaybeVars lhs) body
awhileDropInvariantFun _initial (Alam lhs (Alam _ _))   = groundFunctionImpossible (lhsToTupR lhs)
awhileDropInvariantFun _initial (Abody body)            = groundFunctionImpossible (groundsR body)

-- Computes a SubTupR that removes variables that are invariant in the while loop.
-- Invariant here means that the step function of the loop returns the input unchanged,
-- or returns the initial value in each step.
-- This pattern often occurs with sizes of arrays.
awhileDropInvariant :: GroundVars env t -> MaybeVars GroundR env t -> OperationAcc op env t -> Exists (SubTupR t)
awhileDropInvariant initial argument = \case
  Return vars
    -> matchReturn initial argument vars
  Alet (LeftHandSideWildcard _) _ _ body
    -> awhileDropInvariant initial argument body
  Alet lhs _ _ body
    -> awhileDropInvariant
      (mapTupR (weaken $ weakenWithLHS lhs) initial)
      (mapTupR (weaken $ weakenWithLHS lhs) argument)
      body
  Acond _ t f
    | Exists subTupT <- awhileDropInvariant initial argument t
    , Exists subTupF <- awhileDropInvariant initial argument f
    -- Only remove variables if they are invariant in both branches.
    -- Thus, preserve variables in the union of subTupT and subTupF.
    -> unionSubTupR subTupT subTupF
  _ -> Exists SubTupRkeep -- No invariant variables
  where
    matchReturn :: GroundVars env t' -> MaybeVars GroundR env t' -> GroundVars env t' -> Exists (SubTupR t')
    matchReturn (TupRpair i1 i2) (TupRpair a1 a2) (TupRpair v1 v2)
      | Exists s1 <- matchReturn i1 a1 v1
      , Exists s2 <- matchReturn i2 a2 v2
      = case (s1, s2) of
          (SubTupRskip, SubTupRskip) -> Exists SubTupRskip
          _ -> Exists $ subTupRpair s1 s2
    matchReturn (TupRsingle i) (TupRsingle arg) (TupRsingle var)
      | Just Refl <- matchVar i var
      = Exists SubTupRskip
      | JustVar arg' <- arg
      , Just Refl <- matchVar arg' var
      = Exists SubTupRskip
      | otherwise
      = Exists SubTupRkeep
    matchReturn TupRunit _ _ = Exists SubTupRskip
    matchReturn _ _ _ = internalError "Tuple mismatch"

subTupFunctionResult :: SubTupR t t' -> OperationAfun op env (ta -> t) -> OperationAfun op env (ta -> t')
subTupFunctionResult sub (Alam lhs (Abody body)) = Alam lhs $ Abody $ subTupAcc sub body
subTupFunctionResult _ _ = internalError "Illegal function"

subTupAcc :: SubTupR t t' -> OperationAcc op env t -> OperationAcc op env t'
subTupAcc sub = \case
  Return vars -> Return $ subTupR sub vars
  Alet lhs us bnd body -> Alet lhs us bnd $ subTupAcc sub body
  Acond c t f -> Acond c (subTupAcc sub t) (subTupAcc sub f)
  _ -> internalError "Cannot subTup this program"

subTupFunctionArgument :: SubTupR t t' -> GroundVars env t -> OperationAfun op env (t -> tr) -> OperationAfun op env (t' -> tr)
subTupFunctionArgument sub initial (Alam lhs body)
  | SubTupSubstitution lhs' k <- subTupSubstitution sub lhs initial
  = Alam lhs' $ weaken k body
subTupFunctionArgument _ _ (Abody body) = groundFunctionImpossible $ groundsR body

subTupResult :: SubTupR t t' -> GroundVars env t -> GroundVars env t' -> GroundVars env t
subTupResult SubTupRkeep _ result = result
subTupResult SubTupRskip initial _ = initial
subTupResult (SubTupRpair s1 s2) (TupRpair i1 i2) (TupRpair r1 r2) = subTupResult s1 i1 r1 `TupRpair` subTupResult s2 i2 r2
subTupResult _ _ _ = internalError "Tuple mismatch"

data SubTupSubstitution env env1 t t' where
  SubTupSubstitution
    :: GLeftHandSide t' env1 env2
    -> env :> env2
    -> SubTupSubstitution env env1 t t'

subTupSubstitution :: SubTupR t t' -> GLeftHandSide t env env' -> GroundVars env t -> SubTupSubstitution env' env t t'
subTupSubstitution SubTupRskip lhs vars = SubTupSubstitution (LeftHandSideWildcard TupRunit) (go lhs vars weakenId)
  where
    go :: GLeftHandSide s env1 env2 -> GroundVars env s -> env1 :> env -> env2 :> env
    go (LeftHandSideWildcard _) _ k = k
    go (LeftHandSideSingle _)   (TupRsingle (Var _ ix)) k = Weaken $ \case
      ZeroIdx -> ix
      SuccIdx ix' -> k >:> ix'
    go (LeftHandSidePair l1 l2) (TupRpair v1 v2) k = go l2 v2 $ go l1 v1 k
    go _ _ _ = internalError "Tuple mismatch"
subTupSubstitution SubTupRkeep lhs _ = SubTupSubstitution lhs weakenId
subTupSubstitution (SubTupRpair s1 s2) (LeftHandSidePair l1 l2) (TupRpair v1 v2)
  | SubTupSubstitution l1' k1 <- subTupSubstitution s1 l1 v1
  , Exists l2'' <- rebuildLHS l2
  , SubTupSubstitution l2' k2 <- subTupSubstitution s2 l2'' (mapTupR (weaken $ weakenWithLHS l1') v2)
  = SubTupSubstitution (LeftHandSidePair l1' l2') (k2 .> sinkWithLHS l2 l2'' k1)
subTupSubstitution s (LeftHandSideWildcard t) _
  = SubTupSubstitution (LeftHandSideWildcard $ subTupR s t) weakenId
subTupSubstitution _ _ _ = internalError "Tuple mismatch"

assert :: Text -> Exp env PrimBool -> OperationAcc op env Word8
assert _ (Const _ 1) = Compute (Const scalarTypeWord8 1)
assert msg c = Aassert msg c

assume :: Exp env PrimBool -> OperationAcc op env Word8
assume (Const _ 1) = Compute (Const scalarTypeWord8 1)
assume c = Aassume c

compute :: Exp env a -> OperationAcc op env a
compute (Assert msg c expr) =
  alet
    (LeftHandSideSingle $ GroundRscalar scalarTypeWord8)
    (Aassert msg c)
  $ Fence (IdxSet.singleton ZeroIdx)
  $ compute $ mapArrayInstr (weaken $ weakenSucc weakenId) expr
compute (Assume c expr) =
  alet
    (LeftHandSideSingle $ GroundRscalar scalarTypeWord8)
    (Aassume c)
  $ Fence (IdxSet.singleton ZeroIdx)
  $ compute $ mapArrayInstr (weaken $ weakenSucc weakenId) expr
compute expr
  | Just vars <- extractParams expr =
    Return $ mapTupR (\(Var tp ix) -> Var (GroundRscalar tp) ix) vars
  | otherwise =
    Compute expr
