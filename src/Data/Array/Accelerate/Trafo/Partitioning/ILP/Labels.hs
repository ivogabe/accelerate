{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ViewPatterns #-}
module Data.Array.Accelerate.Trafo.Partitioning.ILP.Labels where


-- accelerate imports
import Data.Array.Accelerate.AST.Idx ( Idx(..) )
import Data.Array.Accelerate.AST.LeftHandSide ( LeftHandSide(..) )
import Data.Array.Accelerate.AST.Operation
import Data.Array.Accelerate.Representation.Type ( TupR(..) )

-- In this file, order very often subly does matter.
-- To keep this clear, we use S.Set whenever it does not,
-- and [] only when it does. It's also often efficient
-- by removing duplicates.
import qualified Data.Set as S

import Lens.Micro.TH ( makeLenses )
import Control.Monad.State
import Lens.Micro.Mtl ((<%=))


-- identifies nodes with unique Ints. and tracks their dependencies
-- `Label x Nothing` means that label x is top-level.
-- `Label x (Just y)` means that label x is (at ilp-construction time determined to be) a subcomputation of label y
-- Invariant: for all x, there is at most one `Label x _`: the second field is not to discriminate vars but to log extra information.
data Label = Label
  { _labelId :: Int
  , _parent :: Maybe Label
  } deriving (Eq, Ord, Show)
makeLenses ''Label

level :: Label -> Int
level (Label _ Nothing)  = 0
level (Label _ (Just l)) = 1 + level l

type Labels = S.Set Label

-- identifies elements of the environment with unique Ints.
newtype ELabel = ELabel Int
  deriving (Show, Eq, Ord, Num)


-- | Keeps track of which argument belongs to which labels
data LabelArgs args where
  LabelArgsNil :: LabelArgs ()
  (:>>:)       :: Labels -> LabelArgs t -> LabelArgs (s -> t)

-- | Keeps track of which array in the environment belongs to which label
data LabelEnv env where
  LabelEnvNil  :: LabelEnv ()
  (:>>>:)      :: (ELabel, Labels) -> LabelEnv t -> LabelEnv (t, s)
instance Semigroup (LabelEnv env) where
  LabelEnvNil <> LabelEnvNil = LabelEnvNil
  ((e1,l1):>>>:lenv1) <> ((e2,l2):>>>:lenv2)
    | e1 == e2 = (e1, l1<>l2) :>>>: (lenv1 <> lenv2)
    | otherwise = error "mappend for LabelEnv found two different labels"

freshE' :: State ELabel ELabel
freshE' = id <%= (+1)


-------------------------------
-- Traversals over stuff to add/extract Labels and ELabels,
-- or otherwise manipulate LabelArgs' or LabelEnvs


-- | Note that this throws some info away: Pair (Wildcard, Single) and Pair (Single, Wildcard) give identical results.
-- Use sites need to store the LHS itself too.
addLhs :: LeftHandSide s v env env' -> Labels -> LabelEnv env -> State ELabel (LabelEnv env')
addLhs LeftHandSideWildcard{} _ = pure
addLhs LeftHandSideSingle{}   l = \lenv -> freshE' >>= \e -> pure ((e, l) :>>>: lenv)
addLhs (LeftHandSidePair x y) l = addLhs x l >=> addLhs y l


weakLhsEnv :: LeftHandSide s v env env' -> LabelEnv env' -> LabelEnv env
weakLhsEnv LeftHandSideSingle{} (_:>>>: env) = env
weakLhsEnv LeftHandSideWildcard{} env = env
weakLhsEnv (LeftHandSidePair l r) env = weakLhsEnv l (weakLhsEnv r env)

emptyLabelEnv :: LabelEnv env -> LabelEnv env
emptyLabelEnv LabelEnvNil = LabelEnvNil
emptyLabelEnv ((e,_):>>>:env) = (e, mempty) :>>>: emptyLabelEnv env

getAllLabelsEnv :: LabelEnv env -> Labels
getAllLabelsEnv LabelEnvNil = mempty
getAllLabelsEnv ((_,set) :>>>: lenv) = set <> getAllLabelsEnv lenv

getLabelArgs :: Args env args -> LabelEnv env -> LabelArgs args
getLabelArgs ArgsNil _ = LabelArgsNil
getLabelArgs (arg :>: args) e = getLabelsArg arg e :>>: getLabelArgs args e

getLabelsArg :: Arg env t -> LabelEnv env -> Labels
getLabelsArg (ArgVar tup)                  env = getLabelsTup tup    env
getLabelsArg (ArgExp expr)                 env = getLabelsExp expr   env
getLabelsArg (ArgFun fun)                  env = getLabelsFun fun    env
getLabelsArg (ArgArray _ _ shVars bufVars) env = getLabelsTup shVars env <> getLabelsTup bufVars env

getLabelsTup :: TupR (Var a env) b -> LabelEnv env -> Labels
getLabelsTup TupRunit                     _   = mempty
getLabelsTup (TupRsingle var) env = getLabelsVar var env
getLabelsTup (TupRpair x y)               env = getLabelsTup x env <> getLabelsTup y env

getLabelsVar :: Var s env t -> LabelEnv env -> Labels
getLabelsVar (varIdx -> idx) = getLabelsIdx idx

getLabelsIdx :: Idx env a -> LabelEnv env -> Labels
getLabelsIdx ZeroIdx ((_,ls) :>>>: _) = ls
getLabelsIdx (SuccIdx idx) (_ :>>>: env) = getLabelsIdx idx env

getELabelIdx :: Idx env a -> LabelEnv env -> ELabel
getELabelIdx ZeroIdx ((e,_) :>>>: _) = e
getELabelIdx (SuccIdx idx) (_ :>>>: env) = getELabelIdx idx env

getLabelsExp :: OpenExp x env y -> LabelEnv env -> Labels
getLabelsExp = undefined -- TODO traverse everything, look for Idxs

getLabelsFun :: OpenFun x env y -> LabelEnv env -> Labels
getLabelsFun (Body expr) lenv = getLabelsExp expr lenv
getLabelsFun (Lam _ fun) lenv = getLabelsFun fun  lenv

updateLabelEnv :: Args env args -> LabelEnv env -> Label -> LabelEnv env
updateLabelEnv ArgsNil lenv _ = lenv
updateLabelEnv (arg :>: args) lenv l = case arg of
  -- CHECK we only look at the 'Buffer' vars here, not the 'shape' ones. Is that ok?
  ArgArray Out _ _ vars -> updateLabelEnv args (insertAtVars vars lenv l) l
  ArgArray Mut _ _ vars -> updateLabelEnv args (insertAtVars vars lenv l) l
  -- CHECK maybe we should also traverse the other args? Does LabelEnv need two sets of Labels (potentially fusible & infusible)?
  _ -> updateLabelEnv args lenv l

insertAtVars :: TupR (Var a env) b -> LabelEnv env -> Label -> LabelEnv env
insertAtVars TupRunit lenv _ = lenv
insertAtVars (TupRpair x y) lenv l = insertAtVars x (insertAtVars y lenv l) l
insertAtVars (TupRsingle (varIdx -> idx)) ((e,lset) :>>>: lenv) l = case idx of
  ZeroIdx -> (e, S.insert l lset) :>>>: lenv
  SuccIdx idx' ->       (e, lset) :>>>: insertAtVars (TupRsingle (Var undefined idx')) lenv l
insertAtVars (TupRsingle (varIdx -> idx)) LabelEnvNil _ = case idx of {} -- convincing the exhausiveness checker

-- | Like `getLabelArgs`, but ignores the `Out` arguments
getInputArgLabels :: Args env args -> LabelEnv env -> Labels
getInputArgLabels ArgsNil _ = mempty
getInputArgLabels (arg :>: args) lenv = getInputArgLabels args lenv <> case arg of
  ArgArray Out _ _ _ -> mempty
  _ -> getLabelsArg arg lenv
