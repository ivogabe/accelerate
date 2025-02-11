{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE StandaloneDeriving #-}
module Data.Array.Accelerate.Trafo.Partitioning.ILP.Labels where


-- accelerate imports
import Data.Array.Accelerate.AST.Idx
import Data.Array.Accelerate.AST.LeftHandSide ( LeftHandSide(..) )
import Data.Array.Accelerate.AST.Operation
import Data.Array.Accelerate.Representation.Type
import Data.Array.Accelerate.Type
import Data.Array.Accelerate.Array.Buffer (Buffer, Buffers)
import Data.Array.Accelerate.Representation.Array
import Data.Array.Accelerate.Error

-- In this file, order very often subly does matter.
-- To keep this clear, we use S.Set whenever it does not,
-- and [] only when it does. It's also often efficient
-- by removing duplicates.
import qualified Data.Set as S

import Lens.Micro.TH ( makeLenses )
import Control.Monad.State ( (>=>), State )
import Lens.Micro.Mtl ((<%=))
import qualified Data.Map as M
import Lens.Micro ((^.))
import Data.Bifunctor (first)
import Data.Type.Equality
import qualified Data.Functor.Const as C
import qualified Debug.Trace

{-
Label is for each AST node: every exec, every let, every branch of control flow, etc has a unique label.
Edge is a dependency between Labels

ELabel is for Environments: the environment consists of array-level and expression-level values,
we give each value a unique ELabel. This helps to re-index AST nodes and expressions and args into the new environment,
provided that we have a LabelEnv with matching ELabels. We accomplish this by storing 'MyLHS's that contain ELabels, inside of Construction.

LabelEnv also has a S.Set Label for each value, denoting the current outgoing edges from that value: This is volatile information, while all the rest is static.

LabelArgs is the same as LabelEnv, except it is bound to Args. The ELabels in here point to the ELabels in Env
-}




-- identifies nodes with unique Ints. and tracks their dependencies
-- `Label x Nothing` means that label x is top-level.
-- `Label x (Just y)` means that label x is (at ilp-construction time determined to be) a subcomputation of label y
-- Invariant: for all x, there is at most one `Label x _`: the second field is not to discriminate vars but to log extra information.
data Label = Label
  { _labelId :: Int
  , _parent :: Maybe Label
  } -- deriving Show
makeLenses ''Label
instance Show Label where
  -- show = ("Label"<>) . show . _labelId
  show (Label i p) = "L" <> show i <> "{" <> show p <> "} "
instance Eq Label where
  (Label x a) == (Label y b)
    | x == y = if a == b then True else error $ "same labelId but different parents: " <> show x <> show a <> " - " <> show b
    | otherwise = False
deriving instance Ord Label

level :: Label -> Int
level (Label _ Nothing)  = 0
level (Label _ (Just l)) = 1 + level l

type Labels = S.Set Label
type ELabels = (ELabel, Labels)
type ELabelTup = TupR (C.Const ELabel)
data ALabel t where
  Arr :: ELabelTup e -- elabel of buffer
      -> ALabel (m sh e) -- only matches on arrays, but supports In, Out and Mut
  NotArr :: ALabel (t e) -- matches on `Var' e`, `Exp' e` and `Fun' e` (is typecorrect on arrays, but wish it wasn't)
deriving instance Show (ALabel t)

type ALabels t = (ALabel t, Labels) -- An ELabel if it corresponds to an array, otherwise Nothing

-- Map identifiers to labels
labelMap :: S.Set Label -> M.Map Int Label
  -- TODO once it works, test M.fromDistinctAscList
labelMap = M.fromList . map (\l -> (l^.labelId, l)) . S.toAscList

-- identifies elements of the environment with unique Ints.
newtype ELabel = ELabel { runELabel :: Int }
  deriving (Show, Eq, Ord, Num)

-- | Keeps track of which argument belongs to which labels
data LabelledArg  env a = L (Arg env a) (ALabels a)
type LabelledArgs env = PreArgs (LabelledArg env)

-- instance Show (LabelledArgs env args) where 
--   show ArgsNil = "ArgsNil"
--   show (L arg a :>: args) = "L " ++ x ++ " " ++ show a ++ " :>: " ++ show args
--     where x = case arg of
--             ArgVar tr -> "Var"
--             ArgExp poe -> "Exp"
--             ArgFun pof -> "Fun"
--             ArgArray mod ar tr tr' -> "Arr"


-- instance Semigroup (LabelledArgs env args) where
--   ArgsNil <> ArgsNil = ArgsNil
--   -- TODO why am I perfectly fine with <> on an Arr with a NotArr?
--   (arg `L` (NotArr,l1)):>:largs1 <> (_ `L` (larg,   l2)):>:largs2 = arg `L` (larg, l1<>l2) :>: (largs1 <> largs2)
--   (arg `L` (larg,  l1)):>:largs1 <> (_ `L` (NotArr, l2)):>:largs2 = arg `L` (larg, l1<>l2) :>: (largs1 <> largs2)
--   _ <> _ = error "mappend for LabelArgs found two Arr labels"

unLabel :: LabelledArgs env args -> Args env args
unLabel ArgsNil              = ArgsNil
unLabel (arg `L` _ :>: args) = arg :>: unLabel args

reindexLabelledArg :: Applicative f => ReindexPartial f env env' -> LabelledArg env t -> f (LabelledArg env' t)
reindexLabelledArg k (ArgVar vars                `L` l) = (`L` l)  .   ArgVar          <$> reindexVars k vars
reindexLabelledArg k (ArgExp e                   `L` l) = (`L` l)  .   ArgExp          <$> reindexExp k e
reindexLabelledArg k (ArgFun f                   `L` l) = (`L` l)  .   ArgFun          <$> reindexExp k f
reindexLabelledArg k (ArgArray m repr sh buffers `L` l) = (`L` l) <$> (ArgArray m repr <$> reindexVars k sh <*> reindexVars k buffers)

reindexLabelledArgs :: Applicative f => ReindexPartial f env env' -> LabelledArgs env t -> f (LabelledArgs env' t)
reindexLabelledArgs = reindexPreArgs reindexLabelledArg


-- | Keeps track of which array in the environment belongs to which label
data LabelEnv env where
  LabelEnvNil :: LabelEnv ()
  (:>>:)      :: ELabels -> LabelEnv t -> LabelEnv (t, s)
instance Semigroup (LabelEnv env) where
  LabelEnvNil <> LabelEnvNil = LabelEnvNil
  (e1,l1):>>:lenv1 <> (e2,l2):>>:lenv2
    | e1 == e2 = (e1, l1<>l2) :>>: (lenv1 <> lenv2)
    | otherwise = error "mappend for LabelEnv found two different labels"

instance Show (LabelEnv env) where
  show LabelEnvNil = "LabelEnvNil"
  show (e :>>: env) = show e ++ " :>>: " ++ show env


freshE' :: State ELabel ELabel
freshE' = id <%= (+1)


-------------------------------
-- Traversals over stuff to add/extract Labels and ELabels,
-- or otherwise manipulate LabelArgs' or LabelEnvs


-- | Note that this throws some info away: Pair (Wildcard, Single) and Pair (Single, Wildcard) give identical results.
-- Use sites need to store a LHS too.
addLhs :: LeftHandSide s v env env' -> Labels -> LabelEnv env -> State ELabel (LabelEnv env')
addLhs LeftHandSideWildcard{} _ = pure
addLhs LeftHandSideSingle{}   l = \lenv -> freshE' >>= \e -> pure ((e, l) :>>: lenv)
addLhs (LeftHandSidePair x y) l = addLhs x l >=> addLhs y l


weakLhsEnv :: LeftHandSide s v env env' -> LabelEnv env' -> LabelEnv env
weakLhsEnv LeftHandSideSingle{} (_:>>: env) = env
weakLhsEnv LeftHandSideWildcard{} env = env
weakLhsEnv (LeftHandSidePair l r) env = weakLhsEnv l (weakLhsEnv r env)

emptyLabelEnv :: LabelEnv env -> LabelEnv env
emptyLabelEnv LabelEnvNil = LabelEnvNil
emptyLabelEnv ((e,_):>>:env) = (e, mempty) :>>: emptyLabelEnv env

getAllLabelsEnv :: LabelEnv env -> Labels
getAllLabelsEnv LabelEnvNil = mempty
getAllLabelsEnv ((_,set) :>>: lenv) = set <> getAllLabelsEnv lenv

getLabelArgs :: Args env args -> LabelEnv env -> LabelledArgs env args
getLabelArgs ArgsNil _ = ArgsNil
getLabelArgs (arg :>: args) e = arg `L` getLabelsArg arg e :>: getLabelArgs args e

getLabelsArg :: Arg env t -> LabelEnv env -> ALabels t
getLabelsArg (ArgVar tup)                  env = first (const NotArr) (getLabelsTup tup env)
getLabelsArg (ArgExp expr)                 env = getLabelsExp expr   env
getLabelsArg (ArgFun fun)                  env = getLabelsFun fun    env
-- TODO this gets us the singleton label assigned to the buffer, check whether this doesn't make us use/write an array before we know its size
-- honestly, this just doesn't cut it. Need a better way to both label arguments (for reconstruction later) and track dependencies (for ILP solving),
-- using this one S.Set for both conflicts (as seen in 'const' vs 'insert')

-- The comment above is outdated, but I'm not sure what is going on here anymore. What are the two types of return arguments from getLabelsTup? Does it make sense that a TupRsingle always gives Right?
-- ALabels shouldn't contain a single ELabel for arrays, but a TupR of ELabels (one for each buffer)!

-- another update: adding the labels from the shapes now, and I see that there are tupr's of elabs already.
-- Maybe we should only return the sh labels for input arrays?
getLabelsArg (ArgArray _ (ArrayR _ tp) shVars buVars) env =
  let
    (Arr x,             buLabs         ) = getLabelsTup buVars env
    (Arr y,                      shLabs) = getLabelsTup shVars env
  in ( --Debug.Trace.trace ("\n\ngetLabelsArg: buffer alabel:" <> show x <> "\nshape alabel:" <> show y <> "\nbuf labels:" <> show buLabs <> "\nshape labels:" <> show shLabs) $ 
    unBuffers tp $ Arr x, buLabs <> shLabs)

getLabelsTup :: TupR (Var a env) b -> LabelEnv env -> ALabels (m sh b)
getLabelsTup TupRunit         _   = (Arr TupRunit, mempty)
getLabelsTup (TupRsingle var) env = getLabelsVar var env
getLabelsTup (TupRpair l r) env = let
  (Arr l', lset) = getLabelsTup l env
  (Arr r', rset) = getLabelsTup r env
  in (Arr $ TupRpair l' r', lset <> rset)
-- getLabelsTup (TupRsingle var) env = Right $ getLabelsVar var env
-- getLabelsTup (TupRpair x y)   env = case (getLabelsTup x env, getLabelsTup y env) of
--   (Left  (_, a), Left  (_, b)) -> Left (NotArr, a <> b)
--   (Left  (_, a), Right (Arr z, b)) -> Right (Arr z, a <> b)
--   (Right (Arr z, a), Left  (_, b)) -> Right (Arr z, a <> b)
--   (Right (_, a), Right (_, b)) -> Left (NotArr, a <> b)
--   _ -> error "who?"


getLabelsVar :: Var s env t -> LabelEnv env -> ALabels (m sh t)
getLabelsVar (varIdx -> idx) = getLabelsIdx idx

getLabelsIdx :: Idx env a -> LabelEnv env -> ALabels (m sh a)
getLabelsIdx ZeroIdx (el :>>: _) = first (Arr . TupRsingle . C.Const) el
getLabelsIdx (SuccIdx idx) (_ :>>: env) = getLabelsIdx idx env

getELabelIdx :: Idx env a -> LabelEnv env -> ELabel
getELabelIdx ZeroIdx ((e,_) :>>: _) = e
getELabelIdx (SuccIdx idx) (_ :>>: env) = getELabelIdx idx env

-- recurses through, only does interesting stuff at ArrayInstructions (first two cases)
getLabelsExp :: OpenExp x env y -> LabelEnv env -> ALabels (Exp' y)
getLabelsExp (ArrayInstr (Index var) poe') env     = let (_, a) = getLabelsVar var env
                                                         (NotArr, b) = getLabelsExp poe' env
                                                     in  (NotArr, a <> b)
getLabelsExp (ArrayInstr (Parameter var) poe') env = let (_, a) = getLabelsVar var env
                                                         (NotArr, b) = getLabelsExp poe' env
                                                     in  (NotArr, a <> b)
getLabelsExp (Let _ poe' poe2) env                 = let (NotArr, a) = getLabelsExp poe' env
                                                         (NotArr, b) = getLabelsExp poe2 env
                                                     in  (NotArr, a <> b)
getLabelsExp (Evar _) _                            = (NotArr, mempty)
getLabelsExp Foreign{} _                           = (NotArr, mempty) -- TODO the fallback can't do indexing, ignoring the foreign
getLabelsExp (Pair poe' poe2) env                  = let (NotArr, a) = getLabelsExp poe' env
                                                         (NotArr, b) = getLabelsExp poe2 env
                                                     in  (NotArr, a <> b)
getLabelsExp Nil _                                 = (NotArr, mempty)
getLabelsExp (VecPack _ poe') env                  = first (\NotArr -> NotArr) $ getLabelsExp poe' env
getLabelsExp (VecUnpack _ poe') env                = first (\NotArr -> NotArr) $ getLabelsExp poe' env
getLabelsExp (IndexSlice _ poe' poe2) env   = let (NotArr, a) = getLabelsExp poe' env
                                                  (NotArr, b) = getLabelsExp poe2 env
                                              in  (NotArr, a <> b)
getLabelsExp (IndexFull _ poe' poe2) env    = let (NotArr, a) = getLabelsExp poe' env
                                                  (NotArr, b) = getLabelsExp poe2 env
                                              in  (NotArr, a <> b)
getLabelsExp (ToIndex _ poe' poe2) env      = let (NotArr, a) = getLabelsExp poe' env
                                                  (NotArr, b) = getLabelsExp poe2 env
                                              in  (NotArr, a <> b)
getLabelsExp (FromIndex _ poe' poe2) env    = let (NotArr, a) = getLabelsExp poe' env
                                                  (NotArr, b) = getLabelsExp poe2 env
                                              in  (NotArr, a <> b)
getLabelsExp (Case poe' x0 Nothing) env     = let (NotArr, a) = foldr (\((`getLabelsExp` env) . snd -> (NotArr, c)) (NotArr, d) -> (NotArr, c <> d))
                                                                      (NotArr, mempty)
                                                                      x0
                                                  (NotArr, b) = getLabelsExp poe' env
                                              in  (NotArr, a <> b)
getLabelsExp (Case poe' x0 (Just poe)) env  = let (NotArr, a) = getLabelsExp (Case poe' x0 Nothing) env
                                                  (NotArr, b) = getLabelsExp poe env
                                              in  (NotArr, a <> b)
getLabelsExp (Cond poe' poe2 poe3) env      = let (NotArr, a) = getLabelsExp poe' env
                                                  (NotArr, b) = getLabelsExp poe2 env
                                                  (NotArr, c) = getLabelsExp poe3 env
                                              in  (NotArr, a <> b <> c)
getLabelsExp (While pof pof' poe') env      = let (NotArr, a) = getLabelsFun pof env
                                                  (NotArr, b) = getLabelsFun pof' env
                                                  (NotArr, c) = getLabelsExp poe' env
                                              in  (NotArr, a <> b <> c)
getLabelsExp (Const _ _) _                  = (NotArr, mempty)
getLabelsExp (PrimConst _) _                = (NotArr, mempty)
getLabelsExp (PrimApp _ poe') env           = first (\NotArr -> NotArr) $ getLabelsExp poe' env
getLabelsExp (ShapeSize _ poe') env         = first (\NotArr -> NotArr) $ getLabelsExp poe' env
getLabelsExp (Undef _) _                    = (NotArr, mempty)
getLabelsExp Coerce {} _                    = (NotArr, mempty)

getLabelsFun :: OpenFun x env y -> LabelEnv env -> ALabels (Fun' y)
getLabelsFun (Body expr) lenv = first body $ getLabelsExp expr lenv
getLabelsFun (Lam _ fun) lenv = first lam  $ getLabelsFun fun  lenv

-- | Replaces the labelset associated with the buffers of out-args with `S.singleton l`.
updateLabelEnv :: Args env args -> LabelEnv env -> Label -> LabelEnv env
updateLabelEnv ArgsNil lenv _ = lenv
updateLabelEnv (arg :>: args) lenv l = case arg of
  -- We only look at the 'Buffer' vars here, not the 'shape' ones.
  ArgArray Out _ _ vars -> updateLabelEnv args (insertAtVars vars lenv $ const $ S.singleton l) l
  ArgArray Mut _ _ vars -> updateLabelEnv args (insertAtVars vars lenv $ const $ S.singleton l) l
  _ -> updateLabelEnv args lenv l

-- Updates the labels with a function. Currently, this is always `const (S.singleton l)`
insertAtVars :: TupR (Var a env) b -> LabelEnv env -> (Labels -> Labels) -> LabelEnv env
insertAtVars TupRunit lenv _ = lenv
insertAtVars (TupRpair x y) lenv f = insertAtVars x (insertAtVars y lenv f) f
insertAtVars (TupRsingle (Var t idx)) ((e,lset) :>>: lenv) f = case idx of
  ZeroIdx -> (e, f lset) :>>: lenv
  SuccIdx idx' ->       (e, lset) :>>: insertAtVars (TupRsingle (Var t idx')) lenv f
insertAtVars (TupRsingle (Var _ idx)) LabelEnvNil _ = case idx of VoidIdx x -> x -- convincing the pattern coverage checker of the impossible case

-- | Like `getLabelArgs`, but ignores the `Out` arguments
getInputArgLabels :: Args env args -> LabelEnv env -> Labels
getInputArgLabels ArgsNil _ = mempty
getInputArgLabels (arg :>: args) lenv = getInputArgLabels args lenv <> case arg of
  ArgArray Out _ _ _ -> mempty
  _ -> snd $ getLabelsArg arg lenv

getOutputArgLabels :: Args env args -> LabelEnv env -> Labels
getOutputArgLabels ArgsNil _ = mempty
getOutputArgLabels (arg :>: args) lenv = getOutputArgLabels args lenv <> case arg of
  ArgArray In _ _ _ -> mempty
  _ -> snd $ getLabelsArg arg lenv


body :: ALabel (Exp' e) -> ALabel (Fun' e)
body NotArr = NotArr
lam  :: ALabel (Fun' f) -> ALabel (Fun' (e->f))
lam  NotArr = NotArr

unBuffers :: forall m sh e. TypeR e -> ALabel (m sh (Buffers e)) -> ALabel (m sh e)
unBuffers TupRunit _ = Arr TupRunit
unBuffers (TupRsingle t) (Arr (TupRsingle (C.Const e)))
  | Refl <- reprIsSingle @ScalarType @e @Buffer t
   = Arr (TupRsingle $ C.Const e)
unBuffers (TupRpair t1 t2) (Arr (TupRpair l r))
  | Arr l' <- unBuffers t1 (Arr l)
  , Arr r' <- unBuffers t2 (Arr r)
  = Arr (TupRpair l' r')
unBuffers _ (Arr _) = internalError "Tuple mismatch"
unBuffers _ _ = internalError "Not an array"
