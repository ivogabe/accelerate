{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE InstanceSigs        #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE PatternGuards       #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}
{-# LANGUAGE StandaloneDeriving       #-}
{-# LANGUAGE ViewPatterns        #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE InstanceSigs #-}
-- |
-- Module      : Data.Array.Accelerate.Pretty.Operation
-- Copyright   : [2008..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.Pretty.Partitioned ({- instance PrettyOp (Cluster op) -}) where

import Data.Array.Accelerate.Pretty.Exp hiding (Val(..), prj)
import qualified Data.Array.Accelerate.Pretty.Exp as Pretty
import Data.Array.Accelerate.Pretty.Type
import Data.Array.Accelerate.Pretty.Operation
import Data.Array.Accelerate.AST.Environment (Env)
import qualified Data.Array.Accelerate.AST.Environment as Env
import Data.Array.Accelerate.AST.Partitioned
import Data.Array.Accelerate.AST.LeftHandSide
import Data.Array.Accelerate.Type
import Data.Array.Accelerate.Trafo.Operation.LiveVars
import Data.Array.Accelerate.Error

import Prettyprinter

import Prelude hiding (exp)
import Data.Array.Accelerate.Representation.Type
import Data.Array.Accelerate.Representation.Shape
import Data.Array.Accelerate.Representation.Array
import Data.Array.Accelerate.AST.Idx (Idx (..))
import Data.Bifunctor (second)
import Data.Array.Accelerate.AST.Var (varsType)

instance (PrettyOp op, SetOpIndices op) => PrettyOp (Clustered op) where
  prettyOp :: PrettyOp op => Clustered op t -> Adoc
  prettyOp (Clustered c _) = prettyOp c
  prettyOpWithArgs env (Clustered c _) = prettyOpWithArgs env c

instance (PrettyOp op, SetOpIndices op) => PrettyOp (Cluster op) where
  prettyOp _ = "cluster"

  prettyOpWithArgs env cluster args
    {- = prettyFlatCluster env flat
    where
      flat = toFlatCluster cluster args-}
    | isSingle cluster = body
    | otherwise = annotate Execute "execute" <+> "{" <> line
      <> indent 2 body <> line <> "}"
    where
      body = fst $ prettyCluster True cluster (mapArgs (toPrettyArg env) args) 0

isSingle :: Cluster op t -> Bool
isSingle SingleOp{} = True
isSingle _ = False

data PrettyArg t where
  PrettyArgArray
    :: Modifier m
    -> Adoc -- shape variables
    -> TupR Adoc' (Buffers e) -- buffer variables
    -> PrettyArg (m sh e)

  PrettyArgVarShape
    :: Adoc -- Pretty printed as normal variables
    -> Adoc -- Pretty printed as shape
    -> PrettyArg t
  
  PrettyArgOther
    :: Adoc
    -> PrettyArg t

type PrettyArgs = PreArgs PrettyArg

newtype Adoc' t = Adoc' Adoc

prettyCluster :: Bool -> PrettyOp op => Cluster op t -> PrettyArgs t -> Int -> (Adoc, Int)
prettyCluster topLevel (SingleOp singleOp _) args fresh = (prettySingleOp topLevel singleOp args, fresh)
prettyCluster _ (Fused fusion left right) args fresh
  | (leftArgs, rightArgs, horizontals, verticals, diagonals, fresh') <- splitEnv fusion args fresh
  , (leftDoc, fresh'') <- prettyCluster False left leftArgs fresh'
  , (rightDoc, fresh''') <- prettyCluster False right rightArgs fresh''
  = ( leftDoc <> line <>
      prettyFuseList (annotate Statement "fused horizontally") horizontals <>
      prettyFuseList (annotate Statement "fused vertically") verticals <>
      prettyFuseList (annotate Statement "fused diagonally") diagonals <>
      rightDoc
    , fresh''')

prettySingleOp :: PrettyOp op => Bool -> SingleOp op t -> PrettyArgs t -> Adoc
prettySingleOp topLevel (Single op opArgs) args =
  hang 2 $ group $ vsep $
    [ annotate Execute "execute" | topLevel ]
    ++
    [
      prettyOp op,
      tupled $ map (\(Exists a) -> prettyPrettyArg $ prettyClusterArg args a) $ argsToList opArgs
    ]

prettyClusterArg :: forall f t. PrettyArgs f -> ClusterArg (FunToEnv f) t -> PrettyArg t
prettyClusterArg pArgs = \case
  ClusterArgSingle idx -> funToEnvPrj pArgs idx
  ClusterArgArray m _ _ buffers -> prettyBuffers m buffers
  where
    prettyBuffers :: Modifier m -> ClusterArgBuffers (FunToEnv f) m sh e -> PrettyArg (m sh e)
    prettyBuffers _ (ClusterArgBuffersDead _ idx) = case funToEnvPrj pArgs idx of
      PrettyArgVarShape _ sh ->
        PrettyArgArray Out sh (TupRsingle $ Adoc' "_")
      PrettyArgOther sh ->
        PrettyArgArray Out sh (TupRsingle $ Adoc' "_")
    prettyBuffers _ (ClusterArgBuffersLive _ idx) = funToEnvPrj pArgs idx
    prettyBuffers m (ClusterArgBuffersPair l r) = prettyBuffers m l `prettyPairArg` prettyBuffers m r

toPrettyArg :: Val env -> Arg env t -> PrettyArg t
toPrettyArg env (ArgArray m _ sh buffers) = PrettyArgArray m (prettyShapeVars env sh) (mapTupR (Adoc' . prettyVar env) buffers)
toPrettyArg env arg@(ArgVar vars)
  | Just _ <- typeShape $ varsType vars
  = PrettyArgVarShape (prettyArg env arg) (prettyShapeVars env vars)
toPrettyArg env arg = PrettyArgOther $ prettyArg env arg

prettyPrettyArg :: PrettyArg t -> Adoc
prettyPrettyArg (PrettyArgArray m sh buffers) = group $ vsep [prettyModifier m, "(" <> sh <> ")", prettyTupR (\_ (Adoc' doc) -> doc) 0 buffers]
prettyPrettyArg (PrettyArgVarShape doc _) = doc
prettyPrettyArg (PrettyArgOther doc) = doc

prettyPairArg :: PrettyArg (f left) -> PrettyArg (f right) -> PrettyArg (f (left, right))
prettyPairArg (PrettyArgArray m sh left) (PrettyArgArray _ _ right) = PrettyArgArray m sh $ TupRpair left right
prettyPairArg _ _ = PrettyArgOther "?"

splitEnv :: Fusion largs rargs t -> PrettyArgs t -> Int -> (PrettyArgs largs, PrettyArgs rargs, [Adoc], [Adoc], [Adoc], Int)
splitEnv EmptyF _ fresh = (ArgsNil, ArgsNil, [], [], [], fresh)
splitEnv (Vertical _ next) (a :>: as) fresh =
  let
    (left, right, horizontals, verticals, diagonals, fresh') = splitEnv next as (fresh + 1)
    sh = case a of
      PrettyArgVarShape _ sh' -> sh'
      _ -> "?"
    buffer = "%" <> viaShow fresh
    buffers = TupRsingle $ Adoc' buffer
  in
    ( PrettyArgArray Out sh buffers :>: left
    , PrettyArgArray In  sh buffers :>: right
    , horizontals
    , buffer : verticals
    , diagonals
    , fresh'
    )
splitEnv (Horizontal next) (a :>: as) fresh =
  let
    (left, right, horizontals, verticals, diagonals, fresh') = splitEnv next as fresh
    buffer = case a of
      PrettyArgArray _ _ (TupRsingle (Adoc' b)) -> b
      _ -> prettyPrettyArg a
  in
    ( a :>: left
    , a :>: right
    , buffer : horizontals
    , verticals
    , diagonals
    , fresh'
    )
splitEnv (Diagonal next) (a :>: as) fresh =
  let
    (left, right, horizontals, verticals, diagonals, fresh') = splitEnv next as fresh
    a' = case a of
      PrettyArgArray _ sh bs -> PrettyArgArray In sh bs
      _ -> PrettyArgOther "?"
    buffer = case a of
      PrettyArgArray _ _ (TupRsingle (Adoc' b)) -> b
      _ -> prettyPrettyArg a
  in
    ( a :>: left
    , a' :>: right
    , horizontals
    , verticals
    , buffer : diagonals
    , fresh'
    )
splitEnv (IntroI1 next) as fresh = splitEnv (IntroL next) as fresh
splitEnv (IntroO1 next) as fresh = splitEnv (IntroL next) as fresh
splitEnv (IntroI2 next) as fresh = splitEnv (IntroR next) as fresh
splitEnv (IntroO2 next) as fresh = splitEnv (IntroR next) as fresh
splitEnv (IntroL next) (a :>: as) fresh =
  let
    (left, right, horizontals, verticals, diagonals, fresh') = splitEnv next as fresh
  in
    (a :>: left, right, horizontals, verticals, diagonals, fresh')
splitEnv (IntroR next) (a :>: as) fresh =
  let
    (left, right, horizontals, verticals, diagonals, fresh') = splitEnv next as fresh
  in
    (left, a :>: right, horizontals, verticals, diagonals, fresh')

prettyFuseList :: Adoc -> [Adoc] -> Adoc
prettyFuseList _ [] = ""
prettyFuseList name docs = (hang 2 $ group $ vsep $ [name, tupled docs]) <> line

prettyFlatCluster :: PrettyOp op => Val env -> FlatCluster op env -> Adoc
prettyFlatCluster env (FlatCluster _ idxLhs sizes directions localR localLHS ops) =
  annotate Execute "execute" <+> "{" <> line
    <> indent 2 (forIndices <> localBuffers <> vsep ops') <> line <> "}"
  where
    (forIndices, idxEnv, _) = prettyIdxLHS env Pretty.Empty 0 idxLhs sizes directions
    (env', _) = pushLocalBuffers env 0 localLHS
    (localBuffers, _) = prettyLocalLHS 0 localLHS localR
    ops' = prettyFlatOps False env' idxEnv ops

prettyIdxLHS :: Val env0 -> Val env -> Int -> ELeftHandSide sh env env' -> GroundVars env0 sh -> TupR LoopDirection sh -> (Adoc, Val env', Int)
prettyIdxLHS _ env fresh (LeftHandSideWildcard _) _ _ = (mempty, env, fresh)
prettyIdxLHS env0 env fresh (LeftHandSideSingle _) (TupRsingle sz) (TupRsingle direction) =
  (doc, env `Pretty.Push` var, fresh + 1)
  where
    doc = for_ <+> var <+> in_ <+> "0 .. " <> prettyVar env0 sz <> direction' <> hardline
    var = "i" <> viaShow fresh
    direction' = case direction of
      LoopAny -> mempty
      LoopMonotone -> " [monotone]"
      LoopAscending -> " [ascending]"
      LoopDescending -> " [descending]"
prettyIdxLHS env0 env fresh (LeftHandSidePair lhs1 lhs2) (TupRpair sz1 sz2) (TupRpair d1 d2)
  | (doc1, env1, fresh1) <- prettyIdxLHS env0 env fresh lhs1 sz1 d1
  , (doc2, env2, fresh2) <- prettyIdxLHS env0 env1 fresh1 lhs2 sz2 d2
  = (doc1 <> doc2, env2, fresh2)
prettyIdxLHS _ _ _ _ _ _ = internalError "Tuple mismatch"

pushLocalBuffers :: Val env -> Int -> GLeftHandSide t env env' -> (Val env', Int)
pushLocalBuffers env fresh (LeftHandSideWildcard _) = (env, fresh)
pushLocalBuffers env fresh (LeftHandSideSingle _) =
  (env `Pretty.Push` ("%" <> viaShow fresh), fresh + 1)
pushLocalBuffers env fresh (LeftHandSidePair lhs1 lhs2)
  | (env', fresh') <- pushLocalBuffers env fresh lhs1
  = pushLocalBuffers env' fresh' lhs2

prettyLocalLHS :: Int -> GLeftHandSide t env env' -> TupR LocalBufferR t -> (Adoc, Int)
prettyLocalLHS fresh (LeftHandSideWildcard _) _ = (mempty, fresh)
prettyLocalLHS fresh (LeftHandSideSingle _) (TupRsingle (LocalBufferR tp depth)) =
  ( let_ <> " %" <> viaShow fresh <> ": [" <> prettyScalarType tp <> "] " <> comment <> hardline
  , fresh + 1)
  where
    comment
      | depth == 0 = "-- outside for loops"
      | otherwise = "-- in for i" <> viaShow (depth - 1)
prettyLocalLHS fresh (LeftHandSidePair lhs1 lhs2) (TupRpair r1 r2)
  | (d1, fresh1) <- prettyLocalLHS fresh lhs1 r1
  , (d2, fresh2) <- prettyLocalLHS fresh1 lhs2 r2
  = (d1 <> d2, fresh2)
prettyLocalLHS _ _ _ = internalError "Tuple mismatch"

prettyFlatOps :: PrettyOp op => Bool -> Val env -> Val idxEnv -> FlatOps op env idxEnv -> [Adoc]
prettyFlatOps single env idxEnv = \case
  FlatOpsNil -> []
  FlatOpsOp op ops ->
    prettyFlatOp single env idxEnv op : prettyFlatOps single env idxEnv ops
  FlatOpsBind depth lhs expr ops
    | (idxEnv', lhs') <- prettyLhs False 'i' idxEnv lhs ->
      ( ( if depth == 0
          then "-- Backpermute outside all for loops"
          else "-- Backpermute in for loop of i" <> viaShow (depth - 1) <> hardline)
        <> let_ <+> lhs' <+> "=" <+> prettyPreOpenExp context0 (prettyArrayInstr env) idxEnv expr)
      : prettyFlatOps single env idxEnv' ops

prettyFlatOp :: PrettyOp op => Bool -> Val env -> Val idxEnv -> FlatOp op env idxEnv -> Adoc
prettyFlatOp single env idxEnv (FlatOp op args idxArgs) =
  hang 2 $ group $ vsep $
    [ annotate Execute "execute" | single ]
    ++
    [
      prettyOp op,
      tupled $ prettyArgsWithIdx env idxEnv args idxArgs
    ]

prettyArgsWithIdx :: Val env -> Val idxEnv -> Args env args -> IdxArgs idxEnv args -> [Adoc]
prettyArgsWithIdx _ _ ArgsNil _ = []
prettyArgsWithIdx env idxEnv (a :>: as) (i :>: is)
  = prettyArgWithIdx env idxEnv a i : prettyArgsWithIdx env idxEnv as is

prettyArgWithIdx :: Val env -> Val idxEnv -> Arg env arg -> IdxArg idxEnv arg -> Adoc
prettyArgWithIdx env idxEnv arg idxArg
  | ArgArray{} <- arg = case idxArg of
    IdxArgIdx depth idx ->
      let
        idx' = map (\(Exists var) -> prettyVar idxEnv var) $ flattenTupR idx
        comment
          | depth == 0 = "{- outside for loops -}"
          | otherwise = "{- in for i" <> viaShow (depth - 1) <> " -}"
      in arg' <> " @ " <> tupled idx' <+> comment
    IdxArgNone -> arg' <> " @ ?"
  | otherwise = arg'
  where
    arg' = prettyArg env arg
