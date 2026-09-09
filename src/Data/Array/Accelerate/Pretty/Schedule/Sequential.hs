{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE MonoLocalBinds      #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
-- |
-- Module      : Data.Array.Accelerate.Pretty.Schedule.Sequential
-- Copyright   : [2008..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.Pretty.Schedule.Sequential (

) where

import Data.Array.Accelerate.Pretty.Exp
import Data.Array.Accelerate.Pretty.Type
import Data.Array.Accelerate.Pretty.Schedule
import Data.Array.Accelerate.AST.Kernel
import Data.Array.Accelerate.AST.LeftHandSide
import Data.Array.Accelerate.AST.Schedule.Sequential
import Data.Array.Accelerate.Pretty.Operation
import Data.Array.Accelerate.Representation.Type

import Prettyprinter

import Prelude hiding (exp)

instance PrettySchedule SequentialSchedule where
  prettySchedule = prettySequentialSchedule empty'

prettySequentialSchedule :: PrettyKernel kernel => Val' env -> SequentialSchedule kernel env t -> Adoc
prettySequentialSchedule env (SequentialLam lhs f)
  | (env', lhs') <- prettyGLhsWithTypes env lhs
  = "\\" <> lhs' <+> "->" <> hardline <> indent 2 (prettySequentialSchedule env' f)
prettySequentialSchedule env (SequentialBody sched)
  = prettySeqSchedule env sched

prettySeqScheduleFun :: PrettyKernel kernel => Val' env -> SeqScheduleFun kernel env t -> Adoc
prettySeqScheduleFun env (Slam lhs f)
  | (env', lhs') <- prettyGLhsWithTypes env lhs
  = "\\" <> lhs' <+> "->" <> hardline <> indent 2 (prettySeqScheduleFun env' f)
prettySeqScheduleFun env (Sbody sched)
  = prettySeqSchedule env sched

prettySeqSchedule :: forall kernel env t. PrettyKernel kernel => Val' env -> SeqSchedule kernel env t -> Adoc
prettySeqSchedule env = \case
  Exec _ kernel args -> prettyKernelFun env kernel args
  Return vars -> hang 2 $ group $ vsep [annotate Statement "return", prettyVars (val env) 10 vars]
  Compute exp -> hang 2 $ group $ vsep [annotate Statement "compute", prettyExp (val env) exp]
  Alet LeftHandSideUnit _ bnd body
    | notReturn bnd
    -- A return looks very strange if there is no explict LHS. It's uncommon,
    -- but also very strange when this does happens.
    -> prettySeqSchedule env bnd
        <> hardline
        <> prettySeqSchedule env body
  Alet lhs us bnd body
    | (env', lhs') <- prettyGLhsWithUniquenessTypes env lhs us
      -> hang 2 (group $ vsep [lhs' <+> "=", prettySeqSchedule env bnd])
         <> hardline
         <> prettySeqSchedule env' body
  Alloc _ tp sh -> hang 2 $ group $ vsep [annotate Statement "alloc", prettyScalarType tp <> "[" <> prettyShapeVars (val env) sh <> "]"]
  Use tp n buffer -> hang 2 $ group $ vsep [annotate Statement "use" <+> prettyScalarType tp <> "[" <> pretty n <> "]", prettyBuffer tp n buffer]
  Unit var -> hang 2 $ group $ vsep [annotate Statement "unit", prettyVar (val env) var]
  Acond c true false
    -> group $ vsep
        [ hang 2 $ group $ vsep
          [ if_ <+> prettyVar (val env) c <+> then_
          , prettySeqSchedule env true
          ]
        , hang 2 $ group $ vsep
          [ else_
          , prettySeqSchedule env false
          ]
        ]
  Awhile us condition step initial
    -> annotate Statement "awhile" <+> prettyTupR (const prettyGroundRWithUniqueness) 10 (groundsRWithUniquenesses (mapTupR varType initial) us)
        <> hardline <> hang 4 ("  ( " <> prettySeqScheduleFun env condition)
        <> hardline <> "  )"
        <> hardline <> hang 4 ("  ( " <> prettySeqScheduleFun env step)
        <> hardline <> "  )"
        <> hardline <> indent 2 (prettyVars (val env) 10 initial)
  Aassert msg cond
    -> hang 2 $ group $ vsep [annotate Statement "assert", prettyText msg, prettyExp (val env) cond]
  Aassume cond
    -> hang 2 $ group $ vsep [annotate Statement "assume", prettyExp (val env) cond]
  where
    notReturn Return{} = False
    notReturn _        = True

prettySArgs :: Val' benv -> SArgs benv f -> Adoc
prettySArgs env args = tupled $ map (\(Exists a) -> prettySArg env a) $ argsToList args

prettySArg :: Val' benv -> SArg benv t -> Adoc
prettySArg env (SArgScalar var)   = prettyVar (val env) var
prettySArg env (SArgBuffer m var) = prettyModifier m <+> prettyVar (val env) var

prettyKernelFun :: forall kernel env f. PrettyKernel kernel => Val' env -> KernelFun kernel f -> SArgs env f -> Adoc
prettyKernelFun env fun args = case prettyKernel of
  PrettyKernelBody includeModifier prettyKernelBody ->
    let
      go :: Val kenv -> OpenKernelFun kernel kenv t -> SArgs env t -> Adoc
      go kenv (KernelFunBody kernel) ArgsNil = prettyKernelBody kenv kernel
      go kenv (KernelFunLam (KernelArgRscalar _) f) (SArgScalar a :>: as)
        = go (Push kenv $ prettyVar (val env) a) f as
      go kenv (KernelFunLam (KernelArgRbuffer _ _) f) (SArgBuffer mod' a :>: as) =
        let
          a'
            | includeModifier = prettyModifier mod' <+> prettyVar (val env) a
            | otherwise       = prettyVar (val env) a
        in
          go (Push kenv a') f as
    in
      go Empty fun args
  PrettyKernelFun prettyKernelAsFun ->
    prettyKernelAsFun fun
      <> hardline <> indent 2 (prettySArgs env args)
