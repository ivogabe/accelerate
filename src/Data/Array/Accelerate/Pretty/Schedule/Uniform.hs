{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE MonoLocalBinds      #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
-- |
-- Module      : Data.Array.Accelerate.Pretty.Schedule.Uniform
-- Copyright   : [2008..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.Pretty.Schedule.Uniform (
  prettySArg, prettySArgs, prettyKernelFun
) where

import Data.Array.Accelerate.Pretty.Exp
import Data.Array.Accelerate.Pretty.Type
import Data.Array.Accelerate.Pretty.Schedule
import Data.Array.Accelerate.Pretty.Operation (prettyGroundR, prettyBuffer, prettyExp, prettyModifier)
import Data.Array.Accelerate.AST.Idx
import Data.Array.Accelerate.AST.Kernel
import Data.Array.Accelerate.AST.LeftHandSide
import Data.Array.Accelerate.AST.Schedule.Uniform
import Data.Array.Accelerate.Representation.Type
import Data.Array.Accelerate.Representation.Shape
import Data.Array.Accelerate.Type
import Data.String

import Prettyprinter

import Prelude hiding (exp)

instance PrettySchedule UniformScheduleFun where
  prettySchedule = prettyUniformScheduleFun empty'

prettyBaseR :: BaseR t -> Adoc
prettyBaseR (BaseRground ground)   = prettyGroundR ground
prettyBaseR (BaseRref ground)      = "*" <> prettyGroundR ground
prettyBaseR (BaseRrefWrite ground) = "*out " <> prettyGroundR ground
prettyBaseR BaseRsignal            = "Signal"
prettyBaseR BaseRsignalResolver    = "Resolver"

-- Naming:
-- * We use 'b' and 'e' as prefix for buffer and scalar variables, like we also
--   do in the pretty printer for OperationAcc.
-- * We use 's' as a prefix for signal and signal resolvers. For the latter we
--   also append a prime (').
-- * We use 'r' as a prefix for references and writable references. For the
--   latter we append a prime (').
-- * We use the same index for a signal and a signal resolver if they are
--   introduced in a NewSignal. Similarly, we use the same indices for a
--   reference and a writable reference if they were introduced by a
--   NewRef
data Val' env = Val' (Val env) Int Int Int Int

val :: Val' env -> Val env
val (Val' env _ _ _ _) = env

push :: BaseR t -> Val' env -> (Val' (env, t), Adoc)
push (BaseRground GroundRbuffer{}) (Val' env b e s r) = (Val' (Push env d) (b + 1) e s r, d)
  where d = "b" <> pretty b
push (BaseRground GroundRscalar{}) (Val' env b e s r) = (Val' (Push env d) b (e + 1) s r, d)
  where d = "e" <> pretty e
push BaseRsignal                   (Val' env b e s r) = (Val' (Push env d) b e (s + 1) r, d)
  where d = "s" <> pretty s
push BaseRsignalResolver           (Val' env b e s r) = (Val' (Push env d) b e (s + 1) r, d)
  where d = "s" <> pretty s <> "'"
push BaseRref{}                    (Val' env b e s r) = (Val' (Push env d) b e s (r + 1), d)
  where d = "r" <> pretty r
push BaseRrefWrite{}               (Val' env b e s r) = (Val' (Push env d) b e s (r + 1), d)
  where d = "r" <> pretty r <> "'"

pushNewSignal :: Val' env -> (Val' ((env, Signal), SignalResolver), Adoc, Adoc)
pushNewSignal (Val' env b e s r) = (Val' (Push (Push env d1) d2) b e (s + 1) r, d1, d2)
  where
    d1 = "s" <> pretty s
    d2 = "s" <> pretty s <> "'"

pushNewRef :: Val' env -> (Val' ((env, Ref t), OutputRef t), Adoc, Adoc)
pushNewRef (Val' env b e s r) = (Val' (Push (Push env d1) d2) b e s (r + 1), d1, d2)
  where
    d1 = "r" <> pretty r
    d2 = "r" <> pretty r <> "'"

prettyBLhs :: Val' env -> BLeftHandSide t env env' -> (Val' env', Adoc)
prettyBLhs = prettyLhs' push Nothing False

prettyBLhsWithTypes :: Val' env -> BLeftHandSide t env env' -> (Val' env', Adoc)
prettyBLhsWithTypes = prettyLhs' push (Just $ \(Exists t) -> prettyBaseR t) False

prettyBLhsForBinding :: Val' env -> BLeftHandSide t env env' -> Binding env t -> (Val' env', Adoc)
prettyBLhsForBinding env (LeftHandSideSingle _ `LeftHandSidePair` LeftHandSideSingle _) binding
  | NewSignal _ <- binding
  , (env', a, b) <- pushNewSignal env = (env', pair a b)
  | NewRef _  <- binding
  , (env', a, b) <- pushNewRef    env = (env', pair a b)
  where pair a b = "(" <> a <> "," <+> b <> ")"
prettyBLhsForBinding env lhs binding
  | bindingHasTrivialType binding = prettyBLhs env lhs
  | otherwise = prettyBLhsWithTypes env lhs

bindingHasTrivialType :: Binding env t -> Bool
bindingHasTrivialType (NewSignal _) = True
bindingHasTrivialType (NewRef _)    = True
bindingHasTrivialType (Alloc _ _ _) = True
bindingHasTrivialType (Use _ _ _)   = True
bindingHasTrivialType _             = False

empty' :: Val' ()
empty' = Val' Empty 0 0 0 0

prettyUniformScheduleFun :: PrettyKernel kernel => Val' env -> UniformScheduleFun kernel env t -> Adoc
prettyUniformScheduleFun env (Slam lhs f)
  | (env', lhs') <- prettyBLhsWithTypes env lhs
  = "\\" <> lhs' <+> "->" <> hardline <> indent 2 (prettyUniformScheduleFun env' f)
prettyUniformScheduleFun env (Sbody sched)
  = prettyUniformSchedule env sched

prettyUniformSchedule :: forall kernel env. PrettyKernel kernel => Val' env -> UniformSchedule kernel env -> Adoc
prettyUniformSchedule env = \case
  Return
    -> annotate Statement "return"
  Alet lhs bnd body
    | (env', lhs') <- prettyBLhsForBinding env lhs bnd
    -> group (vsep [lhs' <+> "=", prettyBinding env bnd]) <> prettyNext' env' body
  Effect effect next
    -> prettyEffect env effect <> prettyNext next
  Acond c true false next
    -> group (vsep
        [ hang 2 $ group $ vsep
          [ if_ <+> prettyVar env c <+> then_
          , prettyUniformSchedule env true
          ]
        , hang 2 $ group $ vsep
          [ else_
          , prettyUniformSchedule env false
          ]
        ])
        <> prettyNext next
  Awhile _ body initial next
    -> hang 2 (group (vsep [annotate Statement "awhile", prettyVars env 10 initial]))
        <> hardline <> hang 4 ("  (" <+> prettyUniformScheduleFun env body)
        <> hardline <> "  )"
        <> prettyNext next
  AwhileSeq _ body initial next
    -> hang 2 (group (vsep [annotate Statement "awhile sequential", prettyVars env 10 initial]))
        <> hardline <> hang 4 ("  (" <+> prettyUniformScheduleFun env body)
        <> hardline <> "  )"
        <> prettyNext next
  Spawn (Effect (SignalAwait signals) body) next
    -> annotate Statement "spawn await" <+> list (map (prettyIdx env) signals) <+> "{"
        <> hardline <> indent 2 (prettyUniformSchedule env body)
        <> hardline <> "}"
        <> prettyNext next
  Spawn body next
    -> annotate Statement "spawn" <+> "{"
        <> hardline <> indent 2 (prettyUniformSchedule env body)
        <> hardline <> "}"
        <> prettyNext next
  where
    prettyNext' :: Val' env' -> UniformSchedule kernel env' -> Adoc
    prettyNext' _    Return = emptyDoc
    prettyNext' env' sched  = hardline <> prettyUniformSchedule env' sched

    prettyNext = prettyNext' env

prettyBinding :: Val' env -> Binding env t -> Adoc
prettyBinding env = \case
  Compute expr    -> hang 2 $ group $ vsep [annotate Statement "compute", prettyExp (val env) expr]
  NewSignal name  -> annotate Statement "new signal" <+> "--" <+> fromString name
  NewRef tp       -> annotate Statement "ref" <+> prettyGroundR tp
  Alloc _ tp sh   -> hang 2 $ group $ vsep [annotate Statement "alloc", prettyScalarType tp <> "[" <> prettyShapeVars env sh <> "]"]
  Use tp n buffer -> hang 2 $ group $ vsep [annotate Statement "use" <+> prettyScalarType tp <> "[" <> pretty n <> "]", prettyBuffer tp n buffer]
  Unit var        -> hang 2 $ group $ vsep [annotate Statement "unit", prettyVar env var]
  RefRead var     -> "*" <> prettyVar env var

prettyEffect :: PrettyKernel kernel => Val' env -> Effect kernel env -> Adoc
prettyEffect env = \case
  Exec _ kernel args    -> prettyKernelFun env kernel args
  SignalAwait signals   -> hang 2 $ group $ vsep [annotate Statement "await",   list $ map (prettyIdx env) signals]
  SignalResolve signals -> hang 2 $ group $ vsep [annotate Statement "resolve", list $ map (prettyIdx env) signals]
  RefWrite ref value    -> hang 2 $ group $ vsep ["*" <> prettyVar env ref <+> "=", prettyVar env value]
  Aassert msg cond      -> hang 2 $ group $ vsep [annotate Statement "assert", prettyText msg, prettyExp (val env) cond]
  Atrace msg t          -> hang 2 $ group $ vsep [annotate Statement "atrace", prettyText msg, prettyArrayDescriptors env t]

prettyKernelFun :: forall kernel env f. PrettyKernel kernel => Val' env -> KernelFun kernel f -> SArgs env f -> Adoc
prettyKernelFun env fun args = case prettyKernel of
  PrettyKernelBody includeModifier prettyKernelBody ->
    let
      go :: Val kenv -> OpenKernelFun kernel kenv t -> SArgs env t -> Adoc
      go kenv (KernelFunBody kernel) ArgsNil = prettyKernelBody kenv kernel
      go kenv (KernelFunLam (KernelArgRscalar _) f) (SArgScalar a :>: as)
        = go (Push kenv $ prettyVar env a) f as
      go kenv (KernelFunLam (KernelArgRbuffer _ _) f) (SArgBuffer mod' a :>: as) =
        let
          a'
            | includeModifier = prettyModifier mod' <+> prettyVar env a
            | otherwise       = prettyVar env a
        in
          go (Push kenv a') f as
    in
      go Empty fun args
  PrettyKernelFun prettyKernelAsFun ->
    hang 2 $ group $ vsep [annotate Execute "execute", prettyKernelAsFun fun, prettySArgs env args]

prettySArgs :: Val' benv -> SArgs benv f -> Adoc
prettySArgs env args = tupled $ map (\(Exists a) -> prettySArg env a) $ argsToList args

prettySArg :: Val' benv -> SArg benv t -> Adoc
prettySArg env (SArgScalar var)   = prettyVar env var
prettySArg env (SArgBuffer m var) = prettyModifier m <+> prettyVar env var

-- Variables
prettyVar :: Val' env -> Var s env t -> Adoc
prettyVar (Val' env _ _ _ _) (Var _ ix) = prj ix env

prettyIdx :: Val' env -> Idx env t -> Adoc
prettyIdx (Val' env _ _ _ _) ix = prj ix env

prettyVars :: forall env s t. Val' env -> Precedence -> Vars s env t -> Adoc
prettyVars env = prettyTupR $ const $ prettyVar env

prettyShapeVars :: Val' env -> Vars s env sh -> Adoc
prettyShapeVars _   TupRunit = "Z"
prettyShapeVars env vars = encloseSep "Z :. " "" " :. " $ map (\(Exists v) -> prettyVar env v) $ flattenTupR vars

prettyArrayDescriptors :: Val' env -> ArrayDescriptors env t -> Adoc
prettyArrayDescriptors env = prettyTupR (prettyArrayDescriptor env) 10

prettyArrayDescriptor :: Val' env -> Precedence -> ArrayDescriptor env t -> Adoc
prettyArrayDescriptor env p (ArrayDescriptor shr sh buffer) = parensIf (p > 0) $ prettyModifier In <+> sh' <+> prettyVars env 10 buffer
  where
    sh' = case shr of
      ShapeRz -> "Z"
      _ -> "(" <> prettyShapeVars env sh <> ")"
