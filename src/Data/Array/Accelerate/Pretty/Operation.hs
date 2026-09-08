{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE MonoLocalBinds      #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- |
-- Module      : Data.Array.Accelerate.Pretty.Operation
-- Copyright   : [2008..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.Pretty.Operation (
  PrettyOp(..), prettyArgs,
  prettyAcc, prettyOpenAcc,
  prettyAfun, prettyOpenAfun,
  prettyGroundR, prettyGroundRWithUniqueness,
  Val, Val'(..), val, empty',
  prettyVar, prettyVars,
  prettyArg, prettyShapeVars, prettyModifier, prettyBuffer,
  prettyFun, prettyExp, prettyExp', prettyArrayInstr,
  prettyGLhsWithTypes, prettyGLhsWithUniquenessTypes,
) where

import Data.Array.Accelerate.Pretty.Exp
import Data.Array.Accelerate.Pretty.Type
import Data.Array.Accelerate.AST.Operation
import Data.Array.Accelerate.AST.LeftHandSide
import Data.Array.Accelerate.AST.IdxSet (IdxSet)
import qualified Data.Array.Accelerate.AST.IdxSet as IdxSet
import Data.Array.Accelerate.Array.Buffer
import Data.Array.Accelerate.Representation.Elt
import Data.Array.Accelerate.Representation.Type
import Data.Array.Accelerate.Type

import Prettyprinter
import Data.String

import Prelude hiding (exp)

class PrettyOp op where
  prettyOp :: op t -> Adoc

  -- Only used in OperationAcc, when printing a PartitionedAcc a cluster is printed using prettyOp.
  -- The reason is that PrettyOp (Cluster' op) instance defines prettyOpWithArgs in terms of prettyOp.
  --
  prettyOpWithArgs :: Val env -> op t -> Args env t -> Adoc
  prettyOpWithArgs env op args = hang 2 $ group $ vsep [annotate Execute "execute", prettyOp op, prettyArgs env args]

prettyAcc :: PrettyOp op => OperationAcc op () t -> Adoc
prettyAcc = prettyOpenAcc empty'

prettyAfun :: PrettyOp op => OperationAfun op () f -> Adoc
prettyAfun = prettyOpenAfun empty'

prettyOpenAfun :: PrettyOp op => Val' benv -> OperationAfun op benv f -> Adoc
prettyOpenAfun env (Abody a) = prettyOpenAcc env a
prettyOpenAfun env (Alam lhs f) = "\\" <> lhs' <+> "->" <> hardline <> indent 2 (prettyOpenAfun env' f)
  where
    (env', lhs') = prettyGLhsWithTypes env lhs

prettyOpenAcc :: PrettyOp op => Val' benv -> OperationAcc op benv t -> Adoc
prettyOpenAcc env = \case
  Exec op args -> prettyOpWithArgs (val env) op args
  Return vars -> hang 2 $ group $ vsep [annotate Statement "return", prettyVars (val env) 10 vars]
  Manifest var -> hang 2 $ group $ vsep [annotate Statement "manifest", prettyVar (val env) var]
  Compute exp -> hang 2 $ group $ vsep [annotate Statement "compute", prettyExp (val env) exp]
  Alet LeftHandSideUnit _ bnd body
    | Exec{} <- bnd
    -- Only hide the left hand side if the right hand side is a kernel execution
    -> prettyOpenAcc env bnd
        <> hardline
        <> prettyOpenAcc env body
  Alet lhs us bnd body
    | (env', lhs') <- prettyGLhsWithUniquenessTypes env lhs us
      -> hang 2 (group $ vsep [lhs' <+> "=", prettyOpenAcc env bnd])
         <> hardline
         <> prettyOpenAcc env' body
  Alloc _ tp sh -> hang 2 $ group $ vsep [annotate Statement "alloc", prettyScalarType tp <> "[" <> prettyShapeVars (val env) sh <> "]"]
  Use tp n buffer -> hang 2 $ group $ vsep [annotate Statement "use" <+> prettyScalarType tp <> "[" <> pretty n <> "]", prettyBuffer tp n buffer]
  Unit var -> hang 2 $ group $ vsep [annotate Statement "unit", prettyVar (val env) var]
  Acond c true false
    -> group $ vsep
        [ hang 2 $ group $ vsep
          [ if_ <+> prettyVar (val env) c <+> then_
          , prettyOpenAcc env true
          ]
        , hang 2 $ group $ vsep
          [ else_
          , prettyOpenAcc env false
          ]
        ]
  Awhile us condition step initial
    -> "awhile" <+> prettyTupR (const prettyGroundRWithUniqueness) 10 (groundsRWithUniquenesses (mapTupR varType initial) us)
        <> hardline <> hang 4 ("  ( " <> prettyOpenAfun env condition)
        <> hardline <> "  )"
        <> hardline <> hang 4 ("  ( " <> prettyOpenAfun env step)
        <> hardline <> "  )"
        <> hardline <> indent 2 (prettyVars (val env) 10 initial)
  Atrace msg t ->
    hang 2 (group $ vsep [annotate Statement "atrace", prettyText msg, prettyArrayDescriptor (val env) t])
  Aassert msg g ->
    hang 2 (group $ vsep [annotate Statement "assert", prettyText msg, prettyExp (val env) g])
  Aassume g ->
    hang 2 (group $ vsep [annotate Statement "assume", prettyExp (val env) g])
  Fence set next ->
    hang 2 (group $ vsep [annotate Statement "fence", prettyIdxSet (val env) set])
    <> hardline
    <> prettyOpenAcc env next

prettyArrayDescriptor :: Val env -> ArrayDescriptors env t -> Adoc
prettyArrayDescriptor env = prettyTupR (\p (ArrayDescriptor _ sh buffer) -> prettyShapeVars env sh <+> " " <+> prettyVars env p buffer) 0

prettyArgs :: Val benv -> Args benv f -> Adoc
prettyArgs env args = tupled $ map (\(Exists a) -> prettyArg env a) $ argsToList args

prettyArg :: Val benv -> Arg benv t -> Adoc
prettyArg env (ArgVar vars) = prettyVars env 10 vars
prettyArg env (ArgExp e) = prettyExp env e
prettyArg env (ArgFun f) = prettyFun env f
prettyArg env (ArgArray m _ sh buffers) = group $ vsep [prettyModifier m, "(" <> prettyShapeVars env sh <> ")", prettyVars env 0 buffers]

prettyModifier :: Modifier m -> Adoc
prettyModifier In  = annotate Modifier "in"
prettyModifier Out = annotate Modifier "out"
prettyModifier Mut = annotate Modifier "mut"

prettyBuffer :: ScalarType tp -> Int -> Buffer tp -> Adoc
prettyBuffer _  0 _ = "[]"
prettyBuffer tp n b = align $ group $ "[ " <> vcat (mapTail (", " <>) $ map (fromString . showElt (TupRsingle tp)) $ bufferToList tp n b) <> " ]"

mapTail :: (a -> a) -> [a] -> [a]
mapTail f (x:xs) = x : map f xs
mapTail _ []     = []

-- Expressions
prettyFun :: Val env -> Fun env f -> Adoc
prettyFun env = prettyPreOpenFun (prettyArrayInstr env) Empty

prettyExp :: Val env -> Exp env t -> Adoc
prettyExp env = prettyPreOpenExp context0 (prettyArrayInstr env) Empty

prettyExp' :: Context -> Val env -> Exp env t -> Adoc
prettyExp' ctx env = prettyPreOpenExp ctx (prettyArrayInstr env) Empty

prettyArrayInstr :: Val env -> PrettyArrayInstr (ArrayInstr env)
prettyArrayInstr env context (Index arr) ix
  = parensIf (ctxPrecedence context < 9)
  $ sep [ prj (varIdx arr) env
        , group (sep ["!!", ix context']) ]
  where
    context' = Context L R 9
prettyArrayInstr env _ (Parameter var) _ = prj (varIdx var) env

-- prettyGLhs :: Val' env -> GLeftHandSide t env env' -> (Val' env', Adoc)
-- prettyGLhs = prettyLhs' push Nothing False

prettyGLhsWithTypes :: Val' env -> GLeftHandSide t env env' -> (Val' env', Adoc)
prettyGLhsWithTypes = prettyLhs' push (Just $ \(Exists t) -> prettyGroundR t) False

prettyGLhsWithUniquenessTypes :: Val' env -> GLeftHandSide t env env' -> Uniquenesses t -> (Val' env', Adoc)
prettyGLhsWithUniquenessTypes env lhs us
  = prettyLhs'
      (\(GroundRWithUniqueness g _) -> push g)
      (Just $ \(Exists t) -> prettyGroundRWithUniqueness t)
      False
      env
      (lhsWithUniquesses lhs us)


-- Environment
data Val' env = Val' (Val env) Int Int

push :: GroundR t -> Val' env -> (Val' (env, t), Adoc)
push (GroundRbuffer _) (Val' env b e) = (Val' (Push env d) (b + 1) e, d)
  where d = "b" <> pretty b
push (GroundRscalar _) (Val' env b e) = (Val' (Push env d) b (e + 1), d)
  where d = "e" <> pretty e

empty' :: Val' ()
empty' = Val' Empty 0 0

val :: Val' env -> Val env
val (Val' env _ _) = env

-- Variables
prettyVar :: Val env -> Var s env t -> Adoc
prettyVar env (Var _ ix) = prj ix env

prettyVars :: forall env s t. Val env -> Precedence -> Vars s env t -> Adoc
prettyVars env = prettyTupR $ const $ prettyVar env

prettyShapeVars :: Val env -> Vars s env sh -> Adoc
prettyShapeVars _   TupRunit = "Z"
prettyShapeVars env vars = encloseSep "Z :. " "" " :. " $ map (\(Exists v) -> prettyVar env v) $ flattenTupR vars

prettyIdxSet :: Val env -> IdxSet env -> Adoc
prettyIdxSet env set = "{" <> hsep (map (\(Exists idx) -> prj idx env) $ IdxSet.toList set) <> "}"

-- Types
prettyGroundR :: GroundR t -> Adoc
prettyGroundR (GroundRscalar tp) = prettyScalarType tp
prettyGroundR (GroundRbuffer tp) = "[" <> prettyScalarType tp <> "]"

prettyGroundRWithUniqueness :: GroundRWithUniqueness t -> Adoc
prettyGroundRWithUniqueness (GroundRWithUniqueness tp Unique) = prettyGroundR tp <> "¹"
prettyGroundRWithUniqueness (GroundRWithUniqueness tp Shared) = prettyGroundR tp <> ""
