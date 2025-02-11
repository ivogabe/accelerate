{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE PatternGuards       #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}
{-# LANGUAGE ViewPatterns        #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
-- |
-- Module      : Data.Array.Accelerate.Pretty.Exp
-- Copyright   : [2008..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.Pretty.Exp (
  Adoc,
  Keyword(..),
  for_, let_, in_, case_, of_, if_, then_, else_,
  prettyPreOpenFun, prettyPreOpenExp, PrettyArrayInstr,
  parensIf, Operator(..), Associativity, Direction(..),
  needsParens, prettyLhs, prettyLhs', prettyELhs, prettyConst,
  prettyTupR,
  primOperator, isInfix,
  Precedence, Fixity(..),
  Val(..), PrettyEnv(..), sizeEnv, prj, prjs,
  Context(..), context0, app,
  shiftwidth, (?), 
  IdxF(..)
  ) where

import Data.Array.Accelerate.AST.Exp                                hiding ( Direction )
import Data.Array.Accelerate.AST.Idx
import Data.Array.Accelerate.AST.LeftHandSide
import Data.Array.Accelerate.AST.Var
import Data.Array.Accelerate.Representation.Elt
import Data.Array.Accelerate.Representation.Type
import Data.Array.Accelerate.Sugar.Foreign
import Data.Array.Accelerate.Type

import Data.Char
import Data.String
import Prettyprinter
import Prelude                                                      hiding ( exp )
import Control.DeepSeq (NFData)

type Adoc = Doc Keyword

data Keyword
  = Statement     -- do | case of | let in
  | Conditional   -- if then else
  | Manifest      -- collective operations (kernel functions)
  | Delayed       -- fused operators
  | Execute
  | Modifier
  deriving (Eq, Show)

for_, let_, in_ :: Adoc
for_ = annotate Statement "for"
let_ = annotate Statement "let"
in_  = annotate Statement "in"

case_, of_ :: Adoc
case_ = annotate Statement "case"
of_   = annotate Statement "of"

if_, then_, else_ :: Adoc
if_   = annotate Statement "if"
then_ = annotate Statement "then"
else_ = annotate Statement "else"

type PrettyArrayInstr arr = forall s. Context -> arr s -> (Context -> Adoc) -> Adoc

prettyPreOpenFun
    :: forall arr env f.
       PrettyArrayInstr arr
    -> Val env
    -> PreOpenFun arr env f
    -> Adoc
prettyPreOpenFun prettyArrayInstr env0 = next (pretty '\\') env0
  where
    next :: Adoc -> Val env' -> PreOpenFun arr env' f' -> Adoc
    next vs env (Body body)
      --   PrimApp f x                             <- body
      -- , op                                      <- primOperator f
      -- , isInfix op
      -- , Tuple (NilTup `SnocTup` a `SnocTup` b)  <- x
      -- , Var (SuccIdx ZeroIdx)                   <- a
      -- , Var ZeroIdx                             <- b
      -- = opName op -- surrounding context will add parens
      --
      = hang shiftwidth (sep [ vs <> "->"
                             , prettyPreOpenExp context0 prettyArrayInstr env body])
    next vs env (Lam lhs lam) =
      let (env', lhs') = prettyELhs True env lhs
      in  next (vs <> lhs' <> space) env' lam

prettyPreOpenExp
    :: forall arr env t.
       Context
    -> PrettyArrayInstr arr
    -> Val env
    -> PreOpenExp arr env t
    -> Adoc
prettyPreOpenExp ctx prettyArrayInstr env exp =
  case exp of
    Evar (Var _ idx)      -> prj idx env
    Let{}                 -> prettyLet ctx prettyArrayInstr env exp
    PrimApp f x
      | a `Pair` b <- x   -> ppF2 op  (ppE a) (ppE b)
      | otherwise         -> ppF1 op' (ppE x)
      where
        op  = primOperator f
        op' = isInfix op ? (Operator (parens (opName op)) App L 10, op)
    --
    PrimConst c           -> prettyPrimConst c
    Const tp c            -> prettyConst (TupRsingle tp) c
    Pair{}                -> prettyTuple ctx prettyArrayInstr env exp
    Nil                   -> "()"
    VecPack   _ e         -> ppF1 "pack"   (ppE e)
    VecUnpack _ e         -> ppF1 "unpack" (ppE e)
    Case x xs d           -> prettyCase prettyArrayInstr env x xs d
    Cond p t e            -> flatAlt multi single
      where
        p' = ppE p context0
        t' = ppE t context0
        e' = ppE e context0
        --
        single = parensIf (needsParens ctx (Operator "?:" Infix N 0))
               $ sep [ p', pretty '?', t', pretty ':', e' ]
        multi  = parensIf (ctxPrecedence ctx > 0)
               $ hang 3
               $ vsep [ if_ <+> p'
                      , hang shiftwidth (sep [ then_, t' ])
                      , hang shiftwidth (sep [ else_, e' ]) ]
    --
    IndexSlice _ slix sh  -> ppF2 "indexSlice"  (ppE slix) (ppE sh)
    IndexFull _ slix sl   -> ppF2 "indexFull"   (ppE slix) (ppE sl)
    ToIndex _ sh ix       -> ppF2 "toIndex"     (ppE sh) (ppE ix)
    FromIndex _ sh ix     -> ppF2 "fromIndex"   (ppE sh) (ppE ix)
    While p f x           -> ppF3 "while"       (ppF p) (ppF f) (ppE x)
    Foreign _ ff _ e      -> ppF2 "foreign"     (\_ -> pretty (strForeign ff)) (ppE e)
    ArrayInstr instr e    -> prettyArrayInstr ctx instr (ppE e)
    ShapeSize _ sh        -> ppF1 "shapeSize"   (ppE sh)
    Coerce _ tp x         -> ppF1 (Operator (withTypeRep tp "coerce") App L 10) (ppE x)
    Undef tp              -> withTypeRep tp "undef"

  where
    ppE :: PreOpenExp arr env e -> Context -> Adoc
    ppE e c = prettyPreOpenExp c prettyArrayInstr env e

    ppF :: PreOpenFun arr env f -> Context -> Adoc
    ppF f _ = parens $ prettyPreOpenFun prettyArrayInstr env f

    ppF1 :: Operator -> (Context -> Adoc) -> Adoc
    ppF1 op x
      = parensIf (needsParens ctx op)
      $ combine [ opName op, x ctx' ]
      where
        ctx'    = isPrefix op ? (arg op R, app)
        combine = isPrefix op ? (cat, hang 2 . sep)

    ppF2 :: Operator -> (Context -> Adoc) -> (Context -> Adoc) -> Adoc
    ppF2 op x y
      = parensIf (needsParens ctx op)
      $ if isInfix op
          then sep [ x (arg op L), group (sep [opName op, y (arg op R)]) ]
          else hang 2 $ sep [ opName op, x app, y app ]

    ppF3 :: Operator -> (Context -> Adoc) -> (Context -> Adoc) -> (Context -> Adoc) -> Adoc
    ppF3 op x y z
      = parensIf (needsParens ctx op)
      $ hang 2
      $ sep [ opName op, x app, y app, z app ]

    withTypeRep :: ScalarType t -> Adoc -> Adoc
    withTypeRep t op = op <+> "@" <> pretty (show t)

prettyLet
    :: forall arr env t.
       Context
    -> PrettyArrayInstr arr
    -> Val env
    -> PreOpenExp arr env t
    -> Adoc
prettyLet ctx prettyArrayInstr env0
  = parensIf (ctxPrecedence ctx > 0)
  . align . wrap . collect env0
  where
    collect :: Val env' -> PreOpenExp arr env' e -> ([Adoc], Adoc)
    collect env =
      \case
        Let lhs e1 e2 ->
          let (env', v)       = prettyELhs False env lhs
              e1'             = ppE env e1
              bnd | isLet e1  = nest shiftwidth (vsep [v <+> equals, e1'])
                  | otherwise = v <+> align (equals <+> e1')
              (bnds, body)    = collect env' e2
          in
          (bnd:bnds, body)
        --
        next     -> ([], ppE env next)

    isLet :: PreOpenExp arr env' t' -> Bool
    isLet Let{} = True
    isLet _     = False

    ppE :: Val env' -> PreOpenExp arr env' t' -> Adoc
    ppE env = prettyPreOpenExp context0 prettyArrayInstr env

    wrap :: ([Adoc], Adoc) -> Adoc
    wrap ([],   body) = body  -- shouldn't happen!
    wrap ([b],  body)
      = sep [ nest shiftwidth (sep [let_, b]), in_, body ]
    wrap (bnds, body)
      = vsep [ nest shiftwidth (vsep [let_, sepBy (flatAlt "" " ; ") bnds])
             , in_
             , body
             ]

    sepBy :: Adoc -> [Adoc] -> Adoc
    sepBy = encloseSep mempty mempty

prettyTuple
    :: forall arr env t.
       Context
    -> PrettyArrayInstr arr
    -> Val env
    -> PreOpenExp arr env t
    -> Adoc
prettyTuple ctx prettyArrayInstr env exp = case collect exp of
    Nothing  -> align $ ppPair exp
    Just tup ->
      case tup of
        []  -> "()"
        _   -> align $ parensIf (ctxPrecedence ctx > 0) ("T" <> pretty (length tup) <+> align (sep tup))
  where
    ppPair :: PreOpenExp arr env t' -> Adoc
    ppPair (Pair e1 e2) = "(" <> ppPair e1 <> "," <+> prettyPreOpenExp context0 prettyArrayInstr env e2 <> ")"
    ppPair e            = prettyPreOpenExp context0 prettyArrayInstr env e

    collect :: PreOpenExp arr env t' -> Maybe [Adoc]
    collect Nil                = Just []
    collect (Pair e1 e2)
      | Just tup <- collect e1 = Just $ tup ++ [prettyPreOpenExp app prettyArrayInstr env e2]
    collect _                  = Nothing

prettyCase
    :: PrettyArrayInstr arr
    -> Val env
    -> PreOpenExp arr env a
    -> [(TAG, PreOpenExp arr env b)]
    -> Maybe (PreOpenExp arr env b)
    -> Adoc
prettyCase prettyArrayInstr env x xs def
  = hang shiftwidth
  $ vsep [ case_ <+> x' <+> of_
         , flatAlt (vcat xs') (encloseSep "{ " " }" "; " xs')
         ]
  where
    x'  = prettyPreOpenExp context0 prettyArrayInstr env x
    xs' = map (\(t,e) -> pretty t <+> "->" <+> prettyPreOpenExp context0 prettyArrayInstr env e) xs
       ++ case def of
            Nothing -> []
            Just d  -> ["_" <+> "->" <+> prettyPreOpenExp context0 prettyArrayInstr env d]

prettyConst :: TypeR e -> e -> Adoc
prettyConst tp x =
  let y = showElt tp x
  in  parensIf (any isSpace y) (pretty y)

prettyPrimConst :: PrimConst a -> Adoc
prettyPrimConst PrimMinBound{} = "minBound"
prettyPrimConst PrimMaxBound{} = "maxBound"
prettyPrimConst PrimPi{}       = "pi"

data Operator = Operator
  { opName            :: Adoc
  , opFixity          :: Fixity
  , opAssociativity   :: Associativity
  , opPrecedence      :: Precedence
  }

instance IsString Operator where
  fromString s = Operator (fromString s) App L 10

needsParens :: Context -> Operator -> Bool
needsParens Context{..} Operator{..}
  | ctxPrecedence     < opPrecedence    = False
  | ctxPrecedence     > opPrecedence    = True
  | ctxAssociativity /= opAssociativity = True
  | otherwise                           = ctxPosition /= opAssociativity

parensIf :: Bool -> Doc ann -> Doc ann
parensIf True  = group . parens . align
parensIf False = id


prettyELhs :: Bool -> Val env -> LeftHandSide s t env env' -> (Val env', Adoc)
prettyELhs requiresParens = prettyLhs requiresParens 'x'

prettyLhs :: forall s env env' t. Bool -> Char -> Val env -> LeftHandSide s t env env' -> (Val env', Adoc)
prettyLhs requiresParens x = prettyLhs' push Nothing requiresParens
  where
    push :: s t' -> Val env'' -> (Val (env'', t'), Adoc)
    push _ env = (Push env v, v)
      where
        v = pretty x <> pretty (sizeEnv env)

prettyLhs'
  :: forall val s env env' t.
     (forall t' env''. s t' -> val env'' -> (val (env'', t'), Adoc))
  -> (Maybe (Exists s -> Adoc))
  -> Bool
  -> val env
  -> LeftHandSide s t env env'
  -> (val env', Adoc)
prettyLhs' push prettyTp requiresParens env0 lhs = case collect lhs of
  Nothing          -> ppPair requiresParens lhs
  Just (env1, tup) ->
    case tup of
      []  -> (env1, "()")
      _   -> (env1, parensIf requiresParens (pretty 'T' <> pretty (length tup) <+> align (sep tup)))
  where
    ppPair :: Bool -> LeftHandSide s arrs' env env'' -> (val env'', Adoc)
    ppPair _         LeftHandSideUnit         = (env0, "()")
    ppPair requiresP (LeftHandSideWildcard t)
      | Just prettyT <- prettyTp              = (env0, parensIf requiresP $ "_: " <> align (prettyTupR (const $ prettyT . Exists) 0 t))
      | otherwise                             = (env0, "_")
    ppPair requiresP (LeftHandSideSingle t)   = (env1, v')
      where
        (env1, v) = push t env0
        v'
          | Just prettyT <- prettyTp          = parensIf requiresP $ v <> ": " <> align (prettyT $ Exists t)
          | otherwise                         = v
    ppPair _         (LeftHandSidePair a b)   = (env2, tupled [doc1, doc2])
      where
        (env1, doc1) = ppPair False a
        (env2, doc2) = prettyLhs' push prettyTp False env1 b

    collect :: LeftHandSide s arrs' env env'' -> Maybe (val env'', [Adoc])
    collect (LeftHandSidePair l1 l2)
      | Just (env1, tup ) <- collect l1
      ,      (env2, doc2) <- prettyLhs' push prettyTp True env1 l2 = Just (env2, tup ++ [doc2])
    collect (LeftHandSideWildcard TupRunit) = Just (env0, [])
    collect _ = Nothing

prettyTupR :: forall s t. (forall t'. Precedence -> s t' -> Adoc) -> Precedence -> TupR s t -> Adoc
prettyTupR elt p tupR
  | TupRunit <- tupR = "()"
  | TupRsingle e <- tupR = elt p e
  | Just tuple <- collect tupR []
    = parensIf (p > 0)
    $ "T" <> pretty (length tuple) <+> align (sep tuple)
  | otherwise = ppPair tupR
  where
    -- Try to recover the 'tuple-format', i.e. a structure of pairs of the form
    -- ((( (), a ), b ), c )
    collect :: TupR s t' -> [Adoc] -> Maybe [Adoc]
    collect TupRunit                      accum = Just accum
    collect (TupRpair v1 (TupRsingle v2)) accum = collect v1 (elt 10 v2 : accum)
    collect _                             _     = Nothing

    -- Prints a pair which is not in the tuple-format.
    -- We thus do not have to traverse it again to check for this format,
    -- preventing repeatedly calling 'collect' on the same structure.
    --
    ppPair :: TupR s t' -> Adoc
    ppPair (TupRpair v1 v2) = tupled [ppPair v1, prettyTupR elt 0 v2]
    ppPair v = prettyTupR elt 0 v

-- Primitive operators
-- -------------------
--
-- The core of the pretty printer is how to correctly handle precedence,
-- associativity, and fixity of the primitive scalar operators.
--

data Direction = L | N | R
  deriving Eq

data Fixity = App | Infix | Prefix
  deriving Eq

type Precedence    = Int
type Associativity = Direction

data Context = Context
  { ctxAssociativity  :: Associativity
  , ctxPosition       :: Direction
  , ctxPrecedence     :: Precedence
  }

context0 :: Context
context0 = Context N N 0

app :: Context
app = Context L N 10

arg :: Operator -> Direction -> Context
arg Operator{..} side = Context opAssociativity side opPrecedence

isPrefix :: Operator -> Bool
isPrefix Operator{..} = opFixity == Prefix

isInfix :: Operator -> Bool
isInfix Operator{..}  = opFixity == Infix

primOperator :: PrimFun a -> Operator
primOperator PrimAdd{}                = Operator (pretty '+')         Infix  L 6
primOperator PrimSub{}                = Operator (pretty '-')         Infix  L 6
primOperator PrimMul{}                = Operator (pretty '*')         Infix  L 7
primOperator PrimNeg{}                = Operator (pretty '-')         Prefix L 6  -- Haskell's only prefix operator
primOperator PrimAbs{}                = Operator "abs"                App    L 10
primOperator PrimSig{}                = Operator "signum"             App    L 10
primOperator PrimQuot{}               = Operator "quot"               App    L 10
primOperator PrimRem{}                = Operator "rem"                App    L 10
primOperator PrimQuotRem{}            = Operator "quotRem"            App    L 10
primOperator PrimIDiv{}               = Operator "div"                App    L 10
primOperator PrimMod{}                = Operator "mod"                App    L 10
primOperator PrimDivMod{}             = Operator "divMod"             App    L 10
primOperator PrimBAnd{}               = Operator ".&."                Infix  L 7
primOperator PrimBOr{}                = Operator ".|."                Infix  L 5
primOperator PrimBXor{}               = Operator "xor"                App    L 10
primOperator PrimBNot{}               = Operator "complement"         App    L 10
primOperator PrimBShiftL{}            = Operator "shiftL"             App    L 10
primOperator PrimBShiftR{}            = Operator "shiftR"             App    L 10
primOperator PrimBRotateL{}           = Operator "rotateL"            App    L 10
primOperator PrimBRotateR{}           = Operator "rotateR"            App    L 10
primOperator PrimPopCount{}           = Operator "popCount"           App    L 10
primOperator PrimCountLeadingZeros{}  = Operator "countLeadingZeros"  App    L 10
primOperator PrimCountTrailingZeros{} = Operator "countTrailingZeros" App    L 10
primOperator PrimFDiv{}               = Operator (pretty '/')         Infix  L 7
primOperator PrimRecip{}              = Operator "recip"              App    L 10
primOperator PrimSin{}                = Operator "sin"                App    L 10
primOperator PrimCos{}                = Operator "cos"                App    L 10
primOperator PrimTan{}                = Operator "tan"                App    L 10
primOperator PrimAsin{}               = Operator "asin"               App    L 10
primOperator PrimAcos{}               = Operator "acos"               App    L 10
primOperator PrimAtan{}               = Operator "atan"               App    L 10
primOperator PrimSinh{}               = Operator "sinh"               App    L 10
primOperator PrimCosh{}               = Operator "cosh"               App    L 10
primOperator PrimTanh{}               = Operator "tanh"               App    L 10
primOperator PrimAsinh{}              = Operator "asinh"              App    L 10
primOperator PrimAcosh{}              = Operator "acosh"              App    L 10
primOperator PrimAtanh{}              = Operator "atanh"              App    L 10
primOperator PrimExpFloating{}        = Operator "exp"                App    L 10
primOperator PrimSqrt{}               = Operator "sqrt"               App    L 10
primOperator PrimLog{}                = Operator "log"                App    L 10
primOperator PrimFPow{}               = Operator "**"                 Infix  R 8
primOperator PrimLogBase{}            = Operator "logBase"            App    L 10
primOperator PrimTruncate{}           = Operator "truncate"           App    L 10
primOperator PrimRound{}              = Operator "round"              App    L 10
primOperator PrimFloor{}              = Operator "floor"              App    L 10
primOperator PrimCeiling{}            = Operator "ceiling"            App    L 10
primOperator PrimAtan2{}              = Operator "atan2"              App    L 10
primOperator PrimIsNaN{}              = Operator "isNaN"              App    L 10
primOperator PrimIsInfinite{}         = Operator "isInfinite"         App    L 10
primOperator PrimLt{}                 = Operator "<"                  Infix  N 4
primOperator PrimGt{}                 = Operator ">"                  Infix  N 4
primOperator PrimLtEq{}               = Operator "<="                 Infix  N 4
primOperator PrimGtEq{}               = Operator ">="                 Infix  N 4
primOperator PrimEq{}                 = Operator "=="                 Infix  N 4
primOperator PrimNEq{}                = Operator "/="                 Infix  N 4
primOperator PrimMax{}                = Operator "max"                App    L 10
primOperator PrimMin{}                = Operator "min"                App    L 10
primOperator PrimLAnd                 = Operator "&&"                 Infix  R 3
primOperator PrimLOr                  = Operator "||"                 Infix  R 2
primOperator PrimLNot                 = Operator "not"                App    L 10
primOperator PrimFromIntegral{}       = Operator "fromIntegral"       App    L 10
primOperator PrimToFloating{}         = Operator "toFloating"         App    L 10


-- Environments
-- ------------

data Val env where
  Empty ::                    Val ()
  Push  :: Val env -> Adoc -> Val (env, t)

class PrettyEnv env where
  prettyEnv :: Adoc -> Val env

instance PrettyEnv () where
  prettyEnv _ = Empty

instance PrettyEnv env => PrettyEnv (env, t) where
  prettyEnv v =
    let env = prettyEnv v :: Val env
        x   = v <> pretty (sizeEnv env)
    in
    env `Push` x

sizeEnv :: Val env -> Int
sizeEnv Empty        = 0
sizeEnv (Push env _) = 1 + sizeEnv env

prj :: Idx env t -> Val env -> Adoc
prj ZeroIdx      (Push _ v)   = v
prj (SuccIdx ix) (Push env _) = prj ix env

prjs :: TupR (IdxF f env) e -> Val env -> [Adoc]
prjs TupRunit _ = []
prjs (TupRpair l r) env = prjs l env <> prjs r env
prjs (TupRsingle (IdxF ix)) env = [prj ix env]

-- Utilities
-- ---------

shiftwidth :: Int
shiftwidth = 2

infix 0 ?
(?) :: Bool -> (a, a) -> a
True  ? (t,_) = t
False ? (_,f) = f


newtype IdxF f env a = IdxF { runIdxF :: Idx env (f a)}
  deriving newtype (NFData)
