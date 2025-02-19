{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns        #-}
-- |
-- Module      : Data.Array.Accelerate.Pretty.Print
-- Copyright   : [2008..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.Pretty.Print (

  PrettyAcc, ExtractAcc,
  prettyPreOpenAcc,
  prettyPreOpenAfun,
  prettyExp', prettyExp, prettyOpenExp,
  prettyFun, prettyOpenFun,
  prettyArray,
  prettyConst,
  prettyELhs,
  prettyALhs,

  -- ** Configuration
  PrettyConfig(..),
  configPlain,
  -- configWithHash,

  -- ** Internals
  Adoc,
  Val(..),
  PrettyEnv(..),
  Context(..),
  Keyword(..),
  Operator(..),
  parensIf, needsParens,
  ansiKeyword,
  shiftwidth,
  context0,
  app,
  manifest, delayed,
  primOperator,
  isInfix,
  prj, sizeEnv,

) where

import Data.Array.Accelerate.AST                                    hiding ( Direction )
import Data.Array.Accelerate.AST.LeftHandSide
import Data.Array.Accelerate.AST.Var
import Data.Array.Accelerate.Pretty.Exp
import Data.Array.Accelerate.Representation.Array
import Data.Array.Accelerate.Representation.Elt
import Data.Array.Accelerate.Representation.Stencil
import Data.Array.Accelerate.Representation.Type
import Data.Array.Accelerate.Sugar.Foreign
import qualified Data.Array.Accelerate.AST                          as AST
-- import qualified Data.Array.Accelerate.Trafo.Delayed                as Delayed

import Data.String
import Prettyprinter
import Prettyprinter.Render.Terminal
import Prelude                                                      hiding ( exp )


-- Implementation
-- --------------

type PrettyAcc acc =
  forall aenv a. PrettyConfig acc -> Context -> Val aenv -> acc aenv a -> Adoc
type ExtractAcc acc =
  forall aenv a. acc aenv a -> PreOpenAcc acc aenv a

manifest :: Operator -> Adoc
manifest = annotate Manifest . opName

delayed :: Operator -> Adoc
delayed = annotate Delayed . opName

ansiKeyword :: Keyword -> AnsiStyle
ansiKeyword Statement   = colorDull Yellow
ansiKeyword Conditional = colorDull Yellow
ansiKeyword Manifest    = color Blue
ansiKeyword Delayed     = color Green
ansiKeyword Execute     = color Blue
ansiKeyword Modifier    = colorDull Blue

-- Configuration for the pretty-printing functions
newtype PrettyConfig acc
  = PrettyConfig { confOperator :: forall aenv arrs.
                                   PreOpenAcc acc aenv arrs
                                -> String
                                -> Operator }

configPlain :: PrettyConfig acc
configPlain = PrettyConfig { confOperator = const fromString }

-- configWithHash :: PrettyConfig Delayed.DelayedOpenAcc
-- configWithHash =
--   PrettyConfig
--     { confOperator = \pacc name ->
--         let hashval = Hash.hashPreOpenAccWith
--                           (Hash.defaultHashOptions { Hash.perfect = False })
--                           Delayed.encodeDelayedOpenAcc
--                           pacc
--         in fromString (name ++ "_" ++ show hashval) }


-- Array computations
-- ------------------

prettyPreOpenAfun
    :: forall acc aenv f.
       PrettyConfig acc
    -> PrettyAcc acc
    -> Val aenv
    -> PreOpenAfun acc aenv f
    -> Adoc
prettyPreOpenAfun config prettyAcc = next (pretty '\\')
  where
    next :: Adoc -> Val aenv' -> PreOpenAfun acc aenv' f' -> Adoc
    next vs aenv (Abody body)   =
      hang shiftwidth (sep [vs <> "->", prettyAcc config context0 aenv body])
    next vs aenv (Alam lhs lam) =
      let (aenv', lhs') = prettyALhs True aenv lhs
      in  next (vs <> lhs' <> space) aenv' lam

prettyPreOpenAcc
    :: forall acc aenv arrs.
       PrettyConfig acc
    -> Context
    -> PrettyAcc acc
    -> ExtractAcc acc
    -> Val aenv
    -> PreOpenAcc acc aenv arrs
    -> Adoc
prettyPreOpenAcc config ctx prettyAcc extractAcc aenv pacc =
  case pacc of
    Avar (Var _ idx)  -> prj idx aenv
    Alet{}            -> prettyAlet config ctx prettyAcc extractAcc aenv pacc
    Apair{}           -> prettyAtuple config ctx prettyAcc extractAcc aenv pacc
    Anil              -> "()"
    Apply _ f a       -> apply
      where
        op    = Operator ">->" Infix L 1
        apply = sep [ ppAF f, group (sep [opName op, ppA a]) ]

    Acond p t e       -> flatAlt multi single
      where
        p' = ppE p
        t' = ppA t
        e' = ppA e
        --
        single = parensIf (needsParens ctx (Operator "?|:" Infix N 0))
               $ sep [ p', "?|", t', pretty ':', e' ]
        multi  = hang 3
               $ vsep [ if_ <+> p'
                      , hang shiftwidth (sep [ then_, t' ])
                      , hang shiftwidth (sep [ else_, e' ]) ]


    Atrace (Message _ _ msg) as bs  -> ppN "atrace"      .$ [ fromString (show msg), ppA as, ppA bs ]
    Aforeign _ ff _ a               -> ppN "aforeign"    .$ [ pretty (strForeign ff), ppA a ]
    Awhile p f a                    -> ppN "awhile"      .$ [ ppAF p, ppAF f, ppA a ]
    Use repr arr                    -> ppN "use"         .$ [ prettyArray repr arr ]
    Unit _ e                        -> ppN "unit"        .$ [ ppE e ]
    Reshape _ sh a                  -> ppN "reshape"     .$ [ ppE sh, ppA a ]
    Generate _ sh f                 -> ppN "generate"    .$ [ ppE sh, ppF f ]
    Transform _ sh p f a            -> ppN "transform"   .$ [ ppE sh, ppF p, ppF f, ppA a ]
    Replicate _ ix a                -> ppN "replicate"   .$ [ ppE ix, ppA a ]
    Slice _ a ix                    -> ppN "slice"       .$ [ ppE ix, ppA a ]
    Map _ f a                       -> ppN "map"         .$ [ ppF f,  ppA a ]
    ZipWith _ f a b                 -> ppN "zipWith"     .$ [ ppF f,  ppA a, ppA b ]
    Fold f (Just z) a               -> ppN "fold"        .$ [ ppF f,  ppE z, ppA a ]
    Fold f Nothing  a               -> ppN "fold1"       .$ [ ppF f,  ppA a ]
    FoldSeg _ f (Just z) a s        -> ppN "foldSeg"     .$ [ ppF f,  ppE z, ppA a, ppA s ]
    FoldSeg _ f Nothing  a s        -> ppN "fold1Seg"    .$ [ ppF f,  ppA a, ppA s ]
    Scan d f (Just z) a             -> ppD "scan" d ""   .$ [ ppF f,  ppE z, ppA a ]
    Scan d f Nothing  a             -> ppD "scan" d "1"  .$ [ ppF f,  ppA a ]
    Scan' d f z a                   -> ppD "scan" d "'"  .$ [ ppF f,  ppE z, ppA a ]
    Permute f d s                   -> ppN "permute"     .$ [ ppF f' | Just f' <- [f]] ++ [ ppA d, ppA s ]
    Backpermute _ sh f a            -> ppN "backpermute" .$ [ ppE sh, ppF f, ppA a ]
    Stencil s _ f b a               -> ppN "stencil"     .$ [ ppF f,  ppB (stencilEltR s) b, ppA a ]
    Stencil2 s1 s2 _ f b1 a1 b2 a2  -> ppN "stencil2"    .$ [ ppF f,  ppB (stencilEltR s1) b1, ppA a1, ppB (stencilEltR s2) b2, ppA a2 ]
  where
    infixr 0 .$
    f .$ xs
      = parensIf (needsParens ctx f)
      $ hang shiftwidth (sep (manifest f : xs))

    ppN :: String -> Operator
    ppN = confOperator config pacc

    ppA :: acc aenv a -> Adoc
    ppA = prettyAcc config app aenv

    ppAF :: PreOpenAfun acc aenv f -> Adoc
    ppAF = parens . prettyPreOpenAfun config prettyAcc aenv

    ppE :: Exp aenv t -> Adoc
    ppE = prettyExp' app aenv

    ppF :: Fun aenv t -> Adoc
    ppF = parens . prettyFun aenv

    ppB :: forall sh e.
           TypeR e
        -> Boundary aenv (Array sh e)
        -> Adoc
    ppB _  Clamp        = "clamp"
    ppB _  Mirror       = "mirror"
    ppB _  Wrap         = "wrap"
    ppB tp (Constant e) = prettyConst tp e
    ppB _  (Function f) = ppF f

    ppD :: String -> AST.Direction -> String -> Operator
    ppD f AST.LeftToRight k = ppN (f <> "l" <> k)
    ppD f AST.RightToLeft k = ppN (f <> "r" <> k)


prettyAlet
    :: forall acc aenv arrs.
       PrettyConfig acc
    -> Context
    -> PrettyAcc acc
    -> ExtractAcc acc
    -> Val aenv
    -> PreOpenAcc acc aenv arrs
    -> Adoc
prettyAlet config ctx prettyAcc extractAcc aenv0
  = parensIf (ctxPrecedence ctx > 0)
  . align . wrap . collect aenv0
  where
    collect :: Val aenv' -> PreOpenAcc acc aenv' a -> ([Adoc], Adoc)
    collect aenv =
      \case
        Alet lhs a1 a2 ->
          let (aenv', v)      = prettyALhs False aenv lhs
              a1'             = ppA aenv a1
              bnd | isAlet a1 = nest shiftwidth (vsep [v <+> equals, a1'])
                  | otherwise = v <+> align (equals <+> a1')
              (bnds, body)    = collect aenv' (extractAcc a2)
          in
          (bnd:bnds, body)
        --
        next       -> ([], prettyPreOpenAcc config context0 prettyAcc extractAcc aenv next)

    isAlet :: acc aenv' a -> Bool
    isAlet (extractAcc -> Alet{}) = True
    isAlet _                      = False

    ppA :: Val aenv' -> acc aenv' a -> Adoc
    ppA = prettyAcc config context0

    wrap :: ([Adoc], Adoc) -> Adoc
    wrap ([],   body) = body  -- shouldn't happen!
    wrap ([b],  body)
      = sep [ nest shiftwidth (sep [let_, b]), in_, body ]
    wrap (bnds, body)
      = vsep [ nest shiftwidth (vsep (let_:bnds))
             , in_
             , body
             ]

prettyAtuple
    :: forall acc aenv arrs.
       PrettyConfig acc
    -> Context
    -> PrettyAcc acc
    -> ExtractAcc acc
    -> Val aenv
    -> PreOpenAcc acc aenv arrs
    -> Adoc
prettyAtuple config ctx prettyAcc extractAcc aenv0 acc = case collect acc [] of
    Nothing  -> align $ ppPair acc
    Just tup ->
      case tup of
        []  -> "()"
        _   -> align $ parensIf (ctxPrecedence ctx > 0) ("T" <> pretty (length tup) <+> align (sep tup))
  where
    ppPair :: PreOpenAcc acc aenv arrs' -> Adoc
    ppPair (Apair a1 a2) =
      "(" <> ppPair (extractAcc a1) <> "," <+> prettyAcc config context0 aenv0 a2 <> ")"
    ppPair a             = prettyPreOpenAcc config context0 prettyAcc extractAcc aenv0 a

    collect :: PreOpenAcc acc aenv arrs' -> [Adoc] -> Maybe [Adoc]
    collect Anil          accum = Just accum
    collect (Apair a1 a2) accum = collect (extractAcc a1) (prettyAcc config app aenv0 a2 : accum)
    collect _             _     = Nothing

-- TODO: Should we also print the types of the declared variables? And the types of wildcards?
prettyALhs :: Bool -> Val env -> LeftHandSide s arrs env env' -> (Val env', Adoc)
prettyALhs requiresParens = prettyLhs requiresParens 'a'

prettyArray :: ArrayR (Array sh e) -> Array sh e -> Adoc
prettyArray aR@(ArrayR _ eR) = parens . fromString . showArray (showsElt eR) aR


-- Scalar expressions
-- ------------------

prettyFun :: Val aenv -> Fun aenv f -> Adoc
prettyFun aenv = prettyPreOpenFun (prettyArrayInstr aenv) Empty

prettyOpenFun :: Val env -> Val aenv -> OpenFun env aenv f -> Adoc
prettyOpenFun env aenv = prettyPreOpenFun (prettyArrayInstr aenv) env

prettyExp :: Val aenv -> Exp aenv t -> Adoc
prettyExp aenv = prettyPreOpenExp context0 (prettyArrayInstr aenv) Empty

prettyOpenExp :: Context -> Val env -> Val aenv -> OpenExp env aenv t -> Adoc
prettyOpenExp ctx env aenv = prettyPreOpenExp ctx (prettyArrayInstr aenv) env

prettyExp' :: Context -> Val aenv -> Exp aenv t -> Adoc
prettyExp' ctx aenv = prettyPreOpenExp ctx (prettyArrayInstr aenv) Empty

prettyArrayInstr :: Val aenv -> PrettyArrayInstr (ArrayInstr aenv)
prettyArrayInstr aenv context (Shape arr) _
  = parensIf (ctxPrecedence context < 10)
  $ "shape" <+> prettyArrayVar aenv arr
prettyArrayInstr aenv context (Index arr) ix
  = parensIf (ctxPrecedence context < 9)
  $ sep [ prettyArrayVar aenv arr
        , group (sep ["!", ix context']) ]
  where
    context' = Context L R 9
prettyArrayInstr aenv context (LinearIndex arr) ix
  = parensIf (ctxPrecedence context < 9)
  $ sep [ prettyArrayVar aenv arr
        , group (sep ["!!", ix context']) ]
  where
    context' = Context L R 9

prettyArrayVar
    :: forall aenv a.
       Val aenv
    -> ArrayVar aenv a
    -> Adoc
prettyArrayVar aenv (Var _ idx) = prj idx aenv
