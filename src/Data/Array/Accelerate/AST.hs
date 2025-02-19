{-# LANGUAGE AllowAmbiguousTypes   #-}
{-# LANGUAGE BangPatterns          #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# OPTIONS_HADDOCK hide #-}
-- |
-- Module      : Data.Array.Accelerate.AST
-- Copyright   : [2008..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--
-- /Scalar versus collective operations/
--
-- The embedded array processing language is a two-level language.  It
-- combines a language of scalar expressions and functions with a language of
-- collective array operations.  Scalar expressions are used to compute
-- arguments for collective operations and scalar functions are used to
-- parametrise higher-order, collective array operations.  The two-level
-- structure, in particular, ensures that collective operations cannot be
-- parametrised with collective operations; hence, we are following a flat
-- data-parallel model.  The collective operations manipulate
-- multi-dimensional arrays whose shape is explicitly tracked in their types.
-- In fact, collective operations cannot produce any values other than
-- multi-dimensional arrays; when they yield a scalar, this is in the form of
-- a 0-dimensional, singleton array.  Similarly, scalar expression can -as
-- their name indicates- only produce tuples of scalar, but not arrays.
--
-- There are, however, two expression forms that take arrays as arguments.  As
-- a result scalar and array expressions are recursively dependent.  As we
-- cannot and don't want to compute arrays in the middle of scalar
-- computations, array computations will always be hoisted out of scalar
-- expressions.  So that this is always possible, these array expressions may
-- not contain any free scalar variables.  To express that condition in the
-- type structure, we use separate environments for scalar and array variables.
--
-- /Programs/
--
-- Collective array programs comprise closed expressions of array operations.
-- There is no explicit sharing in the initial AST form, but sharing is
-- introduced subsequently by common subexpression elimination and floating
-- of array computations.
--
-- /Functions/
--
-- The array expression language is first-order and only provides limited
-- control structures to ensure that it can be efficiently executed on
-- compute-acceleration hardware, such as GPUs.  To restrict functions to
-- first-order, we separate function abstraction from the main expression
-- type.  Functions are represented using de Bruijn indices.
--
-- /Parametric and ad-hoc polymorphism/
--
-- The array language features paramatric polymophism (e.g., pairing and
-- projections) as well as ad-hoc polymorphism (e.g., arithmetic operations).
-- All ad-hoc polymorphic constructs include reified dictionaries (c.f.,
-- module 'Types').  Reified dictionaries also ensure that constants
-- (constructor 'Const') are representable on compute acceleration hardware.
--
-- The AST contains both reified dictionaries and type class constraints.
-- Type classes are used for array-related functionality that is uniformly
-- available for all supported types.  In contrast, reified dictionaries are
-- used for functionality that is only available for certain types, such as
-- arithmetic operations.
--

module Data.Array.Accelerate.AST (

  -- * Internal AST
  -- ** Array computations
  Afun, PreAfun, OpenAfun, PreOpenAfun(..),
  Acc, OpenAcc(..), PreOpenAcc(..), Direction(..), Message(..),
  ALeftHandSide, ArrayVar, ArrayVars,

  -- ** Scalar expressions
  ELeftHandSide, ExpVar, ExpVars, expVars,
  Fun, OpenFun, PreOpenFun(..),
  Exp, OpenExp, PreOpenExp(..),
  ArrayInstr(..), IsArrayInstr(..), NoArrayInstr,
  Boundary(..),
  PrimConst(..),
  PrimFun(..),
  PrimBool,
  PrimMaybe,

  -- ** Extracting type information
  HasArraysR(..), arrayR,
  expType,
  primConstType,
  primFunType,

  -- ** Normal-form
  NFDataAcc,
  rnfOpenAfun, rnfPreOpenAfun,
  rnfOpenAcc, rnfPreOpenAcc,
  rnfALeftHandSide,
  rnfArrayVar,
  rnfOpenFun,
  rnfOpenExp,
  rnfELeftHandSide,
  rnfExpVar,
  rnfBoundary,
  rnfConst,
  rnfPrimConst,
  rnfPrimFun,

  -- ** Template Haskell
  LiftAcc,
  liftPreOpenAfun,
  liftPreOpenAcc,
  liftALeftHandSide,
  liftArrayVar,
  liftOpenFun,
  liftOpenExp,
  liftELeftHandSide,
  liftExpVar,
  liftBoundary,
  liftPrimConst,
  liftPrimFun,
  liftMessage,

  -- ** Miscellaneous
  encodeArrayVar,
  formatPreAccOp,

) where

import Data.Array.Accelerate.AST.Idx
import Data.Array.Accelerate.AST.LeftHandSide
import Data.Array.Accelerate.AST.Var
import Data.Array.Accelerate.AST.Exp
import Data.Array.Accelerate.Analysis.Hash.Exp as Hash
import Data.Array.Accelerate.Representation.Array
import Data.Array.Accelerate.Representation.Elt
import Data.Array.Accelerate.Representation.Shape
import Data.Array.Accelerate.Representation.Slice
import Data.Array.Accelerate.Representation.Stencil
import Data.Array.Accelerate.Representation.Type
import Data.Array.Accelerate.Sugar.Foreign
import Data.Array.Accelerate.Type

import Control.DeepSeq
import Data.Kind
import Data.Maybe
import Data.Text                                                    ( Text )
import Data.Text.Lazy.Builder
import Formatting
import Language.Haskell.TH.Extra                                    ( CodeQ )
import qualified Language.Haskell.TH.Extra                          as TH
import qualified Language.Haskell.TH.Syntax                         as TH
import Data.Typeable                                                ( (:~:)(..) )


-- Array expressions
-- -----------------

-- | Function abstraction over parametrised array computations
--
data PreOpenAfun acc aenv t where
  Abody ::                               acc             aenv  t -> PreOpenAfun acc aenv t
  Alam  :: ALeftHandSide a aenv aenv' -> PreOpenAfun acc aenv' t -> PreOpenAfun acc aenv (a -> t)

-- Function abstraction over vanilla open array computations
--
type OpenAfun = PreOpenAfun OpenAcc

-- | Parametrised array-computation function without free array variables
--
type PreAfun acc = PreOpenAfun acc ()

-- | Vanilla array-computation function without free array variables
--
type Afun = OpenAfun ()

-- Vanilla open array computations
--
newtype OpenAcc aenv t = OpenAcc { runOpenAcc :: PreOpenAcc OpenAcc aenv t }

-- | Closed array expression aka an array program
--
type Acc = OpenAcc ()

-- Types for array binders
--
type ALeftHandSide  = LeftHandSide ArrayR
type ArrayVar       = Var ArrayR
type ArrayVars aenv = Vars ArrayR aenv

-- Trace messages
data Message a where
  Message :: (a -> String)                    -- embedded show
          -> Maybe (CodeQ (a -> String))      -- lifted version of show, for TH
          -> Text
          -> Message a

-- | Collective array computations parametrised over array variables
-- represented with de Bruijn indices.
--
-- * Scalar functions and expressions embedded in well-formed array
--   computations cannot contain free scalar variable indices. The latter
--   cannot be bound in array computations, and hence, cannot appear in any
--   well-formed program.
--
-- * The let-form is used to represent the sharing discovered by common
--   subexpression elimination as well as to control evaluation order. (We
--   need to hoist array expressions out of scalar expressions---they occur
--   in scalar indexing and in determining an arrays shape.)
--
-- The data type is parameterised over the representation types (not the
-- surface type).
--
-- We use a non-recursive variant parametrised over the recursive closure,
-- to facilitate attribute calculation in the backend.
--
data PreOpenAcc (acc :: Type -> Type -> Type) aenv a where

  -- Local non-recursive binding to represent sharing and demand
  -- explicitly. Note this is an eager binding!
  --
  Alet        :: ALeftHandSide bndArrs aenv aenv'
              -> acc            aenv  bndArrs         -- bound expression
              -> acc            aenv' bodyArrs        -- the bound expression scope
              -> PreOpenAcc acc aenv  bodyArrs

  -- Variable bound by a 'Let', represented by a de Bruijn index
  --
  Avar        :: ArrayVar       aenv (Array sh e)
              -> PreOpenAcc acc aenv (Array sh e)

  -- Tuples of arrays
  --
  Apair       :: acc            aenv as
              -> acc            aenv bs
              -> PreOpenAcc acc aenv (as, bs)

  Anil        :: PreOpenAcc acc aenv ()

  -- Array-function application.
  --
  -- The array function is not closed at the core level because we need access
  -- to free variables introduced by 'run1' style evaluators. See Issue#95.
  --
  Apply       :: ArraysR arrs2
              -> PreOpenAfun acc aenv (arrs1 -> arrs2)
              -> acc             aenv arrs1
              -> PreOpenAcc  acc aenv arrs2

  -- Apply a backend-specific foreign function to an array, with a pure
  -- Accelerate version for use with other backends. The functions must be
  -- closed.
  --
  Aforeign    :: Foreign asm
              => ArraysR bs
              -> asm                   (as -> bs) -- The foreign function for a given backend
              -> PreAfun      acc      (as -> bs) -- Fallback implementation(s)
              -> acc              aenv as         -- Arguments to the function
              -> PreOpenAcc   acc aenv bs

  -- If-then-else for array-level computations
  --
  Acond       :: Exp            aenv PrimBool
              -> acc            aenv arrs
              -> acc            aenv arrs
              -> PreOpenAcc acc aenv arrs

  -- Value-recursion for array-level computations
  --
  Awhile      :: PreOpenAfun acc aenv (arrs -> Scalar PrimBool) -- continue iteration while true
              -> PreOpenAfun acc aenv (arrs -> arrs)            -- function to iterate
              -> acc             aenv arrs                      -- initial value
              -> PreOpenAcc  acc aenv arrs

  Atrace      :: Message              arrs1
              -> acc             aenv arrs1
              -> acc             aenv arrs2
              -> PreOpenAcc  acc aenv arrs2

  -- Array inlet. Triggers (possibly) asynchronous host->device transfer if
  -- necessary.
  --
  Use         :: ArrayR (Array sh e)
              -> Array sh e
              -> PreOpenAcc acc aenv (Array sh e)

  -- Capture a scalar (or a tuple of scalars) in a singleton array
  --
  Unit        :: TypeR e
              -> Exp            aenv e
              -> PreOpenAcc acc aenv (Scalar e)

  -- Change the shape of an array without altering its contents.
  -- Precondition (this may not be checked!):
  --
  -- > dim == size dim'
  --
  Reshape     :: ShapeR sh
              -> Exp            aenv sh                         -- new shape
              -> acc            aenv (Array sh' e)              -- array to be reshaped
              -> PreOpenAcc acc aenv (Array sh e)

  -- Construct a new array by applying a function to each index.
  --
  Generate    :: ArrayR (Array sh e)
              -> Exp            aenv sh                         -- output shape
              -> Fun            aenv (sh -> e)                  -- representation function
              -> PreOpenAcc acc aenv (Array sh e)

  -- Hybrid map/backpermute, where we separate the index and value
  -- transformations.
  --
  Transform   :: ArrayR (Array sh' b)
              -> Exp            aenv sh'                        -- dimension of the result
              -> Fun            aenv (sh' -> sh)                -- index permutation function
              -> Fun            aenv (a   -> b)                 -- function to apply at each element
              ->            acc aenv (Array sh  a)              -- source array
              -> PreOpenAcc acc aenv (Array sh' b)

  -- Replicate an array across one or more dimensions as given by the first
  -- argument
  --
  Replicate   :: SliceIndex slix sl co sh                       -- slice type specification
              -> Exp            aenv slix                       -- slice value specification
              -> acc            aenv (Array sl e)               -- data to be replicated
              -> PreOpenAcc acc aenv (Array sh e)

  -- Index a sub-array out of an array; i.e., the dimensions not indexed
  -- are returned whole
  --
  Slice       :: SliceIndex slix sl co sh                       -- slice type specification
              -> acc            aenv (Array sh e)               -- array to be indexed
              -> Exp            aenv slix                       -- slice value specification
              -> PreOpenAcc acc aenv (Array sl e)

  -- Apply the given unary function to all elements of the given array
  --
  Map         :: TypeR e'
              -> Fun            aenv (e -> e')
              -> acc            aenv (Array sh e)
              -> PreOpenAcc acc aenv (Array sh e')

  -- Apply a given binary function pairwise to all elements of the given
  -- arrays. The length of the result is the length of the shorter of the
  -- two argument arrays.
  --
  ZipWith     :: TypeR e3
              -> Fun            aenv (e1 -> e2 -> e3)
              -> acc            aenv (Array sh e1)
              -> acc            aenv (Array sh e2)
              -> PreOpenAcc acc aenv (Array sh e3)

  -- Fold along the innermost dimension of an array with a given
  -- /associative/ function.
  --
  Fold        :: Fun            aenv (e -> e -> e)              -- combination function
              -> Maybe     (Exp aenv e)                         -- default value
              -> acc            aenv (Array (sh, Int) e)        -- folded array
              -> PreOpenAcc acc aenv (Array sh e)

  -- Segmented fold along the innermost dimension of an array with a given
  -- /associative/ function
  --
  FoldSeg     :: IntegralType i
              -> Fun            aenv (e -> e -> e)              -- combination function
              -> Maybe     (Exp aenv e)                         -- default value
              -> acc            aenv (Array (sh, Int) e)        -- folded array
              -> acc            aenv (Segments i)               -- segment descriptor
              -> PreOpenAcc acc aenv (Array (sh, Int) e)

  -- Haskell-style scan of a linear array with a given
  -- /associative/ function and optionally an initial element
  -- (which does not need to be the neutral of the associative operations)
  -- If no initial value is given, this is a scan1
  --
  Scan        :: Direction
              -> Fun            aenv (e -> e -> e)              -- combination function
              -> Maybe     (Exp aenv e)                         -- initial value
              -> acc            aenv (Array (sh, Int) e)
              -> PreOpenAcc acc aenv (Array (sh, Int) e)

  -- Like 'Scan', but produces a rightmost (in case of a left-to-right scan)
  -- fold value and an array with the same length as the input array (the
  -- fold value would be the rightmost element in a Haskell-style scan)
  --
  Scan'       :: Direction
              -> Fun            aenv (e -> e -> e)              -- combination function
              -> Exp            aenv e                          -- initial value
              -> acc            aenv (Array (sh, Int) e)
              -> PreOpenAcc acc aenv (Array (sh, Int) e, Array sh e)

  -- Generalised forward permutation is characterised by a permutation function
  -- that determines for each element of the source array where it should go in
  -- the output. The permutation can be between arrays of varying shape and
  -- dimensionality. This permutation function is implicit in this representation.
  --
  -- Other characteristics of the permutation function 'f':
  --
  --   1. 'f' is a (morally) partial function: only the elements of the domain
  --      for which the source array contains a 'Just' value are mapped in the
  --      result.
  --
  --   2. 'f' is not surjective: positions in the target array need not be
  --      picked up by the permutation function, so the target array must first
  --      be initialised from an array of default values.
  --
  --   3. 'f' is not injective: distinct elements of the domain may map to the
  --      same position in the target array. In this case the combination
  --      function is used to combine elements, which needs to be /associative/
  --      and /commutative/. When the combination function is missing (and thus
  --      set to `const`), we assume that 'f' is injective.
  --
  Permute     :: Maybe (Fun     aenv (e -> e -> e))                  -- combination function
              -> acc            aenv (Array sh' e)                   -- default values
              -> acc            aenv (Array sh (PrimMaybe (((),sh'), e))) -- source array with destination indices
              -> PreOpenAcc acc aenv (Array sh' e)

  -- Generalised multi-dimensional backwards permutation; the permutation can
  -- be between arrays of varying shape; the permutation function must be total
  --
  Backpermute :: ShapeR sh'
              -> Exp            aenv sh'                        -- dimensions of the result
              -> Fun            aenv (sh' -> sh)                -- permutation function
              -> acc            aenv (Array sh e)               -- source array
              -> PreOpenAcc acc aenv (Array sh' e)

  -- Map a stencil over an array.  In contrast to 'map', the domain of
  -- a stencil function is an entire /neighbourhood/ of each array element.
  --
  Stencil     :: StencilR sh e stencil
              -> TypeR e'
              -> Fun             aenv (stencil -> e')           -- stencil function
              -> Boundary        aenv (Array sh e)              -- boundary condition
              -> acc             aenv (Array sh e)              -- source array
              -> PreOpenAcc  acc aenv (Array sh e')

  -- Map a binary stencil over an array.
  --
  Stencil2    :: StencilR sh a stencil1
              -> StencilR sh b stencil2
              -> TypeR c
              -> Fun             aenv (stencil1 -> stencil2 -> c) -- stencil function
              -> Boundary        aenv (Array sh a)                -- boundary condition #1
              -> acc             aenv (Array sh a)                -- source array #1
              -> Boundary        aenv (Array sh b)                -- boundary condition #2
              -> acc             aenv (Array sh b)                -- source array #2
              -> PreOpenAcc acc  aenv (Array sh c)

-- | Vanilla boundary condition specification for stencil operations
--
data Boundary aenv t where
  -- Clamp coordinates to the extent of the array
  Clamp     :: Boundary aenv t

  -- Mirror coordinates beyond the array extent
  Mirror    :: Boundary aenv t

  -- Wrap coordinates around on each dimension
  Wrap      :: Boundary aenv t

  -- Use a constant value for outlying coordinates
  Constant  :: e
            -> Boundary aenv (Array sh e)

  -- Apply the given function to outlying coordinates
  Function  :: Fun aenv (sh -> e)
            -> Boundary aenv (Array sh e)


data ArrayInstr aenv f where
  -- Array shape.
  Shape       :: ArrayVar aenv (Array dim t) -> ArrayInstr aenv (() -> dim)

  -- Project a single scalar from an array.
  Index       :: ArrayVar aenv (Array dim t) -> ArrayInstr aenv (dim -> t)
  LinearIndex :: ArrayVar aenv (Array dim t) -> ArrayInstr aenv (Int -> t)

instance IsArrayInstr (ArrayInstr aenv) where
  arrayInstrType (Shape       (Var (ArrayR shr _) _)) = shapeType shr
  arrayInstrType (Index       (Var (ArrayR _  tp) _)) = tp
  arrayInstrType (LinearIndex (Var (ArrayR _  tp) _)) = tp

  liftArrayInstr (Shape       var) = [|| Shape       $$(liftArrayVar var) ||]
  liftArrayInstr (Index       var) = [|| Index       $$(liftArrayVar var) ||]
  liftArrayInstr (LinearIndex var) = [|| LinearIndex $$(liftArrayVar var) ||]

  rnfArrayInstr  (Shape       var) = rnfArrayVar var
  rnfArrayInstr  (Index       var) = rnfArrayVar var
  rnfArrayInstr  (LinearIndex var) = rnfArrayVar var

  showArrayInstrOp Shape{}         = "Shape"
  showArrayInstrOp Index{}         = "Index"
  showArrayInstrOp LinearIndex{}   = "LinearIndex"

  matchArrayInstr (Shape v1)       (Shape v2)       | Just Refl <- matchVar v1 v2 = Just Refl
  matchArrayInstr (Index v1)       (Index v2)       | Just Refl <- matchVar v1 v2 = Just Refl
  matchArrayInstr (LinearIndex v1) (LinearIndex v2) | Just Refl <- matchVar v1 v2 = Just Refl
  matchArrayInstr _                _                                              = Nothing

  encodeArrayInstr arr = case arr of
    Index a                     -> intHost $(hashQ ("Index" :: String))       <> encodeArrayVar a
    LinearIndex a               -> intHost $(hashQ ("LinearIndex" :: String)) <> encodeArrayVar a
    Shape a                     -> intHost $(hashQ ("Shape" :: String))       <> encodeArrayVar a

encodeArrayVar :: ArrayVar aenv a -> Hash.Builder
encodeArrayVar (Var repr v) = encodeArrayType repr <> encodeIdx v

-- | Vanilla open expressions using de Bruijn indices for variables ranging
-- over tuples of scalars and arrays of tuples. All code, except Cond, is
-- evaluated eagerly. N-tuples are represented as nested pairs.
--
-- The data type is parametrised over the representation type (not the
-- surface types).
--
type OpenExp env aenv = PreOpenExp (ArrayInstr aenv) env

-- | Vanilla open function abstraction
--
type OpenFun env aenv = PreOpenFun (ArrayInstr aenv) env

-- | Vanilla function without free scalar variables
--
type Fun aenv = OpenFun () aenv

-- | Vanilla expression without free scalar variables
--
type Exp aenv = OpenExp () aenv


-- Type utilities
-- --------------

class HasArraysR f where
  arraysR :: f aenv a -> ArraysR a

instance HasArraysR OpenAcc where
  arraysR (OpenAcc a) = arraysR a

arrayR :: HasArraysR f => f aenv (Array sh e) -> ArrayR (Array sh e)
arrayR a = case arraysR a of
  TupRsingle aR -> aR

instance HasArraysR acc => HasArraysR (PreOpenAcc acc) where
  arraysR (Alet _ _ body)             = arraysR body
  arraysR (Avar (Var aR _))           = TupRsingle aR
  arraysR (Apair as bs)               = TupRpair (arraysR as) (arraysR bs)
  arraysR Anil                        = TupRunit
  arraysR (Atrace _ _ bs)             = arraysR bs
  arraysR (Apply aR _ _)              = aR
  arraysR (Aforeign r _ _ _)          = r
  arraysR (Acond _ a _)               = arraysR a
  arraysR (Awhile _ (Alam lhs _) _)   = lhsToTupR lhs
  arraysR Awhile{}                    = error "I want my, I want my MTV!"
  arraysR (Use aR _)                  = TupRsingle aR
  arraysR (Unit tR _)                 = arraysRarray ShapeRz tR
  arraysR (Reshape sh _ a)            = let ArrayR _ tR = arrayR a
                                         in arraysRarray sh tR
  arraysR (Generate aR _ _)           = TupRsingle aR
  arraysR (Transform aR _ _ _ _)      = TupRsingle aR
  arraysR (Replicate slice _ a)       = let ArrayR _ tR = arrayR a
                                         in arraysRarray (sliceDomainR slice) tR
  arraysR (Slice slice a _)           = let ArrayR _ tR = arrayR a
                                         in arraysRarray (sliceShapeR slice) tR
  arraysR (Map tR _ a)                = let ArrayR sh _ = arrayR a
                                         in arraysRarray sh tR
  arraysR (ZipWith tR _ a _)          = let ArrayR sh _ = arrayR a
                                         in arraysRarray sh tR
  arraysR (Fold _ _ a)                = let ArrayR (ShapeRsnoc sh) tR = arrayR a
                                         in arraysRarray sh tR
  arraysR (FoldSeg _ _ _ a _)         = arraysR a
  arraysR (Scan _ _ _ a)              = arraysR a
  arraysR (Scan' _ _ _ a)             = let aR@(ArrayR (ShapeRsnoc sh) tR) = arrayR a
                                         in TupRsingle aR `TupRpair` TupRsingle (ArrayR sh tR)
  arraysR (Permute _ a _)             = arraysR a
  arraysR (Backpermute sh _ _ a)      = let ArrayR _ tR = arrayR a
                                         in arraysRarray sh tR
  arraysR (Stencil _ tR _ _ a)        = let ArrayR sh _ = arrayR a
                                         in arraysRarray sh tR
  arraysR (Stencil2 _ _ tR _ _ a _ _) = let ArrayR sh _ = arrayR a
                                         in arraysRarray sh tR

-- Normal form data
-- ================

instance NFData (OpenAfun aenv f) where
  rnf = rnfOpenAfun

instance NFData (OpenAcc aenv t) where
  rnf = rnfOpenAcc

instance NFData (OpenExp env aenv t) where
  rnf = rnfOpenExp

instance NFData (OpenFun env aenv t) where
  rnf = rnfOpenFun


type NFDataAcc acc = forall aenv t. acc aenv t -> ()

rnfOpenAfun :: OpenAfun aenv t -> ()
rnfOpenAfun = rnfPreOpenAfun rnfOpenAcc

rnfPreOpenAfun :: NFDataAcc acc -> PreOpenAfun acc aenv t -> ()
rnfPreOpenAfun rnfA (Abody b) = rnfA b
rnfPreOpenAfun rnfA (Alam lhs f) = rnfALeftHandSide lhs `seq` rnfPreOpenAfun rnfA f

rnfOpenAcc :: OpenAcc aenv t -> ()
rnfOpenAcc (OpenAcc pacc) = rnfPreOpenAcc rnfOpenAcc pacc

rnfPreOpenAcc :: forall acc aenv t. HasArraysR acc => NFDataAcc acc -> PreOpenAcc acc aenv t -> ()
rnfPreOpenAcc rnfA pacc =
  let
      rnfAF :: PreOpenAfun acc aenv' t' -> ()
      rnfAF = rnfPreOpenAfun rnfA

      rnfE :: OpenExp env' aenv' t' -> ()
      rnfE = rnfOpenExp

      rnfF :: OpenFun env' aenv' t' -> ()
      rnfF = rnfOpenFun

      rnfB :: ArrayR (Array sh e) -> Boundary aenv' (Array sh e) -> ()
      rnfB = rnfBoundary

      rnfM :: Message a -> ()
      rnfM (Message f g msg) = f `seq` rnfMaybe (`seq` ()) g `seq` rnf msg
  in
  case pacc of
    Alet lhs bnd body         -> rnfALeftHandSide lhs `seq` rnfA bnd `seq` rnfA body
    Avar var                  -> rnfArrayVar var
    Apair as bs               -> rnfA as `seq` rnfA bs
    Anil                      -> ()
    Atrace msg as bs          -> rnfM msg `seq` rnfA as `seq` rnfA bs
    Apply repr afun acc       -> rnfTupR rnfArrayR repr `seq` rnfAF afun `seq` rnfA acc
    Aforeign repr asm afun a  -> rnfTupR rnfArrayR repr `seq` rnf (strForeign asm) `seq` rnfAF afun `seq` rnfA a
    Acond p a1 a2             -> rnfE p `seq` rnfA a1 `seq` rnfA a2
    Awhile p f a              -> rnfAF p `seq` rnfAF f `seq` rnfA a
    Use repr arr              -> rnfArray repr arr
    Unit tp x                 -> rnfTypeR tp `seq` rnfE x
    Reshape shr sh a          -> rnfShapeR shr `seq` rnfE sh `seq` rnfA a
    Generate repr sh f        -> rnfArrayR repr `seq` rnfE sh `seq` rnfF f
    Transform repr sh p f a   -> rnfArrayR repr `seq` rnfE sh `seq` rnfF p `seq` rnfF f `seq` rnfA a
    Replicate slice sh a      -> rnfSliceIndex slice `seq` rnfE sh `seq` rnfA a
    Slice slice a sh          -> rnfSliceIndex slice `seq` rnfE sh `seq` rnfA a
    Map tp f a                -> rnfTypeR tp `seq` rnfF f `seq` rnfA a
    ZipWith tp f a1 a2        -> rnfTypeR tp `seq` rnfF f `seq` rnfA a1 `seq` rnfA a2
    Fold f z a                -> rnfF f `seq` rnfMaybe rnfE z `seq` rnfA a
    FoldSeg i f z a s         -> rnfIntegralType i `seq` rnfF f `seq` rnfMaybe rnfE z `seq` rnfA a `seq` rnfA s
    Scan d f z a              -> d `seq` rnfF f `seq` rnfMaybe rnfE z `seq` rnfA a
    Scan' d f z a             -> d `seq` rnfF f `seq` rnfE z `seq` rnfA a
    Permute f d a             -> rnfMaybe rnfF f `seq` rnfA d `seq` rnfA a
    Backpermute shr sh f a    -> rnfShapeR shr `seq` rnfE sh `seq` rnfF f `seq` rnfA a
    Stencil sr tp f b a       ->
      let
        TupRsingle (ArrayR shr _) = arraysR a
        repr                      = ArrayR shr $ stencilEltR sr
      in rnfStencilR sr `seq` rnfTupR rnfScalarType tp `seq` rnfF f `seq` rnfB repr b  `seq` rnfA a
    Stencil2 sr1 sr2 tp f b1 a1 b2 a2 ->
      let
        TupRsingle (ArrayR shr _) = arraysR a1
        repr1 = ArrayR shr $ stencilEltR sr1
        repr2 = ArrayR shr $ stencilEltR sr2
      in rnfStencilR sr1 `seq` rnfStencilR sr2 `seq` rnfTupR rnfScalarType tp `seq` rnfF f `seq` rnfB repr1 b1 `seq` rnfB repr2 b2 `seq` rnfA a1 `seq` rnfA a2

rnfArrayVar :: ArrayVar aenv a -> ()
rnfArrayVar = rnfVar rnfArrayR

rnfALeftHandSide :: ALeftHandSide arrs aenv aenv' -> ()
rnfALeftHandSide = rnfLeftHandSide rnfArrayR

rnfBoundary :: forall aenv sh e. ArrayR (Array sh e) -> Boundary aenv (Array sh e) -> ()
rnfBoundary _             Clamp        = ()
rnfBoundary _             Mirror       = ()
rnfBoundary _             Wrap         = ()
rnfBoundary (ArrayR _ tR) (Constant c) = rnfConst tR c
rnfBoundary _             (Function f) = rnfOpenFun f

-- Template Haskell
-- ================

type LiftAcc acc = forall aenv a. acc aenv a -> CodeQ (acc aenv a)

liftPreOpenAfun :: LiftAcc acc -> PreOpenAfun acc aenv t -> CodeQ (PreOpenAfun acc aenv t)
liftPreOpenAfun liftA (Alam lhs f) = [|| Alam $$(liftALeftHandSide lhs) $$(liftPreOpenAfun liftA f) ||]
liftPreOpenAfun liftA (Abody b)    = [|| Abody $$(liftA b) ||]

liftPreOpenAcc
    :: forall acc aenv a.
       HasArraysR acc
    => LiftAcc acc
    -> PreOpenAcc acc aenv a
    -> CodeQ (PreOpenAcc acc aenv a)
liftPreOpenAcc liftA pacc =
  let
      liftE :: OpenExp env aenv t -> CodeQ (OpenExp env aenv t)
      liftE = liftOpenExp

      liftF :: OpenFun env aenv t -> CodeQ (OpenFun env aenv t)
      liftF = liftOpenFun

      liftAF :: PreOpenAfun acc aenv f -> CodeQ (PreOpenAfun acc aenv f)
      liftAF = liftPreOpenAfun liftA

      liftB :: ArrayR (Array sh e) -> Boundary aenv (Array sh e) -> CodeQ (Boundary aenv (Array sh e))
      liftB = liftBoundary

      liftMF :: Maybe (OpenFun env aenv t) -> CodeQ (Maybe (OpenFun env aenv t))
      liftMF Nothing = [|| Nothing ||]
      liftMF (Just f) = [|| Just $$(liftF f) ||]
  in
  case pacc of
    Alet lhs bnd body         -> [|| Alet $$(liftALeftHandSide lhs) $$(liftA bnd) $$(liftA body) ||]
    Avar var                  -> [|| Avar $$(liftArrayVar var) ||]
    Apair as bs               -> [|| Apair $$(liftA as) $$(liftA bs) ||]
    Anil                      -> [|| Anil ||]
    Atrace msg as bs          -> [|| Atrace $$(liftMessage (arraysR as) msg) $$(liftA as) $$(liftA bs) ||]
    Apply repr f a            -> [|| Apply $$(liftArraysR repr) $$(liftAF f) $$(liftA a) ||]
    Aforeign repr asm f a     -> [|| Aforeign $$(liftArraysR repr) $$(liftForeign asm) $$(liftPreOpenAfun liftA f) $$(liftA a) ||]
    Acond p t e               -> [|| Acond $$(liftE p) $$(liftA t) $$(liftA e) ||]
    Awhile p f a              -> [|| Awhile $$(liftAF p) $$(liftAF f) $$(liftA a) ||]
    Use repr a                -> [|| Use $$(liftArrayR repr) $$(liftArray repr a) ||]
    Unit tp e                 -> [|| Unit $$(liftTypeR tp) $$(liftE e) ||]
    Reshape shr sh a          -> [|| Reshape $$(liftShapeR shr) $$(liftE sh) $$(liftA a) ||]
    Generate repr sh f        -> [|| Generate $$(liftArrayR repr) $$(liftE sh) $$(liftF f) ||]
    Transform repr sh p f a   -> [|| Transform $$(liftArrayR repr) $$(liftE sh) $$(liftF p) $$(liftF f) $$(liftA a) ||]
    Replicate slix sl a       -> [|| Replicate $$(liftSliceIndex slix) $$(liftE sl) $$(liftA a) ||]
    Slice slix a sh           -> [|| Slice $$(liftSliceIndex slix) $$(liftA a) $$(liftE sh) ||]
    Map tp f a                -> [|| Map $$(liftTypeR tp) $$(liftF f) $$(liftA a) ||]
    ZipWith tp f a b          -> [|| ZipWith $$(liftTypeR tp) $$(liftF f) $$(liftA a) $$(liftA b) ||]
    Fold f z a                -> [|| Fold $$(liftF f) $$(liftMaybe liftE z) $$(liftA a) ||]
    FoldSeg i f z a s         -> [|| FoldSeg $$(liftIntegralType i) $$(liftF f) $$(liftMaybe liftE z) $$(liftA a) $$(liftA s) ||]
    Scan d f z a              -> [|| Scan  $$(liftDirection d) $$(liftF f) $$(liftMaybe liftE z) $$(liftA a) ||]
    Scan' d f z a             -> [|| Scan' $$(liftDirection d) $$(liftF f) $$(liftE z) $$(liftA a) ||]
    Permute f d a             -> [|| Permute $$(liftMF f) $$(liftA d) $$(liftA a) ||]
    Backpermute shr sh p a    -> [|| Backpermute $$(liftShapeR shr) $$(liftE sh) $$(liftF p) $$(liftA a) ||]
    Stencil sr tp f b a       ->
      let TupRsingle (ArrayR shr _) = arraysR a
          repr = ArrayR shr $ stencilEltR sr
       in [|| Stencil $$(liftStencilR sr) $$(liftTypeR tp) $$(liftF f) $$(liftB repr b) $$(liftA a) ||]
    Stencil2 sr1 sr2 tp f b1 a1 b2 a2 ->
      let TupRsingle (ArrayR shr _) = arraysR a1
          repr1 = ArrayR shr $ stencilEltR sr1
          repr2 = ArrayR shr $ stencilEltR sr2
       in [|| Stencil2 $$(liftStencilR sr1) $$(liftStencilR sr2) $$(liftTypeR tp) $$(liftF f) $$(liftB repr1 b1) $$(liftA a1) $$(liftB repr2 b2) $$(liftA a2) ||]


liftALeftHandSide :: ALeftHandSide arrs aenv aenv' -> CodeQ (ALeftHandSide arrs aenv aenv')
liftALeftHandSide = liftLeftHandSide liftArrayR

liftArrayVar :: ArrayVar aenv a -> CodeQ (ArrayVar aenv a)
liftArrayVar = liftVar liftArrayR

liftDirection :: Direction -> CodeQ Direction
liftDirection LeftToRight = [|| LeftToRight ||]
liftDirection RightToLeft = [|| RightToLeft ||]

liftMessage :: ArraysR a -> Message a -> CodeQ (Message a)
liftMessage aR (Message _ fmt msg) =
  let
      -- We (ironically?) can't lift TExp, so nested occurrences must fall
      -- back to displaying in representation format
      fmtR :: ArraysR arrs' -> CodeQ (arrs' -> String)
      fmtR TupRunit                         = [|| \() -> "()" ||]
      fmtR (TupRsingle (ArrayR ShapeRz eR)) = [|| \as -> showElt $$(liftTypeR eR) $ linearIndexArray $$(liftTypeR eR) as 0 ||]
      fmtR (TupRsingle (ArrayR shR eR))     = [|| \as -> showArray (showsElt $$(liftTypeR eR)) (ArrayR $$(liftShapeR shR) $$(liftTypeR eR)) as ||]
      fmtR aR'                              = [|| \as -> showArrays $$(liftArraysR aR') as ||]
  in
  [|| Message $$(fromMaybe (fmtR aR) fmt) Nothing $$(TH.unsafeCodeCoerce (TH.lift msg)) ||]

liftBoundary
    :: forall aenv sh e.
       ArrayR (Array sh e)
    -> Boundary aenv (Array sh e)
    -> CodeQ (Boundary aenv (Array sh e))
liftBoundary _             Clamp        = [|| Clamp ||]
liftBoundary _             Mirror       = [|| Mirror ||]
liftBoundary _             Wrap         = [|| Wrap ||]
liftBoundary (ArrayR _ tp) (Constant v) = [|| Constant $$(liftElt tp v) ||]
liftBoundary _             (Function f) = [|| Function $$(liftOpenFun f) ||]

formatDirection :: Format r (Direction -> r)
formatDirection = later $ \case
  LeftToRight -> singleton 'l'
  RightToLeft -> singleton 'r'

formatPreAccOp :: Format r (PreOpenAcc acc aenv arrs -> r)
formatPreAccOp = later $ \case
  Alet{}            -> "Alet"
  Avar (Var _ ix)   -> bformat ("Avar a" % int) (idxToInt ix)
  Use aR a          -> bformat ("Use " % string) (showArrayShort 5 (showsElt (arrayRtype aR)) aR a)
  Atrace{}          -> "Atrace"
  Apply{}           -> "Apply"
  Aforeign{}        -> "Aforeign"
  Acond{}           -> "Acond"
  Awhile{}          -> "Awhile"
  Apair{}           -> "Apair"
  Anil              -> "Anil"
  Unit{}            -> "Unit"
  Generate{}        -> "Generate"
  Transform{}       -> "Transform"
  Reshape{}         -> "Reshape"
  Replicate{}       -> "Replicate"
  Slice{}           -> "Slice"
  Map{}             -> "Map"
  ZipWith{}         -> "ZipWith"
  Fold _ z _        -> bformat ("Fold" % maybed "1" (fconst mempty)) z
  FoldSeg _ _ z _ _ -> bformat ("Fold" % maybed "1" (fconst mempty) % "Seg") z
  Scan d _ z _      -> bformat ("Scan" % formatDirection % maybed "1" (fconst mempty)) d z
  Scan' d _ _ _     -> bformat ("Scan" % formatDirection % "\'") d
  Permute{}         -> "Permute"
  Backpermute{}     -> "Backpermute"
  Stencil{}         -> "Stencil"
  Stencil2{}        -> "Stencil2"
