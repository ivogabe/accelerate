{-# LANGUAGE CPP                  #-}
{-# LANGUAGE ConstraintKinds      #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE InstanceSigs         #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE PatternGuards        #-}
{-# LANGUAGE RankNTypes           #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE ViewPatterns         #-}
{-# OPTIONS_GHC -fno-warn-incomplete-patterns #-} -- TODO: remove this & fix warnings
{-# OPTIONS_GHC -fno-warn-name-shadowing      #-}
-- |
-- Module      : Data.Array.Accelerate.Trafo.Fusion
-- Copyright   : [2012..2019] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--
-- This module implements producer/producer and consumer/producer fusion as a
-- term rewriting of the Accelerate AST.
--
-- The function 'quench' perform the source-to-source fusion transformation,
-- while 'anneal' additionally makes the representation of embedded producers
-- explicit by representing the AST as a 'DelayedAcc' of manifest and delayed
-- nodes.
--

module Data.Array.Accelerate.Trafo.Fusion (

  -- ** Types
  DelayedAcc, DelayedOpenAcc(..),
  DelayedAfun, DelayedOpenAfun,

  -- ** Conversion
  convertAcc,  convertAccWith,
  convertAfun, convertAfunWith,

) where

-- standard library
import Prelude                                          hiding ( exp, until )

-- friends
import Data.BitSet
import Data.Array.Accelerate.AST
import Data.Array.Accelerate.Error
import Data.Array.Accelerate.Trafo.Base
import Data.Array.Accelerate.Trafo.Config
import Data.Array.Accelerate.Trafo.Shrink
import Data.Array.Accelerate.Trafo.Simplify
import Data.Array.Accelerate.Trafo.Substitution
import Data.Array.Accelerate.Array.Representation       hiding (fromIndex, toIndex, shape)
import Data.Array.Accelerate.Analysis.Match
import Data.Array.Accelerate.Type

import Data.Array.Accelerate.Debug.Flags                ( array_fusion )
import qualified Data.Array.Accelerate.Debug.Stats      as Stats
#ifdef ACCELERATE_DEBUG
import System.IO.Unsafe -- for debugging
#endif


-- Delayed Array Fusion
-- ====================

-- | Apply the fusion transformation to a closed de Bruijn AST
--
convertAcc :: Acc arrs -> DelayedAcc arrs
convertAcc = convertAccWith defaultOptions

convertAccWith :: Config -> Acc arrs -> DelayedAcc arrs
convertAccWith config = withSimplStats . convertOpenAcc config

-- | Apply the fusion transformation to a function of array arguments
--
convertAfun :: Afun f -> DelayedAfun f
convertAfun = convertAfunWith defaultOptions

convertAfunWith :: Config -> Afun f -> DelayedAfun f
convertAfunWith config = withSimplStats . convertOpenAfun config

-- -- | Apply the fusion transformation to the array computations embedded
-- --   in a sequence computation.
-- convertSeq :: Bool -> Seq a -> DelayedSeq a
-- convertSeq fuseAcc (embedSeq (embedOpenAcc fuseAcc) -> ExtendSeq aenv s)
--   = withSimplStats (DelayedSeq (cvtE aenv) (convertOpenSeq fuseAcc s))
--   where
--     cvtE :: Extend OpenAcc aenv aenv' -> Extend DelayedOpenAcc aenv aenv'
--     cvtE BaseEnv                                          = BaseEnv
--     cvtE (PushEnv env a) | a' <- convertOpenAcc fuseAcc a = PushEnv (cvtE env) a'

withSimplStats :: a -> a
#ifdef ACCELERATE_DEBUG
withSimplStats x = unsafePerformIO Stats.resetSimplCount `seq` x
#else
withSimplStats x = x
#endif


-- | Apply the fusion transformation to an AST. This consists of two phases:
--
--    1. A bottom-up traversal that converts nodes into the internal delayed
--       representation, merging adjacent producer/producer pairs.
--
--    2. A top-down traversal that makes the representation of fused
--       consumer/producer pairs explicit as a 'DelayedAcc' of manifest and
--       delayed nodes.
--
-- TLM: Note that there really is no ambiguity as to which state an array will
--      be in following this process: an array will be either delayed or
--      manifest, and the two helper functions are even named as such! We should
--      encode this property in the type somehow...
--
convertOpenAcc :: Config -> OpenAcc aenv arrs -> DelayedOpenAcc aenv arrs
convertOpenAcc config = manifest config . computeAcc . embedOpenAcc config

-- Convert array computations into an embeddable delayed representation.
-- Reapply the embedding function from the first pass and unpack the
-- representation. It is safe to match on BaseEnv because the first pass
-- will put producers adjacent to the term consuming it.
--
delayed :: Config -> OpenAcc aenv (Array sh e) -> DelayedOpenAcc aenv (Array sh e)
delayed config (embedOpenAcc config -> Embed env cc)
  | BaseEnv <- env
  = case simplify cc of
      Done v                                                -> avarsIn v
      Yield repr sh f                                       -> Delayed repr sh f (f `compose` fromIndex (arrayRshape repr) sh)
      Step  repr sh p f v
        | Just Refl <- match sh (arrayShape v)
        , Just Refl <- isIdentity p                         -> Delayed repr sh (f `compose` indexArray v) (f `compose` linearIndex v)
        | f'        <- f `compose` indexArray v `compose` p -> Delayed repr sh f' (f' `compose` fromIndex (arrayRshape repr) sh)
  --
  | otherwise
  = manifest config (computeAcc (Embed env cc))


-- Convert array programs as manifest terms.
--
manifest :: Config -> OpenAcc aenv a -> DelayedOpenAcc aenv a
manifest config (OpenAcc pacc) =
  let fusionError = $internalError "manifest" "unexpected fusible materials"
  in
  Manifest $ case pacc of
    -- Non-fusible terms
    -- -----------------
    Avar ix                 -> Avar ix
    Use repr arr            -> Use repr arr
    Unit tp e               -> Unit tp e
    Alet lhs bnd body       -> alet lhs (manifest config bnd) (manifest config body)
    Acond p t e             -> Acond p (manifest config t) (manifest config e)
    Awhile p f a            -> Awhile (cvtAF p) (cvtAF f) (manifest config a)
    Apair a1 a2             -> Apair (manifest config a1) (manifest config a2)
    Anil                    -> Anil
    Apply repr f a          -> apply repr (cvtAF f) (manifest config a)
    Aforeign repr ff f a    -> Aforeign repr ff (cvtAF f) (manifest config a)

    -- Producers
    -- ---------
    --
    -- Some producers might still exist as a manifest array. Typically this
    -- is because they are the last stage of the computation, or the result
    -- of a let-binding to be used multiple times. The input array here
    -- should be a evaluated array term, else something went wrong.
    --
    Map tp f a              -> Map tp f (delayed config a)
    Generate repr sh f      -> Generate repr sh f
    Transform repr sh p f a -> Transform repr sh p f (delayed config a)
    Backpermute shr sh p a  -> Backpermute shr sh p (delayed config a)
    Reshape slr sl a        -> Reshape slr sl (manifest config a)

    Replicate{}             -> fusionError
    Slice{}                 -> fusionError
    ZipWith{}               -> fusionError

    -- Consumers
    -- ---------
    --
    -- Embed producers directly into the representation. For delayed terms
    -- with local bindings, these will have been floated up above the
    -- consumer already
    --
    Fold f z a              -> Fold     f z (delayed config a)
    Fold1 f a               -> Fold1    f (delayed config a)
    FoldSeg i f z a s       -> FoldSeg  i f z (delayed config a) (delayed config s)
    Fold1Seg i f a s        -> Fold1Seg i f (delayed config a) (delayed config s)
    Scanl f z a             -> Scanl    f z (delayed config a)
    Scanl1 f a              -> Scanl1   f (delayed config a)
    Scanl' f z a            -> Scanl'   f z (delayed config a)
    Scanr f z a             -> Scanr    f z (delayed config a)
    Scanr1 f a              -> Scanr1   f (delayed config a)
    Scanr' f z a            -> Scanr'   f z (delayed config a)
    Permute f d p a         -> Permute  f (manifest config d) p (delayed config a)
    Stencil s tp f x a      -> Stencil  s tp f x (delayed config a)
    Stencil2 s1 s2 tp f x a y b
                            -> Stencil2 s1 s2 tp f x (delayed config a) y (delayed config b)
    -- Collect s               -> Collect  (cvtS s)

    where
      -- Flatten needless let-binds, which can be introduced by the
      -- conversion to the internal embeddable representation.
      --
      alet :: ALeftHandSide a aenv aenv'
           -> DelayedOpenAcc aenv a
           -> DelayedOpenAcc aenv' b
           -> PreOpenAcc DelayedOpenAcc aenv b
      alet lhs bnd body
        | Just bodyVars  <- extractArrayVars body
        , Just Refl      <- bindingIsTrivial lhs bodyVars
        , Manifest x     <- bnd
        = x
        --
        | otherwise
        = Alet lhs bnd body

      -- Eliminate redundant application to an identity function. This
      -- arises in the use of pipe to avoid fusion and force its argument
      -- to be evaluated, i.e.:
      --
      -- > compute :: Acc a -> Acc a
      -- > compute = id >-> id
      --
      apply :: ArraysR b
            -> PreOpenAfun DelayedOpenAcc aenv (a -> b)
            ->             DelayedOpenAcc aenv a
            -> PreOpenAcc  DelayedOpenAcc aenv b
      apply repr afun x
        | Alam lhs (Abody body)   <- afun
        , Just bodyVars           <- extractArrayVars body
        , Just Refl               <- bindingIsTrivial lhs bodyVars
        , Manifest x'             <- x
        = Stats.ruleFired "applyD/identity" x'
        --
        | otherwise
        = Apply repr afun x

      cvtAF :: OpenAfun aenv f -> PreOpenAfun DelayedOpenAcc aenv f
      cvtAF (Alam lhs f) = Alam lhs (cvtAF f)
      cvtAF (Abody b)    = Abody (manifest config b)

      -- cvtS :: PreOpenSeq OpenAcc aenv senv s -> PreOpenSeq DelayedOpenAcc aenv senv s
      -- cvtS = convertOpenSeq config

convertOpenAfun :: Config -> OpenAfun aenv f -> DelayedOpenAfun aenv f
convertOpenAfun c (Alam lhs f) = Alam lhs (convertOpenAfun c f)
convertOpenAfun c (Abody b) = Abody (convertOpenAcc  c b)

{--
convertOpenSeq :: Config -> PreOpenSeq OpenAcc aenv senv a -> PreOpenSeq DelayedOpenAcc aenv senv a
convertOpenSeq config s =
  case s of
    Consumer c          -> Consumer (cvtC c)
    Reify ix            -> Reify ix
    Producer p s'       -> Producer p' (convertOpenSeq config s')
      where
        p' = case p of
               StreamIn arrs     -> StreamIn arrs
               ToSeq slix sh a   -> ToSeq slix sh (delayed config a)
               MapSeq f x        -> MapSeq (cvtAF f) x
               ChunkedMapSeq f x -> ChunkedMapSeq (cvtAF f) x
               ZipWithSeq f x y  -> ZipWithSeq (cvtAF f) x y
               ScanSeq f e x     -> ScanSeq (cvtF f) (cvtE e) x
  where
    cvtC :: Consumer OpenAcc aenv senv a -> Consumer DelayedOpenAcc aenv senv a
    cvtC c =
      case c of
        FoldSeq f e x        -> FoldSeq (cvtF f) (cvtE e) x
        FoldSeqFlatten f a x -> FoldSeqFlatten (cvtAF f) (manifest config a) x
        Stuple t             -> Stuple (cvtCT t)

    cvtCT :: Atuple (Consumer OpenAcc aenv senv) t -> Atuple (Consumer DelayedOpenAcc aenv senv) t
    cvtCT NilAtup        = NilAtup
    cvtCT (SnocAtup t c) = SnocAtup (cvtCT t) (cvtC c)

    cvtAF :: OpenAfun aenv f -> PreOpenAfun DelayedOpenAcc aenv f
    cvtAF (Alam f)  = Alam  (cvtAF f)
    cvtAF (Abody b) = Abody (manifest config b)

    cvtE :: OpenExp env aenv t -> DelayedOpenExp env aenv t
    cvtE = convertOpenExp config

    cvtF :: OpenFun env aenv f -> DelayedOpenFun env aenv f
    cvtF (Lam f)  = Lam (cvtF f)
    cvtF (Body b) = Body (cvtE b)
--}


-- | Apply the fusion transformation to the AST to combine and simplify terms.
-- This converts terms into the internal delayed array representation and merges
-- adjacent producer/producer terms. Using the reduced internal form limits the
-- number of combinations that need to be considered.
--
type EmbedAcc acc = forall aenv arrs. acc aenv arrs -> Embed acc aenv arrs
type ElimAcc  acc = forall aenv s t. acc aenv s -> acc (aenv,s) t -> Bool

embedOpenAcc :: Config -> OpenAcc aenv arrs -> Embed OpenAcc aenv arrs
embedOpenAcc config (OpenAcc pacc) =
  embedPreAcc config (embedOpenAcc config) elimOpenAcc pacc
  where
    -- When does the cost of re-computation outweigh that of memory access? For
    -- the moment only do the substitution on a single use of the bound array
    -- into the use site, but it is likely advantageous to be far more
    -- aggressive here.
    --
    -- SEE: [Sharing vs. Fusion]
    --
    elimOpenAcc :: ElimAcc OpenAcc
    elimOpenAcc _bnd body
      | count False ZeroIdx body <= lIMIT = True
      | otherwise                         = False
      where
        lIMIT = 1

        count :: UsesOfAcc OpenAcc
        count no ix (OpenAcc pacc) = usesOfPreAcc no count ix pacc


embedPreAcc
    :: forall acc aenv arrs. Kit acc
    => Config
    -> EmbedAcc   acc
    -> ElimAcc    acc
    -> PreOpenAcc acc aenv arrs
    -> Embed      acc aenv arrs
embedPreAcc config embedAcc elimAcc pacc
  = unembed
  $ case pacc of

    -- Non-fusible terms
    -- -----------------
    --
    -- Solid and semi-solid terms that we generally do not wish to fuse, such
    -- as control flow (|?), array introduction (use, unit), array tupling and
    -- projection, and foreign function operations. Generally we also do not
    -- want to fuse past array let bindings, as this would imply work
    -- duplication. SEE: [Sharing vs. Fusion]
    --
    Alet lhs bnd body   -> aletD embedAcc elimAcc lhs bnd body
    Anil                -> done $ Anil
    Acond p at ae       -> acondD embedAcc (cvtE p) at ae
    Apply repr f a      -> done $ Apply repr (cvtAF f) (cvtA a)
    Awhile p f a        -> done $ Awhile (cvtAF p) (cvtAF f) (cvtA a)
    Apair a1 a2         -> done $ Apair (cvtA a1) (cvtA a2)
    Aforeign repr ff f a -> done $ Aforeign repr ff (cvtAF f) (cvtA a)
    -- Collect s           -> collectD s

    -- Array injection
    Avar v              -> done $ Avar v
    Use repr arr        -> done $ Use repr arr
    Unit tp e           -> done $ Unit tp (cvtE e)

    -- Producers
    -- ---------
    --
    -- The class of operations that given a set of zero or more input arrays,
    -- produce a _single_ element for the output array by manipulating a
    -- _single_ element from each input array. These can be further classified
    -- as value (map, zipWith) or index space (backpermute, slice, replicate)
    -- transformations.
    --
    -- The critical feature is that each element of the output is produced
    -- independently of all others, and so we can aggressively fuse arbitrary
    -- sequences of these operations.
    --
    Generate repr sh f  -> generateD repr (cvtE sh) (cvtF f)

    Map tp f a          -> mapD tp (cvtF f) (embedAcc a)
    ZipWith tp f a b    -> fuse2 (into (zipWithD tp) (cvtF f)) a b
    Transform repr sh p f a -> transformD repr (cvtE sh) (cvtF p) (cvtF f) (embedAcc a)

    Backpermute slr sl p a
                        -> fuse (into2 (backpermuteD slr) (cvtE sl) (cvtF p)) a
    Slice slix a sl     -> fuse (into  (sliceD slix)      (cvtE sl)) a
    Replicate slix sh a -> fuse (into  (replicateD slix)  (cvtE sh)) a
    Reshape slr sl a    -> reshapeD slr (embedAcc a) (cvtE sl)

    -- Consumers
    -- ---------
    --
    -- Operations where each element of the output array depends on multiple
    -- elements of the input array. To implement these operations efficiently in
    -- parallel, we need to know how elements of the array depend on each other:
    -- a parallel scan is implemented very differently from a parallel fold, for
    -- example.
    --
    -- In order to avoid obfuscating this crucial information required for
    -- parallel implementation, fusion is separated into to phases:
    -- producer/producer, implemented above, and consumer/producer, which is
    -- implemented below. This will place producers adjacent to the consumer
    -- node, so that the producer can be directly embedded into the consumer
    -- during the code generation phase.
    --
    Fold f z a          -> embed  repr  (into2 Fold           (cvtF f) (cvtE z)) a
    Fold1 f a           -> embed  repr  (into  Fold1          (cvtF f)) a
    FoldSeg i f z a s   -> embed2 repr  (into2 (FoldSeg i)    (cvtF f) (cvtE z)) a s
    Fold1Seg i f a s    -> embed2 repr  (into  (Fold1Seg i)   (cvtF f)) a s
    Scanl f z a         -> embed  repr  (into2 Scanl          (cvtF f) (cvtE z)) a
    Scanl1 f a          -> embed  repr  (into  Scanl1         (cvtF f)) a
    Scanl' f z a        -> embed  repr  (into2 Scanl'         (cvtF f) (cvtE z)) a
    Scanr f z a         -> embed  repr  (into2 Scanr          (cvtF f) (cvtE z)) a
    Scanr1 f a          -> embed  repr  (into  Scanr1         (cvtF f)) a
    Scanr' f z a        -> embed  repr  (into2 Scanr'         (cvtF f) (cvtE z)) a
    Permute f d p a     -> embed2 repr  (into2 permute        (cvtF f) (cvtF p)) d a
    Stencil s t f x a   -> embed  repr  (into2 (stencil1 s t) (cvtF f) (cvtB x)) a
    Stencil2 s1 s2 t f x a y b
                        -> embed2 repr  (into3 (stencil2 s1 s2 t) (cvtF f) (cvtB x) (cvtB y)) a b

  where
    repr = arraysRepr pacc
    -- If fusion is not enabled, force terms to the manifest representation
    --
    unembed :: Embed acc aenv arrs -> Embed acc aenv arrs
    unembed x
      | array_fusion `member` options config = x
      | Embed env cc <- x
      , pacc <- compute cc
      = case extractArrayVars $ inject pacc of
          Just vars -> Embed env $ Done vars
          _
            | DeclareVars lhs _ value <- declareVars (arraysRepr pacc)
              -> Embed (PushEnv env lhs $ inject pacc) $ Done $ value weakenId

    cvtA :: acc aenv' a -> acc aenv' a
    cvtA = computeAcc . embedAcc

    cvtAF :: PreOpenAfun acc aenv' f -> PreOpenAfun acc aenv' f
    cvtAF (Alam lhs f) = Alam lhs (cvtAF f)
    cvtAF (Abody a) = Abody (cvtA a)

    -- Helpers to shuffle the order of arguments to a constructor
    --
    permute f p d a     = Permute f d p a

    -- NOTE: [Stencil fusion]
    --
    -- We allow stencils to delay their argument arrays with no special
    -- considerations. This means that the delayed function will be evaluated
    -- _at every element_ of the stencil pattern. We should do some analysis of
    -- when this duplication is beneficial (keeping in mind that the stencil
    -- implementations themselves may share neighbouring elements).
    --
    stencil1 s t f x a          = Stencil  s     t f x a
    stencil2 s1 s2 t f x y a b  = Stencil2 s1 s2 t f x a y b

    -- Conversions for closed scalar functions and expressions. This just
    -- applies scalar simplifications.
    --
    cvtF :: Fun aenv' t -> Fun aenv' t
    cvtF = simplify

    cvtE :: Exp aenv' t -> Exp aenv' t
    cvtE = simplify

    cvtB :: Boundary aenv' t -> Boundary aenv' t
    cvtB Clamp        = Clamp
    cvtB Mirror       = Mirror
    cvtB Wrap         = Wrap
    cvtB (Constant c) = Constant c
    cvtB (Function f) = Function (cvtF f)

    -- Helpers to embed and fuse delayed terms
    --
    into :: Sink f => (f env' a -> b) -> f env a -> Extend ArrayR acc env env' -> b
    into op a env = op (sinkA env a)

    into2 :: (Sink f1, Sink f2)
          => (f1 env' a -> f2 env' b -> c) -> f1 env a -> f2 env b -> Extend ArrayR acc env env' -> c
    into2 op a b env = op (sinkA env a) (sinkA env b)

    into3 :: (Sink f1, Sink f2, Sink f3)
          => (f1 env' a -> f2 env' b -> f3 env' c -> d) -> f1 env a -> f2 env b -> f3 env c -> Extend ArrayR acc env env' -> d
    into3 op a b c env = op (sinkA env a) (sinkA env b) (sinkA env c)

    -- Operations which can be fused into consumers. Move all of the local
    -- bindings out of the way so that the fusible function operates
    -- directly on the delayed representation. See also: [Representing
    -- delayed arrays]
    --
    fuse :: (forall aenv'. Extend ArrayR acc aenv aenv' -> Cunctation aenv' as -> Cunctation aenv' bs)
         ->       acc aenv as
         -> Embed acc aenv bs
    fuse op (embedAcc -> Embed env cc) = Embed env (op env cc)

    fuse2 :: (forall aenv'. Extend ArrayR acc aenv aenv' -> Cunctation aenv' as -> Cunctation aenv' bs -> Cunctation aenv' cs)
          ->       acc aenv as
          ->       acc aenv bs
          -> Embed acc aenv cs
    fuse2 op a1 a0
      | Embed env1 cc1  <- embedAcc a1
      , Embed env0 cc0  <- embedAcc (sinkA env1 a0)
      , env             <- env1 `append` env0
      = Embed env (op env (sinkA env0 cc1) cc0)

    -- Consumer operations which will be evaluated.
    --
    -- NOTE: [Fusion and the lowest common use site]
    --
    -- The AST given to us by sharing recovery will place let bindings at
    -- the lowest common use site for that shared term. For example:
    --
    --   fold f z (let a0 = ..
    --                 a1 = ..
    --              in zipWith g a0 a1)
    --
    -- In order to enable producer/consumer fusion for the above example,
    -- it is necessary to float the let bindings above the `fold`
    -- operation; SEE: [Sharing vs. Fusion] for more information.
    --
    -- Furthermore, we used to maintain an invariant that all (manifest)
    -- arguments were supplied as array variables, for example:
    --
    --   fold1 f (let a0 = ..               let a0 = ..
    --             in stencil g a0)   ==>       a1 = stencil g a0
    --                                          a2 = fold1 f a1
    --
    -- However, if the argument term will be evaluated (i.e. can not be
    -- fused into the producer) then it is better that we do _not_ float
    -- those terms, and instead leave them under the consumer. This helps
    -- to syntactically constrain the "liveness" of terms: if the argument
    -- to an operation is not an array variable, we can see directly that
    -- this will be the last use-site of that array. In particular, this is
    -- useful for the 'permute' operation to know when it can in-place
    -- update the array of default values.
    --
    embed :: ArraysR bs
          -> (forall aenv'. Extend ArrayR acc aenv aenv' -> acc aenv' as -> PreOpenAcc acc aenv' bs)
          ->       acc aenv as
          -> Embed acc aenv bs
    embed reprBs op (embedAcc -> Embed env cc)
      | Done{} <- cc
      , DeclareVars lhs _ value <- declareVars reprBs
      = Embed (PushEnv BaseEnv lhs $ inject (op BaseEnv (computeAcc (Embed env cc)))) $ Done $ value weakenId
      | otherwise
      -- Next line is duplicated for both branches, as the type variable for the environment is instantiated differently
      , DeclareVars lhs _ value <- declareVars reprBs
      = Embed (PushEnv env     lhs $ inject (op env     (inject (compute cc))))       $ Done $ value weakenId

    embed2 :: ArraysR cs
           -> (forall aenv'. Extend ArrayR acc aenv aenv' -> acc aenv' as -> acc aenv' bs -> PreOpenAcc acc aenv' cs)
           ->       acc aenv as
           ->       acc aenv bs
           -> Embed acc aenv cs
    embed2 reprCs op (embedAcc -> Embed env1 cc1) a0
      | Done{}          <- cc1
      , a1              <- computeAcc (Embed env1 cc1)
      = embed reprCs (\env0 -> op env0 (sinkA env0 a1)) a0
      --
      | Embed env0 cc0  <- embedAcc (sinkA env1 a0)
      , env             <- env1 `append` env0
      = case cc0 of
          Done{}
            | DeclareVars lhs _ value <- declareVars reprCs
              -> Embed (PushEnv env1 lhs $ inject (op env1 (inject (compute cc1)) (computeAcc (Embed env0 cc0))))      $ Done $ value weakenId
          _
            -- Next line is duplicated for both branches, as the type variable for the environment is instantiated differently
            | DeclareVars lhs _ value <- declareVars reprCs
              -> Embed (PushEnv env  lhs $ inject (op env  (inject (compute (sinkA env0 cc1))) (inject (compute cc0)))) $ Done $ value weakenId

    -- trav1 :: (Arrays as, Arrays bs)
    --       => (forall aenv'. Embed acc aenv' as -> Embed acc aenv' as)
    --       -> (forall aenv'. Extend ArrayR acc aenv aenv' -> acc aenv' as -> PreOpenAcc acc aenv' bs)
    --       ->       acc aenv as
    --       -> Embed acc aenv bs
    -- trav1 f op (f . embedAcc -> Embed env cc)
    --   = Embed (env `pushArrayEnv` inject (op env (inject (compute cc)))) doneZeroIdx

    -- trav2 :: (Arrays as, Arrays bs, Arrays cs)
    --       => (forall aenv'. Embed acc aenv' as -> Embed acc aenv' as)
    --       -> (forall aenv'. Embed acc aenv' bs -> Embed acc aenv' bs)
    --       -> (forall aenv'. Extend ArrayR acc aenv aenv' -> acc aenv' as -> acc aenv' bs -> PreOpenAcc acc aenv' cs)
    --       ->       acc aenv as
    --       ->       acc aenv bs
    --       -> Embed acc aenv cs
    -- trav2 f1 f0 op (f1 . embedAcc -> Embed env1 cc1) (f0 . embedAcc . sinkA env1 -> Embed env0 cc0)
    --   | env     <- env1 `append` env0
    --   , acc1    <- inject . compute $ sinkA env0 cc1
    --   , acc0    <- inject . compute $ cc0
    --   = Embed (env `pushArrayEnv` inject (op env acc1 acc0)) doneZeroIdx

    -- force :: Arrays as => Embed acc aenv' as -> Embed acc aenv' as
    -- force (Embed env cc)
    --   | Done{} <- cc = Embed env                                  cc
    --   | otherwise    = Embed (env `pushArrayEnv` inject (compute cc)) doneZeroIdx

    -- -- Move additional bindings for producers outside of the sequence, so that
    -- -- producers may fuse with their arguments resulting in actual sequencing
    -- collectD :: PreOpenSeq acc aenv () arrs
    --          -> Embed acc aenv arrs
    -- collectD (embedSeq embedAcc -> ExtendSeq env s')
    --   = Embed (env `pushArrayEnv` inject (Collect s')) doneZeroIdx


{--
-- Move additional bindings for producer outside of sequence, so
-- that producers may fuse with their arguments, resulting in
-- actual sequencing.
embedSeq :: forall acc aenv arrs. Kit acc
         => EmbedAcc acc
         -> PreOpenSeq acc aenv () arrs
         -> ExtendSeq       acc aenv () arrs
embedSeq embedAcc s
  = travS s BaseEnv
  where
    travS :: forall senv aenv' arrs'.
             PreOpenSeq acc aenv senv arrs'
          -> Extend acc aenv aenv'
          -> ExtendSeq acc aenv senv arrs'
    travS s env =
      case s of
        Producer p s
          | ExtendSeq env' s' <- travS s env
          , ExtendProducer env'' p' <- travP p env'
          -> ExtendSeq (env' `append` env'') (Producer p' (sinkSeq env'' s'))
        Consumer c
          | c' <- travC c env
          -> ExtendSeq env (Consumer c')
        Reify ix
          -> ExtendSeq env (Reify ix)

    travP :: forall arrs' aenv' senv.
             Producer acc aenv senv arrs'
          -> Extend acc aenv aenv'
          -> ExtendProducer acc aenv' senv arrs'
    travP (ToSeq slix sh a) env
      | Embed env' cc <- embedAcc (sink env a)
      = ExtendProducer env' (ToSeq slix sh (inject (compute cc)))
    travP (StreamIn arrs) _          = ExtendProducer BaseEnv (StreamIn arrs)
    travP (MapSeq f x) env           = ExtendProducer BaseEnv (MapSeq (cvtAF (sink env f)) x)
    travP (ChunkedMapSeq f x) env    = ExtendProducer BaseEnv (ChunkedMapSeq (cvtAF (sink env f)) x)
    travP (ZipWithSeq f x y) env     = ExtendProducer BaseEnv (ZipWithSeq (cvtAF (sink env f)) x y)
    travP (ScanSeq f e x) env        = ExtendProducer BaseEnv (ScanSeq (cvtF (sink env f)) (cvtE (sink env e)) x)

    travC :: forall arrs' aenv' senv.
             Consumer acc aenv senv arrs'
          -> Extend acc aenv aenv'
          -> Consumer acc aenv' senv arrs'
    travC (FoldSeq f e x) env = FoldSeq (cvtF (sink env f)) (cvtE (sink env e)) x
    travC (FoldSeqFlatten f a x) env = FoldSeqFlatten (cvtAF (sink env f)) (cvtA (sink env a)) x
    travC (Stuple t) env = Stuple (cvtCT t)
      where
        cvtCT :: Atuple (Consumer acc aenv senv) t -> Atuple (Consumer acc aenv' senv) t
        cvtCT NilAtup        = NilAtup
        cvtCT (SnocAtup t c) = SnocAtup (cvtCT t) (travC c env)

    cvtE :: Elt t => Exp aenv' t -> Exp aenv' t
    cvtE = simplify

    cvtF :: Fun aenv' t -> Fun aenv' t
    cvtF = simplify

    cvtA :: Arrays a => acc aenv' a -> acc aenv' a
    cvtA = computeAcc . embedAcc

    cvtAF :: PreOpenAfun acc aenv' f -> PreOpenAfun acc aenv' f
    cvtAF (Alam  f) = Alam  (cvtAF f)
    cvtAF (Abody a) = Abody (cvtA a)


-- A sequence with additional bindings
data ExtendSeq acc aenv senv arrs where
  ExtendSeq :: forall acc aenv aenv' senv arrs.
                Extend acc aenv aenv'
             -> PreOpenSeq acc aenv' senv arrs
             -> ExtendSeq acc aenv senv arrs

-- A producer with additional bindings
data ExtendProducer acc aenv senv arrs where
  ExtendProducer :: forall acc aenv aenv' senv arrs.
                    Extend acc aenv aenv'
                 -> Producer acc aenv' senv arrs
                 -> ExtendProducer acc aenv senv arrs
--}


-- Internal representation
-- =======================

-- NOTE: [Representing delayed arrays]
--
-- During the fusion transformation we represent terms as a pair consisting of
-- a collection of supplementary environment bindings and a description of how
-- to construct the array.
--
-- It is critical to separate these two. To create a real AST node we need both
-- the environment and array term, but analysis of how to fuse terms requires
-- only the array description. If the additional bindings are bundled as part of
-- the representation, the existentially quantified extended environment type
-- will be untouchable. This is problematic because the terms of the two arrays
-- are defined with respect to this existentially quantified type, and there is
-- no way to directly combine these two environments:
--
--   append :: Extend ArrayR env env1 -> Extend ArrayR env env2 -> Extend ArrayR env ???
--
-- And hence, no way to combine the terms of the delayed representation.
--
-- The only way to bring terms into the same scope is to operate via the
-- manifest terms. This entails a great deal of conversion between delayed and
-- AST terms, but is certainly possible.
--
-- However, because of the limited scope into which this existential type is
-- available, we ultimately perform this process many times. In fact, complexity
-- of the fusion algorithm for an AST of N terms becomes O(r^n), where r is the
-- number of different rules we have for combining terms.
--
data Embed acc aenv a where
  Embed :: Extend ArrayR acc aenv aenv'
        -> Cunctation             aenv' a
        -> Embed         acc aenv       a

instance HasArraysRepr acc => HasArraysRepr (Embed acc) where
  arraysRepr (Embed _ c) = arraysRepr c

-- Cunctation (n): the action or an instance of delaying; a tardy action.
--
-- This describes the ways in which the fusion transformation represents
-- intermediate arrays. The fusion process operates by recasting producer array
-- computations in terms of a set of scalar functions used to construct an
-- element at each index, and fusing successive producers by combining these
-- scalar functions.
--
data Cunctation aenv a where

  -- The base case is just a real (manifest) array term. No fusion happens here.
  -- Note that the array is referenced by an index into the extended
  -- environment, ensuring that the array is manifest and making the term
  -- non-recursive in 'acc'.
  --
  Done  :: ArrayVars  aenv arrs
        -> Cunctation aenv arrs

  -- We can represent an array by its shape and a function to compute an element
  -- at each index.
  --
  Yield :: ArrayR (Array sh e)
        -> Exp        aenv sh
        -> Fun        aenv (sh -> e)
        -> Cunctation aenv (Array sh e)

  -- A more restrictive form than 'Yield' may afford greater opportunities for
  -- optimisation by a backend. This more structured form applies an index and
  -- value transform to an input array. Note that the transform is applied to an
  -- array stored as an environment index, so that the term is non-recursive and
  -- it is always possible to embed into a collective operation.
  --
  Step  :: ArrayR (Array sh' b)
        -> Exp        aenv sh'
        -> Fun        aenv (sh' -> sh)
        -> Fun        aenv (a   -> b)
        -> ArrayVar   aenv (Array sh  a)
        -> Cunctation aenv (Array sh' b)

instance Simplify (Cunctation aenv a) where
  simplify = \case
    Done v                                                    -> Done v
    Yield repr (simplify -> sh) (simplify -> f)               -> Yield repr sh f
    Step  repr (simplify -> sh) (simplify -> p) (simplify -> f) v
      | Just Refl <- match sh (arrayShape v)
      , Just Refl <- isIdentity p
      , Just Refl <- isIdentity f                             -> Done $ VarsSingle v
      | otherwise                                             -> Step repr sh p f v

instance HasArraysRepr Cunctation where
  arraysRepr (Done v)            = varsType v
  arraysRepr (Yield repr _ _)    = TupRsingle repr
  arraysRepr (Step repr _ _ _ _) = TupRsingle repr

-- Convert a real AST node into the internal representation
--
done :: Kit acc => PreOpenAcc acc aenv a -> Embed acc aenv a
done pacc
  | Just vars <- extractArrayVars $ inject pacc
  = Embed BaseEnv (Done vars)
  | DeclareVars lhs _ value <- declareVars (arraysRepr pacc)
  = Embed (PushEnv BaseEnv lhs $ inject pacc) $ Done $ value weakenId

doneZeroIdx :: ArrayR (Array sh e) -> Cunctation (aenv, Array sh e) (Array sh e)
doneZeroIdx repr = Done $ VarsSingle $ Var repr ZeroIdx

-- Recast a cunctation into a mapping from indices to elements.
--
yield :: Cunctation aenv (Array sh e)
      -> Cunctation aenv (Array sh e)
yield cc =
  case cc of
    Yield{}             -> cc
    Step repr sh p f v  -> Yield repr sh (f `compose` indexArray v `compose` p)
    Done (VarsSingle v@(Var repr _))
                        -> Yield repr (arrayShape v) (indexArray v)


-- Recast a cunctation into transformation step form. Not possible if the source
-- was in the Yield formulation.
--
step :: Cunctation aenv (Array sh e)
     -> Maybe (Cunctation aenv (Array sh e))
step cc =
  case cc of
    Yield{}             -> Nothing
    Step{}              -> Just cc
    Done (VarsSingle v@(Var repr@(ArrayR shr tp) _))
                        -> Just $ Step repr (arrayShape v) (identity $ shapeType shr) (identity tp) v


-- Get the shape of a delayed array
--
shape :: Cunctation aenv (Array sh e) -> Exp aenv sh
shape cc
  | Just (Step _ sh _ _ _) <- step cc     = sh
  | Yield _ sh _           <- yield cc    = sh


-- Environment manipulation
-- ========================

instance Sink Cunctation where
  weaken k = \case
    Done v              -> Done (weaken k v)
    Step repr sh p f v  -> Step  repr (weaken k sh) (weaken k p) (weaken k f) (weaken k v)
    Yield repr sh f     -> Yield repr (weaken k sh) (weaken k f)

-- prjExtend :: Kit acc => Extend acc env env' -> Idx env' t -> PreOpenAcc acc env' t
-- prjExtend (PushEnv _   v) ZeroIdx       = weakenA rebuildAcc SuccIdx v
-- prjExtend (PushEnv env _) (SuccIdx idx) = weakenA rebuildAcc SuccIdx $ prjExtend env idx
-- prjExtend _               _             = $internalError "prjExtend" "inconsistent valuation"

{--
-- Rearrange type arguments to fit with Sink type class.
newtype SinkSeq acc senv aenv a = SinkSeq { unSinkSeq :: PreOpenSeq acc aenv senv a }

-- sink for sequences.
sinkSeq :: Kit acc => Extend acc aenv aenv' -> PreOpenSeq acc aenv senv a -> PreOpenSeq acc aenv' senv a
sinkSeq env s = unSinkSeq $ sink env (SinkSeq s)

instance Kit acc => Sink (SinkSeq acc senv) where
  weaken :: forall aenv aenv' arrs. aenv :> aenv' -> SinkSeq acc senv aenv arrs -> SinkSeq acc senv aenv' arrs
  weaken k (SinkSeq s) = SinkSeq $
    case s of
      Producer p s' -> Producer   (weakenP p) (weakenL s')
      Consumer c    -> Consumer   (weakenC c)
      Reify ix      -> Reify      ix

    where
      weakenL :: forall senv' arrs'. PreOpenSeq acc aenv senv' arrs' -> PreOpenSeq acc aenv' senv' arrs'
      weakenL s' = unSinkSeq (weaken k (SinkSeq s'))

      weakenP :: forall a. Producer acc aenv senv a -> Producer acc aenv' senv a
      weakenP p =
        case p of
          StreamIn arrs        -> StreamIn arrs
          ToSeq slix sh a      -> ToSeq slix sh (weaken k a)
          MapSeq f x           -> MapSeq (weaken k f) x
          ChunkedMapSeq f x    -> ChunkedMapSeq (weaken k f) x
          ZipWithSeq f x y     -> ZipWithSeq (weaken k f) x y
          ScanSeq f a x        -> ScanSeq (weaken k f) (weaken k a) x

      weakenC :: forall a. Consumer acc aenv senv a -> Consumer acc aenv' senv a
      weakenC c =
        case c of
          FoldSeq f a x        -> FoldSeq (weaken k f) (weaken k a) x
          FoldSeqFlatten f a x -> FoldSeqFlatten (weaken k f) (weaken k a) x
          Stuple t             ->
            let wk :: Atuple (Consumer acc aenv senv) t -> Atuple (Consumer acc aenv' senv) t
                wk NilAtup        = NilAtup
                wk (SnocAtup t c) = wk t `SnocAtup` weakenC c
            in
            Stuple (wk t)
--}

-- Array fusion of a de Bruijn computation AST
-- ===========================================

-- Array computations
-- ------------------

-- Evaluate a delayed computation and tie the recursive knot
--
-- We do a bit of extra work to (try to) maintain that terms should be left
-- at their lowest common use site. SEE: [Fusion and the lowest common use site]
--
computeAcc :: Kit acc => Embed acc aenv arrs -> acc aenv arrs
computeAcc (Embed      BaseEnv              cc) = inject (compute cc)
computeAcc (Embed env@(PushEnv bot lhs top) cc) =
  case simplify cc of
    Done v          -> bindA env (avarsIn v)
    Yield repr sh f -> bindA env (inject (Generate repr sh f))
    Step repr sh p f v@(Var _ ix)
      | Just Refl <- match sh (arrayShape v)
      , Just Refl <- isIdentity p
      -> case ix of
           ZeroIdx
             | LeftHandSideSingle ArrayR{} <- lhs
             , Just (OpenAccFun g) <- strengthen noTop (OpenAccFun f)
                  -> bindA bot (inject (Map (arrayRtype repr) g top))
           _      -> bindA env (inject (Map (arrayRtype repr) f (avarIn v)))

      | Just Refl <- isIdentity f
      -> case ix of
           ZeroIdx
             | LeftHandSideSingle ArrayR{} <- lhs
             , Just (OpenAccFun q)  <- strengthen noTop (OpenAccFun p)
             , Just (OpenAccExp sz) <- strengthen noTop (OpenAccExp sh)
                  -> bindA bot (inject (Backpermute (arrayRshape repr) sz q top))
           _      -> bindA env (inject (Backpermute (arrayRshape repr) sh p (avarIn v)))

      | otherwise
      -> case ix of
           ZeroIdx
             | LeftHandSideSingle ArrayR{} <- lhs
             , Just (OpenAccFun g)  <- strengthen noTop (OpenAccFun f)
             , Just (OpenAccFun q)  <- strengthen noTop (OpenAccFun p)
             , Just (OpenAccExp sz) <- strengthen noTop (OpenAccExp sh)
                  -> bindA bot (inject (Transform repr sz q g top))
           _      -> bindA env (inject (Transform repr sh p f (avarIn v)))

  where
    bindA :: Kit acc
          => Extend ArrayR acc aenv aenv'
          ->               acc      aenv' a
          ->               acc aenv       a
    bindA BaseEnv             b = b
    bindA (PushEnv env lhs a) b
      -- If the freshly bound value is directly, returned, we don't have to bind it in a
      -- let. We can do this if the left hand side does not contain wildcards (other than
      -- wildcards for unit / nil) and if the value contains the same variables.
      | Just vars <- extractArrayVars b
      , Just Refl <- bindingIsTrivial lhs vars = bindA env a
      | otherwise                              = bindA env (inject (Alet lhs a b))

    noTop :: (aenv, a) :?> aenv
    noTop ZeroIdx      = Nothing
    noTop (SuccIdx ix) = Just ix


-- Convert the internal representation of delayed arrays into a real AST
-- node. Use the most specific version of a combinator whenever possible.
--
compute :: Kit acc => Cunctation aenv arrs -> PreOpenAcc acc aenv arrs
compute cc = case simplify cc of
  Done VarsNil                              -> Anil
  Done (VarsSingle v@(Var ArrayR{} _))      -> Avar v
  Done (VarsPair v1 v2)                     -> avarsIn v1 `Apair` avarsIn v2
  Yield repr  sh f                          -> Generate repr sh f
  Step (ArrayR shr tp) sh p f v
    | Just Refl <- match sh (arrayShape v)
    , Just Refl <- isIdentity p             -> Map tp f (avarIn v)
    | Just Refl <- isIdentity f             -> Backpermute shr sh p (avarIn v)
    | otherwise                             -> Transform (ArrayR shr tp) sh p f (avarIn v)


-- Representation of a generator as a delayed array
--
generateD :: ArrayR (Array sh e)
          -> Exp aenv sh
          -> Fun aenv (sh -> e)
          -> Embed  acc aenv (Array sh e)
generateD repr sh f
  = Stats.ruleFired "generateD"
  $ Embed BaseEnv (Yield repr sh f)


-- Fuse a unary function into a delayed array. Also looks for unzips which can
-- be executed in constant time; SEE [unzipD]
--
mapD :: Kit acc
     => TupleType b
     -> Fun aenv (a -> b)
     -> Embed  acc aenv (Array sh a)
     -> Embed  acc aenv (Array sh b)
mapD tp f (unzipD tp f -> Just a) = a
mapD tp f (Embed env cc)
  = Stats.ruleFired "mapD"
  $ Embed env (go cc)
  where
    go (step  -> Just (Step (ArrayR shr _) sh ix g v)) = Step  (ArrayR shr tp) sh ix (sinkA env f `compose` g) v
    go (yield -> Yield (ArrayR shr _) sh g)            = Yield (ArrayR shr tp) sh    (sinkA env f `compose` g)


-- If we are unzipping a manifest array then force the term to be computed;
-- a backend will be able to execute this in constant time.
--
unzipD
    :: Kit acc
    => TupleType b
    -> Fun aenv (a -> b)
    -> Embed  acc aenv (Array sh a)
    -> Maybe (Embed acc aenv (Array sh b))
unzipD tp f (Embed env cc@(Done v))
  | Lam lhs (Body a) <- f
  , Just vars <- extractExpVars a
  , ArrayR shr _ <- arrayRepr cc
  , f' <- Lam lhs $ Body $ evars vars = Just $ Embed (env `pushArrayEnv` inject (Map tp f' $ avarsIn v)) $ doneZeroIdx $ ArrayR shr tp

unzipD _ _ _
  = Nothing

-- Fuse an index space transformation function that specifies where elements in
-- the destination array read there data from in the source array.
--
backpermuteD
    :: ShapeR sh'
    -> Exp        aenv sh'
    -> Fun        aenv (sh' -> sh)
    -> Cunctation aenv (Array sh  e)
    -> Cunctation aenv (Array sh' e)
backpermuteD shr' sh' p = Stats.ruleFired "backpermuteD" . go
  where
    go (step  -> Just (Step (ArrayR _ tp) _ q f v)) = Step  (ArrayR shr' tp) sh' (q `compose` p) f v
    go (yield -> Yield (ArrayR _ tp) _ g)           = Yield (ArrayR shr' tp) sh' (g `compose` p)


-- Transform as a combined map and backwards permutation
--
transformD
    :: Kit acc
    => ArrayR (Array sh' b)
    -> Exp aenv sh'
    -> Fun aenv (sh' -> sh)
    -> Fun aenv (a   -> b)
    -> Embed  acc aenv (Array sh  a)
    -> Embed  acc aenv (Array sh' b)
transformD (ArrayR shr' tp) sh' p f
  = Stats.ruleFired "transformD"
  . fuse (into2 (backpermuteD shr') sh' p)
  . mapD tp f
  where
    fuse :: (forall aenv'. Extend ArrayR acc aenv aenv' -> Cunctation aenv' as -> Cunctation aenv' bs)
         -> Embed acc aenv as
         -> Embed acc aenv bs
    fuse op (Embed env cc) = Embed env (op env cc)

    into2 :: (Sink f1, Sink f2)
          => (f1 env' a -> f2 env' b -> c) -> f1 env a -> f2 env b -> Extend ArrayR acc env env' -> c
    into2 op a b env = op (sinkA env a) (sinkA env b)


-- Replicate as a backwards permutation
--
-- TODO: If we have a pattern such as `replicate sh (map f xs)` then in some
--       cases it might be beneficial to not fuse these terms, if `f` is
--       expensive and/or `sh` is large.
--
replicateD
    :: SliceIndex slix sl co sh
    -> Exp        aenv slix
    -> Cunctation aenv (Array sl e)
    -> Cunctation aenv (Array sh e)
replicateD sliceIndex slix cc
  = Stats.ruleFired "replicateD"
  $ backpermuteD (sliceDomainR sliceIndex) (IndexFull sliceIndex slix (shape cc)) (extend sliceIndex slix) cc


-- Dimensional slice as a backwards permutation
--
sliceD
    :: SliceIndex slix sl co sh
    -> Exp            aenv slix
    -> Cunctation aenv (Array sh e)
    -> Cunctation aenv (Array sl e)
sliceD sliceIndex slix cc
  = Stats.ruleFired "sliceD"
  $ backpermuteD (sliceShapeR sliceIndex) (IndexSlice sliceIndex slix (shape cc)) (restrict sliceIndex slix) cc


-- Reshape an array
--
-- For delayed arrays this is implemented as an index space transformation. For
-- manifest arrays this can be done with the standard Reshape operation in
-- constant time without executing any array operations. This does not affect
-- the fusion process since the term is already manifest.
--
-- TLM: there was a runtime check to ensure the old and new shapes contained the
--      same number of elements: this has been lost for the delayed cases!
--
reshapeD
    :: Kit acc
    => ShapeR sl
    -> Embed  acc aenv (Array sh e)
    -> Exp aenv sl
    -> Embed  acc aenv (Array sl e)
reshapeD slr (Embed env cc) (sinkA env -> sl)
  | Done v <- cc
  = Embed (env `pushArrayEnv` inject (Reshape slr sl (avarsIn v))) $ doneZeroIdx repr

  | otherwise
  = Stats.ruleFired "reshapeD"
  $ Embed env (backpermuteD slr sl (reindex (arrayRshape $ arrayRepr cc) (shape cc) slr sl) cc)

  where
    ArrayR _ tp = arrayRepr cc
    repr        = ArrayR slr tp


-- Combine two arrays element-wise with a binary function to produce a delayed
-- array.
--
zipWithD :: TupleType c
         -> Fun        aenv (a -> b -> c)
         -> Cunctation aenv (Array sh a)
         -> Cunctation aenv (Array sh b)
         -> Cunctation aenv (Array sh c)
zipWithD tp f cc1 cc0
  -- Two stepper functions identically accessing the same array can be kept in
  -- stepping form. This might yield a simpler final term.
  --
  | Just (Step (ArrayR shr _) sh1 p1 f1 v1) <- step cc1
  , Just (Step _              sh0 p0 f0 v0) <- step cc0
  , Just Refl                   <- match v1 v0
  , Just Refl                   <- match p1 p0
  = Stats.ruleFired "zipWithD/step"
  $ Step (ArrayR shr tp) (mkIntersect shr sh1 sh0) p0 (combine f f1 f0) v0

  -- Otherwise transform both delayed terms into (index -> value) mappings and
  -- combine the two indexing functions that way.
  --
  | Yield (ArrayR shr _) sh1 f1 <- yield cc1
  , Yield _              sh0 f0 <- yield cc0
  = Stats.ruleFired "zipWithD"
  $ Yield (ArrayR shr tp) (mkIntersect shr sh1 sh0) (combine f f1 f0)

  where
    combine :: forall aenv a b c e.
               Fun aenv (a -> b -> c)
            -> Fun aenv (e -> a)
            -> Fun aenv (e -> b)
            -> Fun aenv (e -> c)
    combine c ixa ixb
      | Lam lhs1 (Body ixa')          <- ixa                          -- else the skolem 'e' will escape
      , Lam lhs2 (Body ixb')          <- ixb
      -- The two LeftHandSides may differ in the use of wildcards. If they do not match, we must
      -- combine them as done in `combineLhs`. As this will probably not occur often and requires
      -- additional weakening, we do a quick check whether the left hand sides are equal.
      --
      = case matchELeftHandSide lhs1 lhs2 of
          Just Refl
            | Lam lhsA (Lam lhsB (Body c')) <- weakenE (weakenWithLHS lhs1) c
              -> Lam lhs1 $ Body $ Let lhsA ixa'  $ Let lhsB (weakenE (weakenWithLHS lhsA)       ixb') c'
          Nothing
            | CombinedLHS lhs k1 k2 <- combineLhs lhs1 lhs2
            , Lam lhsA (Lam lhsB (Body c')) <- weakenE (weakenWithLHS lhs) c
            , ixa'' <- weakenE k1 ixa'
              -> Lam lhs  $ Body $ Let lhsA ixa'' $ Let lhsB (weakenE (weakenWithLHS lhsA .> k2) ixb') c'

combineLhs :: LeftHandSide s t env env1' -> LeftHandSide s t env env2' -> CombinedLHS s t env1' env2' env
combineLhs = go weakenId weakenId
  where
    go :: env1 :> env -> env2 :> env -> LeftHandSide s t env1 env1' -> LeftHandSide s t env2 env2' -> CombinedLHS s t env1' env2' env
    go k1 k2 (LeftHandSideWildcard tp) (LeftHandSideWildcard _) = CombinedLHS (LeftHandSideWildcard tp)    k1        k2
    go k1 k2 (LeftHandSideSingle tp)   (LeftHandSideSingle _)   = CombinedLHS (LeftHandSideSingle tp)      (sink k1) (sink k2)
    go k1 k2 (LeftHandSidePair l1 h1)  (LeftHandSidePair l2 h2)
      | CombinedLHS l k1'  k2'  <- go k1  k2  l1 l2
      , CombinedLHS h k1'' k2'' <- go k1' k2' h1 h2             = CombinedLHS (LeftHandSidePair l h)       k1''      k2''
    go k1 k2 (LeftHandSideWildcard _)  lhs
      | Exists lhs' <- rebuildLHS lhs                           = CombinedLHS lhs'        (weakenWithLHS lhs' .> k1) (sinkWithLHS lhs lhs' k2)
    go k1 k2 lhs                       (LeftHandSideWildcard _)
      | Exists lhs' <- rebuildLHS lhs                           = CombinedLHS lhs'        (sinkWithLHS lhs lhs' k1)  (weakenWithLHS lhs' .> k2)

data CombinedLHS s t env1' env2' env where
  CombinedLHS :: LeftHandSide s t env env' -> env1' :> env' -> env2' :> env' -> CombinedLHS s t env1' env2' env

-- NOTE: [Sharing vs. Fusion]
--
-- The approach to array fusion is similar to that the first generation of Repa.
-- It was discovered that the most immediately pressing problem with delayed
-- arrays in Repa-1 was that it did not preserve sharing of collective
-- operations, leading to excessive recomputation and severe repercussions on
-- performance if the user did not explicitly intervene.
--
-- However, as we have explicit sharing information in the term tree, so it is
-- straightforward to respect sharing by not fusing let-bindings, as that
-- introduces work duplication. However, sometimes we can be cleverer.
--
-- let-floating:
-- -------------
--
-- If the binding is of manifest data, we can instead move the let-binding to a
-- different point in the program and then continue to fuse into the body. This
-- is done by adding the bound term to the Extend environment. In essence this
-- is covering a different occurrence of the same problem Extend was introduced
-- to handle: let bindings of manifest data unnecessarily get in the way of the
-- fusion process. For example:
--
--   map f (zipWith g xs (map h xs))
--
-- after sharing recovery results in:
--
--   map f (let a0 = xs in zipWith g a0 (map h a0))
--
-- Without allowing the binding for a0 to float outwards, `map f` will not be
-- fused into the rest of the program.
--
-- let-elimination:
-- ----------------
--
-- Array binding points appear in the program because the array data _or_ shape
-- was accessed multiple times in the source program. In general we want to fuse
-- arbitrary sequences of array _data_, irrespective of how the shape component
-- is used. For example, reverse is defined in the prelude as:
--
--   reverse xs = let len  = unindex1 (shape xs)
--                    pf i = len - i - 1
--                in
--                backpermute (shape xs) (ilift1 pf) xs
--
-- Sharing recovery introduces a let-binding for the input `xs` since it is used
-- thrice in the definition, which impedes subsequent fusion. However the actual
-- array data is only accessed once, with the remaining two uses querying the
-- array shape. Since the delayed terms contain the shape of the array they
-- represent as a scalar term, if the data component otherwise satisfies the
-- rules for fusing terms, as it does in this example, we can eliminate the
-- let-binding by pushing the scalar shape and value generation terms directly
-- into the body.
--
-- Let-elimination can also be used to _introduce_ work duplication, which may
-- be beneficial if we can estimate that the cost of re-computation is less than
-- the cost of completely evaluating the array and subsequently retrieving the
-- data from memory.
--
-- let-binding:
-- ------------
--
-- Ultimately, we might not want to eliminate the binding. If so, evaluate it
-- and add it to a _clean_ Extend environment for the body. If not, the Extend
-- list effectively _flattens_ all bindings, so any terms required for the bound
-- term get lifted out to the same scope as the body. This increases their
-- lifetime and hence raises the maximum memory used. If we don't do this, we
-- get terms such as:
--
--   let a0  = <terms for binding> in
--   let bnd = <bound term> in
--   <body term>
--
-- rather than the following, where the scope of a0 is clearly only availably
-- when evaluating the bound term, as it should be:
--
--   let bnd =
--     let a0 = <terms for binding>
--     in <bound term>
--   in <body term>
--
aletD :: Kit acc
      => EmbedAcc acc
      -> ElimAcc  acc
      -> ALeftHandSide arrs aenv aenv'
      ->          acc aenv  arrs
      ->          acc aenv' brrs
      -> Embed    acc aenv  brrs
aletD embedAcc elimAcc lhs (embedAcc -> Embed env1 cc1) acc0

  -- let-floating
  -- ------------
  --
  -- Immediately inline the variable referring to the bound expression into the
  -- body, instead of adding to the environments and creating an indirection
  -- that must be later eliminated by shrinking.
  --
  | LeftHandSideSingle _                  <- lhs
  , Done (VarsSingle v1@(Var ArrayR{} _)) <- cc1
  , Embed env0 cc0                        <- embedAcc $ rebuildA (subAtop (Avar v1) . sink1 env1) acc0
  = Stats.ruleFired "aletD/float"
  $ Embed (env1 `append` env0) cc0

  -- Ensure we only call 'embedAcc' once on the body expression
  --
  | otherwise
  = aletD' embedAcc elimAcc lhs (Embed env1 cc1) (embedAcc acc0)


aletD' :: forall acc aenv aenv' arrs brrs. Kit acc
       => EmbedAcc acc
       -> ElimAcc  acc
       -> ALeftHandSide arrs aenv aenv'
       -> Embed    acc aenv  arrs
       -> Embed    acc aenv' brrs
       -> Embed    acc aenv  brrs
aletD' embedAcc elimAcc (LeftHandSideSingle ArrayR{}) (Embed env1 cc1) (Embed env0 cc0)

  -- let-binding
  -- -----------
  --
  -- Check whether we can eliminate the let-binding. Note that we must inspect
  -- the entire term, not just the Cunctation that would be produced by
  -- embedAcc. If we don't we can be left with dead terms that don't get
  -- eliminated. This problem occurred in the canny program.
  --
  | acc1    <- computeAcc (Embed env1 cc1)
  , False   <- elimAcc acc1 acc0
  = Stats.ruleFired "aletD/bind"
  $ Embed (BaseEnv `pushArrayEnv` acc1 `append` env0) cc0

  -- let-elimination
  -- ---------------
  --
  -- Handle the remaining cases in a separate function. It turns out that this
  -- is important so we aren't excessively sinking/delaying terms.
  --
  | acc0'   <- sink1 env1 acc0
  = Stats.ruleFired "aletD/eliminate"
  $ case cc1 of
      Step{}  -> eliminate env1 cc1 acc0'
      Yield{} -> eliminate env1 cc1 acc0'

  where
    acc0 :: acc aenv' brrs
    acc0 = computeAcc (Embed env0 cc0)

    -- The second part of let-elimination. Splitting into two steps exposes the
    -- extra type variables, and ensures we don't do extra work manipulating the
    -- body when not necessary (which can lead to a complexity blowup).
    --
    eliminate :: forall aenv aenv' sh e brrs.
                 Extend ArrayR acc aenv aenv'
              -> Cunctation             aenv' (Array sh e)
              ->               acc     (aenv', Array sh e) brrs
              -> Embed         acc aenv                    brrs
    eliminate env1 cc1 body
      | Done v1                  <- cc1
      , VarsSingle v1'@(Var r _) <- v1  = elim r (arrayShape v1') (indexArray v1')
      | Step r sh1 p1 f1 v1      <- cc1 = elim r sh1 (f1 `compose` indexArray v1 `compose` p1)
      | Yield r sh1 f1           <- cc1 = elim r sh1 f1
      where
        bnd :: PreOpenAcc acc aenv' (Array sh e)
        bnd = compute cc1

        elim :: ArrayR (Array sh e) -> Exp aenv' sh -> Fun aenv' (sh -> e) -> Embed acc aenv brrs
        elim r sh1 f1
          | sh1'              <- weaken (weakenSucc' weakenId) sh1
          , f1'               <- weaken (weakenSucc' weakenId) f1
          , Embed env0' cc0'  <- embedAcc $ rebuildA (subAtop bnd) $ kmap (replaceA sh1' f1' $ Var r ZeroIdx) body
          = Embed (env1 `append` env0') cc0'

    -- As part of let-elimination, we need to replace uses of array variables in
    -- scalar expressions with an equivalent expression that generates the
    -- result directly
    --
    -- TODO: when we inline bindings we ought to let bind at the first
    --       occurrence and use a variable at all subsequent locations. At the
    --       moment we are just hoping CSE in the simplifier phase does good
    --       things, but that is limited in what it looks for.
    --
    replaceE :: forall env aenv sh e t.
                OpenExp env aenv sh -> OpenFun env aenv (sh -> e) -> ArrayVar aenv (Array sh e)
             -> OpenExp env aenv t
             -> OpenExp env aenv t
    replaceE sh' f' avar@(Var (ArrayR shr _) _) exp =
      case exp of
        Let lhs x y                     -> let k = weakenWithLHS lhs
                                           in  Let lhs (cvtE x) (replaceE (weakenE k sh') (weakenE k f') avar y)
        Evar var                        -> Evar var
        Foreign tp ff f e               -> Foreign tp ff f (cvtE e)
        Const tp c                      -> Const tp c
        Undef tp                        -> Undef tp
        Nil                             -> Nil
        Pair e1 e2                      -> Pair (cvtE e1) (cvtE e2)
        IndexSlice x ix sh              -> IndexSlice x (cvtE ix) (cvtE sh)
        IndexFull x ix sl               -> IndexFull x (cvtE ix) (cvtE sl)
        ToIndex shr' sh ix              -> ToIndex shr' (cvtE sh) (cvtE ix)
        FromIndex shr' sh i             -> FromIndex shr' (cvtE sh) (cvtE i)
        Cond p t e                      -> Cond (cvtE p) (cvtE t) (cvtE e)
        PrimConst c                     -> PrimConst c
        PrimApp g x                     -> PrimApp g (cvtE x)
        ShapeSize shr' sh               -> ShapeSize shr' (cvtE sh)
        While p f x                     -> While (replaceF sh' f' avar p) (replaceF sh' f' avar f) (cvtE x)
        Coerce t1 t2 e                  -> Coerce t1 t2 (cvtE e)

        Shape a
          | Just Refl <- match a avar   -> Stats.substitution "replaceE/shape" sh'
          | otherwise                   -> exp

        Index a sh
          | Just Refl    <- match a avar
          , Lam lhs (Body b) <- f'      -> Stats.substitution "replaceE/!" . cvtE $ Let lhs sh b
          | otherwise                   -> Index a (cvtE sh)

        LinearIndex a i
          | Just Refl    <- match a avar
          , Lam lhs (Body b) <- f'
                                        -> Stats.substitution "replaceE/!!" . cvtE
                                         $ Let lhs
                                               (Let (LeftHandSideSingle scalarTypeInt) i $ FromIndex shr (weakenE (weakenSucc' weakenId) sh') $ Evar $ Var scalarTypeInt ZeroIdx)
                                               b
          | otherwise                   -> LinearIndex a (cvtE i)

      where
        cvtE :: OpenExp env aenv s -> OpenExp env aenv s
        cvtE = replaceE sh' f' avar

    replaceF :: forall env aenv sh e t.
                OpenExp env aenv sh -> OpenFun env aenv (sh -> e) -> ArrayVar aenv (Array sh e)
             -> OpenFun env aenv t
             -> OpenFun env aenv t
    replaceF sh' f' avar fun =
      case fun of
        Body e          -> Body (replaceE sh' f' avar e)
        Lam lhs f       -> let k = weakenWithLHS lhs
                           in  Lam lhs (replaceF (weakenE k sh') (weakenE k f') avar f)

    replaceA :: forall aenv sh e a.
                Exp aenv sh -> Fun aenv (sh -> e) -> ArrayVar aenv (Array sh e)
             -> PreOpenAcc acc aenv a
             -> PreOpenAcc acc aenv a
    replaceA sh' f' avar pacc =
      case pacc of
        Avar v
          | Just Refl <- match v avar   -> Avar avar
          | otherwise                   -> Avar v

        Alet lhs bnd (body :: acc aenv1 a) ->
          let w :: aenv :> aenv1
              w    = weakenWithLHS lhs
              sh'' = weaken w sh'
              f''  = weaken w f'
          in
          Alet lhs (cvtA bnd) (kmap (replaceA sh'' f'' (weaken w avar)) body)

        Use repr arrs           -> Use repr arrs
        Unit tp e               -> Unit tp (cvtE e)
        Acond p at ae           -> Acond (cvtE p) (cvtA at) (cvtA ae)
        Anil                    -> Anil
        Apair a1 a2             -> Apair (cvtA a1) (cvtA a2)
        Awhile p f a            -> Awhile (cvtAF p) (cvtAF f) (cvtA a)
        Apply repr f a          -> Apply repr (cvtAF f) (cvtA a)
        Aforeign repr ff f a    -> Aforeign repr ff f (cvtA a)       -- no sharing between f and a
        Generate repr sh f      -> Generate repr (cvtE sh) (cvtF f)
        Map tp f a              -> Map tp (cvtF f) (cvtA a)
        ZipWith tp f a b        -> ZipWith tp (cvtF f) (cvtA a) (cvtA b)
        Backpermute shr sh p a  -> Backpermute shr (cvtE sh) (cvtF p) (cvtA a)
        Transform repr sh p f a -> Transform repr (cvtE sh) (cvtF p) (cvtF f) (cvtA a)
        Slice slix a sl         -> Slice slix (cvtA a) (cvtE sl)
        Replicate slix sh a     -> Replicate slix (cvtE sh) (cvtA a)
        Reshape shr sl a        -> Reshape shr (cvtE sl) (cvtA a)
        Fold f z a              -> Fold (cvtF f) (cvtE z) (cvtA a)
        Fold1 f a               -> Fold1 (cvtF f) (cvtA a)
        FoldSeg i f z a s       -> FoldSeg i (cvtF f) (cvtE z) (cvtA a) (cvtA s)
        Fold1Seg i f a s        -> Fold1Seg i (cvtF f) (cvtA a) (cvtA s)
        Scanl f z a             -> Scanl (cvtF f) (cvtE z) (cvtA a)
        Scanl1 f a              -> Scanl1 (cvtF f) (cvtA a)
        Scanl' f z a            -> Scanl' (cvtF f) (cvtE z) (cvtA a)
        Scanr f z a             -> Scanr (cvtF f) (cvtE z) (cvtA a)
        Scanr1 f a              -> Scanr1 (cvtF f) (cvtA a)
        Scanr' f z a            -> Scanr' (cvtF f) (cvtE z) (cvtA a)
        Permute f d p a         -> Permute (cvtF f) (cvtA d) (cvtF p) (cvtA a)
        Stencil s t f x a       -> Stencil s t (cvtF f) (cvtB x) (cvtA a)
        Stencil2 s1 s2 t f x a y b
                                -> Stencil2 s1 s2 t (cvtF f) (cvtB x) (cvtA a) (cvtB y) (cvtA b)
        -- Collect seq             -> Collect (cvtSeq seq)

      where
        cvtA :: acc aenv s -> acc aenv s
        cvtA = kmap (replaceA sh' f' avar)

        cvtE :: Exp aenv s -> Exp aenv s
        cvtE = replaceE sh' f' avar

        cvtF :: Fun aenv s -> Fun aenv s
        cvtF = replaceF sh' f' avar

        cvtB :: Boundary aenv s -> Boundary aenv s
        cvtB Clamp        = Clamp
        cvtB Mirror       = Mirror
        cvtB Wrap         = Wrap
        cvtB (Constant c) = Constant c
        cvtB (Function f) = Function (cvtF f)

        cvtAF :: PreOpenAfun acc aenv s -> PreOpenAfun acc aenv s
        cvtAF = cvt sh' f' avar
          where
            cvt :: forall aenv a.
                   Exp aenv sh -> Fun aenv (sh -> e) -> ArrayVar aenv (Array sh e)
                -> PreOpenAfun acc aenv a
                -> PreOpenAfun acc aenv a
            cvt sh'' f'' avar' (Abody a) = Abody $ kmap (replaceA sh'' f'' avar') a
            cvt sh'' f'' avar' (Alam lhs (af :: PreOpenAfun acc aenv1 b)) =
              Alam lhs $ cvt (weaken w sh'')
                (weaken w f'')
                (weaken w avar')
                af
              where
                w :: aenv :> aenv1
                w = weakenWithLHS lhs

-- Do not fuse bindings of multiple variables
aletD' _ _ lhs (Embed env1 cc1) (Embed env0 cc0)
  = Stats.ruleFired "aletD/bind"
  $ Embed (PushEnv BaseEnv lhs acc1 `append` env0) cc0
  where
    acc1 = computeAcc $ Embed env1 cc1


{--
        cvtSeq :: PreOpenSeq acc aenv senv s -> PreOpenSeq acc aenv senv s
        cvtSeq s =
          case s of
            Producer p s' ->
              Producer
                (case p of
                   StreamIn arrs        -> StreamIn arrs
                   ToSeq slix sh a      -> ToSeq slix sh (cvtA a)
                   MapSeq f x           -> MapSeq (cvtAF f) x
                   ChunkedMapSeq f x    -> ChunkedMapSeq (cvtAF f) x
                   ZipWithSeq f x y     -> ZipWithSeq (cvtAF f) x y
                   ScanSeq f e x        -> ScanSeq (cvtF f) (cvtE e) x)
                (cvtSeq s')
            Consumer c ->
              Consumer (cvtC c)
            Reify ix -> Reify ix

        cvtC :: Consumer acc aenv senv s -> Consumer acc aenv senv s
        cvtC c =
          case c of
            FoldSeq f e x        -> FoldSeq (cvtF f) (cvtE e) x
            FoldSeqFlatten f a x -> FoldSeqFlatten (cvtAF f) (cvtA a) x
            Stuple t             -> Stuple (cvtCT t)

        cvtCT :: Atuple (Consumer acc aenv senv) t -> Atuple (Consumer acc aenv senv) t
        cvtCT NilAtup        = NilAtup
        cvtCT (SnocAtup t c) = cvtCT t `SnocAtup` cvtC c
--}


-- Array conditionals, in particular eliminate branches when the predicate
-- reduces to a known constant.
--
-- Note that we take the raw unprocessed terms as input. If instead we had the
-- terms for each branch in the delayed representation, this would require that
-- each term has been sunk into a common environment, which implies the
-- conditional has been pushed underneath the intersection of bound terms for
-- both branches. This would result in redundant work processing the bindings
-- for the branch not taken.
--
acondD :: Kit acc
       => EmbedAcc acc
       -> Exp          aenv Bool
       ->          acc aenv arrs
       ->          acc aenv arrs
       -> Embed    acc aenv arrs
acondD embedAcc p t e
  | Const _ True  <- p      = Stats.knownBranch "True"      $ embedAcc t
  | Const _ False <- p      = Stats.knownBranch "False"     $ embedAcc e
  | Just Refl <- match t e  = Stats.knownBranch "redundant" $ embedAcc e
  | otherwise               = done $ Acond p (computeAcc (embedAcc t))
                                             (computeAcc (embedAcc e))


-- Scalar expressions
-- ------------------

identity :: TupleType a -> OpenFun env aenv (a -> a)
identity tp
  | DeclareVars lhs _ value <- declareVars tp
  = Lam lhs $ Body $ evars $ value weakenId

toIndex :: ShapeR sh -> OpenExp env aenv sh -> OpenFun env aenv (sh -> Int)
toIndex shr sh
  | DeclareVars lhs k value <- declareVars $ shapeType shr
  = Lam lhs $ Body $ ToIndex shr (weakenE k sh) $ evars $ value weakenId

fromIndex :: ShapeR sh -> OpenExp env aenv sh -> OpenFun env aenv (Int -> sh)
fromIndex shr sh = Lam (LeftHandSideSingle scalarTypeInt) $ Body $ FromIndex shr (weakenE (weakenSucc' weakenId) sh) $ Evar $ Var scalarTypeInt ZeroIdx

reindex :: ShapeR sh'
        -> OpenExp env aenv sh'
        -> ShapeR sh
        -> OpenExp env aenv sh
        -> OpenFun env aenv (sh -> sh')
reindex shr' sh' shr sh
  | Just Refl <- match sh sh'   = identity (shapeType shr')
  | otherwise                   = fromIndex shr' sh' `compose` toIndex shr sh

extend :: SliceIndex slix sl co sh
       -> Exp aenv slix
       -> Fun aenv (sh -> sl)
extend sliceIndex slix
  | DeclareVars lhs k value <- declareVars $ shapeType $ sliceDomainR sliceIndex
  = Lam lhs $ Body $ IndexSlice sliceIndex (weakenE k slix) $ evars $ value weakenId

restrict :: SliceIndex slix sl co sh
         -> Exp aenv slix
         -> Fun aenv (sl -> sh)
restrict sliceIndex slix
  | DeclareVars lhs k value <- declareVars $ shapeType $ sliceShapeR sliceIndex
  = Lam lhs $ Body $ IndexFull sliceIndex (weakenE k slix) $ evars $ value weakenId

arrayShape :: ArrayVar aenv (Array sh e) -> Exp aenv sh
arrayShape = simplify . Shape

indexArray :: ArrayVar aenv (Array sh e) -> Fun aenv (sh -> e)
indexArray v@(Var (ArrayR shr _) _)
  | DeclareVars lhs _ value <- declareVars $ shapeType shr
  = Lam lhs $ Body $ Index v $ evars $ value weakenId

linearIndex :: ArrayVar aenv (Array sh e) -> Fun aenv (Int -> e)
linearIndex v = Lam (LeftHandSideSingle scalarTypeInt) $ Body $ LinearIndex v $ Evar $ Var scalarTypeInt ZeroIdx

