{-# LANGUAGE BangPatterns        #-}
{-# LANGUAGE EmptyCase           #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE MagicHash           #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing #-}
{-# OPTIONS_HADDOCK prune #-}
-- |
-- Module      : Data.Array.Accelerate.Interpreter.Simple
-- Description : Reference backend (interpreted)
-- Copyright   : [2008..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--
-- This interpreter is meant to be a reference implementation of the
-- semantics of the embedded array language. The emphasis is on defining
-- the semantics clearly, not on performance.
--

module Data.Array.Accelerate.Interpreter.Simple (

  Smart.Acc, Sugar.Arrays,
  Afunction, AfunctionR,

  -- * Interpret an array expression
  run, run1, runN,

  -- Internal (hidden)
  evalPrim, evalPrimConst, evalCoerceScalar, atraceOp,

) where

import Data.Array.Accelerate.Array.Buffer
import Data.Array.Accelerate.AST                                    hiding ( Boundary(..) )
import Data.Array.Accelerate.AST.Environment
import Data.Array.Accelerate.AST.Var
import Data.Array.Accelerate.Error
import Data.Array.Accelerate.Representation.Array
import Data.Array.Accelerate.Representation.Elt
import Data.Array.Accelerate.Representation.Shape
import Data.Array.Accelerate.Representation.Slice
import Data.Array.Accelerate.Representation.Stencil
import Data.Array.Accelerate.Representation.Tag
import Data.Array.Accelerate.Representation.Type
import Data.Array.Accelerate.Representation.Vec
import Data.Array.Accelerate.Trafo
import Data.Array.Accelerate.Trafo.Sharing                          ( AfunctionR, AfunctionRepr(..), afunctionRepr )
import qualified Data.Array.Accelerate.Trafo.Sharing as Sharing
import Data.Array.Accelerate.Type
import Data.Primitive.Vec
import qualified Data.Array.Accelerate.AST                          as AST
import qualified Data.Array.Accelerate.Debug.Internal.Flags         as Debug
-- import qualified Data.Array.Accelerate.Debug.Internal.Graph         as Debug
import qualified Data.Array.Accelerate.Debug.Internal.Stats         as Debug
import qualified Data.Array.Accelerate.Debug.Internal.Timed         as Debug
import qualified Data.Array.Accelerate.Smart                        as Smart
import qualified Data.Array.Accelerate.Sugar.Array                  as Sugar
import qualified Data.Array.Accelerate.Sugar.Elt                    as Sugar

-- import Control.DeepSeq                                              ( ($!!) )
import Control.Exception
import Control.Monad
import Control.Monad.ST
import Data.Bits
import Data.Primitive.ByteArray
import Data.Primitive.Types
import Data.Text.Lazy.Builder
import Formatting
import System.IO
import System.IO.Unsafe                                             ( unsafePerformIO )
import Unsafe.Coerce
import qualified Data.Text.IO                                       as T
import Prelude                                                      hiding ( (!!), sum )


-- Program execution
-- -----------------

-- | Run a complete embedded array program using the reference interpreter.
--
run :: (HasCallStack, Sugar.Arrays a) => Smart.Acc a -> a
run a = unsafePerformIO execute
  where
    !acc    = Sharing.convertAcc a
    execute = do
      -- Debug.dumpGraph $!! acc
      Debug.dumpSimplStats
      res <- phase "execute" Debug.elapsed $ evaluate $ evalOpenAcc acc Empty
      return $ Sugar.toArr $ snd res

-- | This is 'runN' specialised to an array program of one argument.
--
run1 :: (HasCallStack, Sugar.Arrays a, Sugar.Arrays b) => (Smart.Acc a -> Smart.Acc b) -> a -> b
run1 = runN

-- | Prepare and execute an embedded array program.
--
runN :: forall f. (HasCallStack, Afunction f) => f -> AfunctionR f
runN f = go
  where
    !acc    = Sharing.convertAfun f
    !afun   = unsafePerformIO $ do
                -- Debug.dumpGraph $!! acc
                Debug.dumpSimplStats
                return acc
    !go     = eval (afunctionRepr @f) afun Empty
    --
    eval :: forall g aenv. AfunctionRepr g (AfunctionR g) (ArraysFunctionR g)
         -> OpenAfun aenv (ArraysFunctionR g)
         -> Val aenv
         -> AfunctionR g
    eval (AfunctionReprLam reprF) (Alam lhs f) aenv = \a -> eval reprF f $ aenv `push` (lhs, Sugar.fromArr a)
    eval AfunctionReprBody        (Abody b)    aenv = unsafePerformIO $ phase "execute" Debug.elapsed (Sugar.toArr . snd <$> evaluate (evalOpenAcc b aenv))
    eval AfunctionReprLam{}       (Abody b)    _    = arraysRFunctionImpossible (arraysR b)
    eval AfunctionReprBody        Alam{}       _    = arraysRFunctionImpossible (Sugar.arraysR @(AfunctionR g))


-- Debugging
-- ---------

phase :: Builder -> Format Builder (Double -> Double -> Builder) -> IO a -> IO a
phase n fmt go = Debug.timed Debug.dump_phases (now ("phase " <> n <> ": ") % fmt) go


-- Delayed Arrays
-- --------------

-- Note that in contrast to the representation used in the optimised AST, the
-- delayed array representation used here is _only_ for delayed arrays --- we do
-- not require an optional Manifest|Delayed data type to evaluate the program.
--
data Delayed a where
  Delayed :: ArrayR (Array sh e)
          -> sh
          -> (sh -> e)
          -> (Int -> e)
          -> Delayed (Array sh e)


-- Array expression evaluation
-- ---------------------------

type WithReprs acc = (ArraysR acc, acc)

fromFunction' :: ArrayR (Array sh e) -> sh -> (sh -> e) -> WithReprs (Array sh e)
fromFunction' repr sh f = (TupRsingle repr, fromFunction repr sh f)

-- Evaluate an open array function
--
evalOpenAfun :: HasCallStack => OpenAfun aenv f -> Val aenv -> f
evalOpenAfun (Alam lhs f) aenv = \a -> evalOpenAfun f $ aenv `push` (lhs, a)
evalOpenAfun (Abody b)    aenv = snd $ evalOpenAcc b aenv


-- The core interpreter for optimised array programs
--
evalOpenAcc
    :: forall aenv a. HasCallStack
    => OpenAcc aenv a
    -> Val aenv
    -> WithReprs a
evalOpenAcc (OpenAcc pacc) aenv =
  let
      manifest :: forall a'. HasCallStack => OpenAcc aenv a' -> WithReprs a'
      manifest acc =
        let (repr, a') = evalOpenAcc acc aenv
        in  rnfArraysR repr a' `seq` (repr, a')

      delayed :: OpenAcc aenv (Array sh e) -> Delayed (Array sh e)
      delayed a' = Delayed aR (shape a) (indexArray aR a) (linearIndexArray (arrayRtype aR) a)
        where
          (TupRsingle aR, a) = manifest a'

      evalE :: Exp aenv t -> t
      evalE exp = evalExp exp aenv

      evalF :: Fun aenv f -> f
      evalF fun = evalFun fun aenv

      evalB :: AST.Boundary aenv t -> Boundary t
      evalB bnd = evalBoundary bnd aenv

      dir :: Direction -> t -> t -> t
      dir LeftToRight l _ = l
      dir RightToLeft _ r = r
  in
  case pacc of
    Alet lhs acc1 acc2            -> evalOpenAcc acc2 $ aenv `push` (lhs, snd $ manifest acc1)
    Avar (Var repr ix)            -> (TupRsingle repr, prj ix aenv)
    Apair acc1 acc2               -> let (r1, a1) = manifest acc1
                                         (r2, a2) = manifest acc2
                                     in
                                     (TupRpair r1 r2, (a1, a2))
    Anil                          -> (TupRunit, ())
    Apply repr afun acc           -> (repr, evalOpenAfun afun aenv $ snd $ manifest acc)
    Aforeign repr _ afun acc      -> (repr, evalOpenAfun afun Empty $ snd $ manifest acc)
    Acond p acc1 acc2
      | toBool (evalE p)          -> manifest acc1
      | otherwise                 -> manifest acc2

    Awhile cond body acc          -> (repr, go initial)
      where
        (repr, initial) = manifest acc
        p               = evalOpenAfun cond aenv
        f               = evalOpenAfun body aenv
        go !x
          | toBool (linearIndexArray (Sugar.eltR @Word8) (p x) 0) = go (f x)
          | otherwise                                             = x

    Atrace msg as bs              -> unsafePerformIO $ manifest bs <$ atraceOp msg (snd $ manifest as)

    Use repr arr                  -> (TupRsingle repr, arr)
    Unit tp e                     -> unitOp tp (evalE e)

    -- Producers
    -- ---------
    Reshape shr sh acc            -> reshapeOp shr (evalE sh) (manifest acc)
    Generate repr sh f            -> generateOp repr (evalE sh) (evalF f)
    Transform repr sh p f acc     -> transformOp repr (evalE sh) (evalF p) (evalF f) (delayed acc)
    Replicate slice slix acc      -> replicateOp slice (evalE slix) (manifest acc)
    Slice slice acc slix          -> sliceOp slice (manifest acc) (evalE slix)
    Map tp f acc                  -> mapOp tp (evalF f) (delayed acc)
    ZipWith tp f acc1 acc2        -> zipWithOp tp (evalF f) (delayed acc1) (delayed acc2)
    Backpermute shr sh p acc      -> backpermuteOp shr (evalE sh) (evalF p) (delayed acc)

    -- Consumers
    -- ---------
    Fold f (Just z) acc           -> foldOp (evalF f) (evalE z) (delayed acc)
    Fold f Nothing  acc           -> fold1Op (evalF f) (delayed acc)
    FoldSeg i f (Just z) acc seg  -> foldSegOp i (evalF f) (evalE z) (delayed acc) (delayed seg)
    FoldSeg i f Nothing acc seg   -> fold1SegOp i (evalF f) (delayed acc) (delayed seg)
    Scan  d f (Just z) acc        -> dir d scanlOp  scanrOp  (evalF f) (evalE z) (delayed acc)
    Scan  d f Nothing  acc        -> dir d scanl1Op scanr1Op (evalF f)           (delayed acc)
    Scan' d f z acc               -> dir d scanl'Op scanr'Op (evalF f) (evalE z) (delayed acc)
    Permute f def acc             -> permuteOp (evalF <$> f) (manifest def) (delayed acc)
    Stencil s tp sten b acc       -> stencilOp s tp (evalF sten) (evalB b) (delayed acc)
    Stencil2 s1 s2 tp sten b1 a1 b2 a2
                                  -> stencil2Op s1 s2 tp (evalF sten) (evalB b1) (delayed a1) (evalB b2) (delayed a2)


-- Array primitives
-- ----------------

unitOp :: TypeR e -> e -> WithReprs (Scalar e)
unitOp tp e = fromFunction' (ArrayR ShapeRz tp) () (const e)


generateOp
    :: ArrayR (Array sh e)
    -> sh
    -> (sh -> e)
    -> WithReprs (Array sh e)
generateOp = fromFunction'


transformOp
    :: ArrayR (Array sh' b)
    -> sh'
    -> (sh' -> sh)
    -> (a -> b)
    -> Delayed (Array sh a)
    -> WithReprs (Array sh' b)
transformOp repr sh' p f (Delayed _ _ xs _)
  = fromFunction' repr sh' (\ix -> f (xs $ p ix))


reshapeOp
    :: HasCallStack
    => ShapeR sh
    -> sh
    -> WithReprs (Array sh' e)
    -> WithReprs (Array sh  e)
reshapeOp newShapeR newShape (TupRsingle (ArrayR shr tp), (Array sh adata))
  = boundsCheck "shape mismatch" (size newShapeR newShape == size shr sh)
    ( TupRsingle (ArrayR newShapeR tp)
    , Array newShape adata
    )


replicateOp
    :: SliceIndex slix sl co sh
    -> slix
    -> WithReprs (Array sl e)
    -> WithReprs (Array sh e)
replicateOp slice slix (TupRsingle repr@(ArrayR _ tp), arr)
  = fromFunction' repr' sh (\ix -> (repr, arr) ! pf ix)
  where
    repr' = ArrayR (sliceDomainR slice) tp
    (sh, pf) = extend slice slix (shape arr)

    extend :: SliceIndex slix sl co dim
           -> slix
           -> sl
           -> (dim, dim -> sl)
    extend SliceNil              ()        ()
      = ((), const ())
    extend (SliceAll sliceIdx)   (slx, ()) (sl, sz)
      = let (dim', f') = extend sliceIdx slx sl
        in  ((dim', sz), \(ix, i) -> (f' ix, i))
    extend (SliceFixed sliceIdx) (slx, sz) sl
      = let (dim', f') = extend sliceIdx slx sl
        in  ((dim', sz), \(ix, _) -> f' ix)


sliceOp
    :: SliceIndex slix sl co sh
    -> WithReprs (Array sh e)
    -> slix
    -> WithReprs (Array sl e)
sliceOp slice (TupRsingle repr@(ArrayR _ tp), arr) slix
  = fromFunction' repr' sh' (\ix -> (repr, arr) ! pf ix)
  where
    repr' = ArrayR (sliceShapeR slice) tp
    (sh', pf) = restrict slice slix (shape arr)

    restrict
        :: HasCallStack
        => SliceIndex slix sl co sh
        -> slix
        -> sh
        -> (sl, sl -> sh)
    restrict SliceNil              ()        ()
      = ((), const ())
    restrict (SliceAll sliceIdx)   (slx, ()) (sl, sz)
      = let (sl', f') = restrict sliceIdx slx sl
        in  ((sl', sz), \(ix, i) -> (f' ix, i))
    restrict (SliceFixed sliceIdx) (slx, i)  (sl, sz)
      = let (sl', f') = restrict sliceIdx slx sl
        in  indexCheck i sz $ (sl', \ix -> (f' ix, i))


mapOp :: TypeR b
      -> (a -> b)
      -> Delayed   (Array sh a)
      -> WithReprs (Array sh b)
mapOp tp f (Delayed (ArrayR shr _) sh xs _)
  = fromFunction' (ArrayR shr tp) sh (\ix -> f (xs ix))


zipWithOp
    :: TypeR c
    -> (a -> b -> c)
    -> Delayed   (Array sh a)
    -> Delayed   (Array sh b)
    -> WithReprs (Array sh c)
zipWithOp tp f (Delayed (ArrayR shr _) shx xs _) (Delayed _ shy ys _)
  = fromFunction' (ArrayR shr tp) (intersect shr shx shy) (\ix -> f (xs ix) (ys ix))


foldOp
    :: (e -> e -> e)
    -> e
    -> Delayed (Array (sh, Int) e)
    -> WithReprs (Array sh e)
foldOp f z (Delayed (ArrayR (ShapeRsnoc shr) tp) (sh, n) arr _)
  = fromFunction' (ArrayR shr tp) sh (\ix -> iter (ShapeRsnoc ShapeRz) ((), n) (\((), i) -> arr (ix, i)) f z)


fold1Op
    :: HasCallStack
    => (e -> e -> e)
    -> Delayed (Array (sh, Int) e)
    -> WithReprs (Array sh e)
fold1Op f (Delayed (ArrayR (ShapeRsnoc shr) tp) (sh, n) arr _)
  = boundsCheck "empty array" (n > 0)
  $ fromFunction' (ArrayR shr tp) sh (\ix -> iter1 (ShapeRsnoc ShapeRz) ((), n) (\((), i) -> arr (ix, i)) f)


foldSegOp
    :: HasCallStack
    => IntegralType i
    -> (e -> e -> e)
    -> e
    -> Delayed (Array (sh, Int) e)
    -> Delayed (Segments i)
    -> WithReprs (Array (sh, Int) e)
foldSegOp itp f z (Delayed repr (sh, _) arr _) (Delayed _ ((), n) _ seg)
  | IntegralDict <- integralDict itp
  = boundsCheck "empty segment descriptor" (n > 0)
  $ fromFunction' repr (sh, n-1)
  $ \(sz, ix) -> let start = fromIntegral $ seg ix
                     end   = fromIntegral $ seg (ix+1)
                 in
                 boundsCheck "empty segment" (end >= start)
                 $ iter (ShapeRsnoc ShapeRz) ((), end-start) (\((), i) -> arr (sz, start+i)) f z


fold1SegOp
    :: HasCallStack
    => IntegralType i
    -> (e -> e -> e)
    -> Delayed (Array (sh, Int) e)
    -> Delayed (Segments i)
    -> WithReprs (Array (sh, Int) e)
fold1SegOp itp f (Delayed repr (sh, _) arr _) (Delayed _ ((), n) _ seg)
  | IntegralDict <- integralDict itp
  = boundsCheck "empty segment descriptor" (n > 0)
  $ fromFunction' repr (sh, n-1)
  $ \(sz, ix)   -> let start = fromIntegral $ seg ix
                       end   = fromIntegral $ seg (ix+1)
                   in
                   boundsCheck "empty segment" (end > start)
                   $ iter1 (ShapeRsnoc ShapeRz) ((), end-start) (\((), i) -> arr (sz, start+i)) f


scanl1Op
    :: forall sh e. HasCallStack
    => (e -> e -> e)
    -> Delayed (Array (sh, Int) e)
    -> WithReprs (Array (sh, Int) e)
scanl1Op f (Delayed (ArrayR shr tp) sh ain _)
  = ( TupRsingle $ ArrayR shr tp
    , adata `seq` Array sh adata
    )
  where
    --
    (adata, _)  = runBuffers tp $ do
      aout <- newBuffers tp (size shr sh)

      let write (sz, 0) = writeBuffers tp aout (toIndex shr sh (sz, 0)) (ain (sz, 0))
          write (sz, i) = do
            x <- readBuffers tp aout (toIndex shr sh (sz, i-1))
            let y = ain (sz, i)
            writeBuffers tp aout (toIndex shr sh (sz, i)) (f x y)

      iter shr sh write (>>) (return ())
      return (aout, undefined)


scanlOp
    :: forall sh e. HasCallStack
    => (e -> e -> e)
    -> e
    -> Delayed (Array (sh, Int) e)
    -> WithReprs (Array (sh, Int) e)
scanlOp f z (Delayed (ArrayR shr tp) (sh, n) ain _)
  = ( TupRsingle $ ArrayR shr tp
    , adata `seq` Array sh' adata
    )
  where
    sh'         = (sh, n+1)
    --
    (adata, _)  = runBuffers tp $ do
      aout <- newBuffers tp (size shr sh')

      let write (sz, 0) = writeBuffers tp aout (toIndex shr sh' (sz, 0)) z
          write (sz, i) = do
            x <- readBuffers tp aout (toIndex shr sh' (sz, i-1))
            let y = ain (sz, i-1)
            writeBuffers tp aout (toIndex shr sh' (sz, i)) (f x y)

      iter shr sh' write (>>) (return ())
      return (aout, undefined)


scanl'Op
    :: forall sh e. HasCallStack
    => (e -> e -> e)
    -> e
    -> Delayed (Array (sh, Int) e)
    -> WithReprs (Array (sh, Int) e, Array sh e)
scanl'Op f z (Delayed (ArrayR shr@(ShapeRsnoc shr') tp) (sh, n) ain _)
  = ( TupRsingle (ArrayR shr tp) `TupRpair` TupRsingle (ArrayR shr' tp)
    , aout `seq` asum `seq` ( Array (sh, n) aout, Array sh asum )
    )
  where
    ((aout, asum), _) = runBuffers (TupRpair tp tp) $ do
      aout <- newBuffers tp (size shr  (sh, n))
      asum <- newBuffers tp (size shr' sh)

      let write (sz, 0)
            | n == 0    = writeBuffers tp asum (toIndex shr' sh sz) z
            | otherwise = writeBuffers tp aout (toIndex shr  (sh, n) (sz, 0)) z
          write (sz, i) = do
            x <- readBuffers tp aout (toIndex shr (sh, n) (sz, i-1))
            let y = ain (sz, i-1)
            if i == n
              then writeBuffers tp asum (toIndex shr' sh      sz)      (f x y)
              else writeBuffers tp aout (toIndex shr  (sh, n) (sz, i)) (f x y)

      iter shr (sh, n+1) write (>>) (return ())
      return ((aout, asum), undefined)


scanrOp
    :: forall sh e. HasCallStack
    => (e -> e -> e)
    -> e
    -> Delayed (Array (sh, Int) e)
    -> WithReprs (Array (sh, Int) e)
scanrOp f z (Delayed (ArrayR shr tp) (sz, n) ain _)
  = ( TupRsingle (ArrayR shr tp)
    , adata `seq` Array sh' adata
    )
  where
    sh'         = (sz, n+1)
    --
    (adata, _)  = runBuffers tp $ do
      aout <- newBuffers tp (size shr sh')

      let write (sz, 0) = writeBuffers tp aout (toIndex shr sh' (sz, n)) z
          write (sz, i) = do
            let x = ain (sz, n-i)
            y <- readBuffers tp aout (toIndex shr sh' (sz, n-i+1))
            writeBuffers tp aout (toIndex shr sh' (sz, n-i)) (f x y)

      iter shr sh' write (>>) (return ())
      return (aout, undefined)


scanr1Op
    :: forall sh e. HasCallStack
    => (e -> e -> e)
    -> Delayed (Array (sh, Int) e)
    -> WithReprs (Array (sh, Int) e)
scanr1Op f (Delayed (ArrayR shr tp) sh@(_, n) ain _)
  = ( TupRsingle $ ArrayR shr tp
    , adata `seq` Array sh adata
    )
  where
    (adata, _)  = runBuffers tp $ do
      aout <- newBuffers tp (size shr sh)

      let write (sz, 0) = writeBuffers tp aout (toIndex shr sh (sz, n-1)) (ain (sz, n-1))
          write (sz, i) = do
            let x = ain (sz, n-i-1)
            y <- readBuffers tp aout (toIndex shr sh (sz, n-i))
            writeBuffers tp aout (toIndex shr sh (sz, n-i-1)) (f x y)

      iter shr sh write (>>) (return ())
      return (aout, undefined)


scanr'Op
    :: forall sh e. HasCallStack
    => (e -> e -> e)
    -> e
    -> Delayed (Array (sh, Int) e)
    -> WithReprs (Array (sh, Int) e, Array sh e)
scanr'Op f z (Delayed (ArrayR shr@(ShapeRsnoc shr') tp) (sh, n) ain _)
  = ( TupRsingle (ArrayR shr tp) `TupRpair` TupRsingle (ArrayR shr' tp)
    , aout `seq` asum `seq` ( Array (sh, n) aout, Array sh asum )
    )
  where
    ((aout, asum), _) = runBuffers (TupRpair tp tp) $ do
      aout <- newBuffers tp (size shr  (sh, n))
      asum <- newBuffers tp (size shr' sh)

      let write (sz, 0)
            | n == 0    = writeBuffers tp asum (toIndex shr' sh sz) z
            | otherwise = writeBuffers tp aout (toIndex shr  (sh, n) (sz, n-1)) z

          write (sz, i) = do
            let x = ain (sz, n-i)
            y <- readBuffers tp aout (toIndex shr (sh, n) (sz, n-i))
            if i == n
              then writeBuffers tp asum (toIndex shr' sh      sz)          (f x y)
              else writeBuffers tp aout (toIndex shr  (sh, n) (sz, n-i-1)) (f x y)

      iter shr (sh, n+1) write (>>) (return ())
      return ((aout, asum), undefined)


permuteOp
    :: forall sh sh' e. HasCallStack
    => Maybe (e -> e -> e)
    -> WithReprs (Array sh' e)
    -> Delayed   (Array sh  (PrimMaybe (((), sh'), e)))
    -> WithReprs (Array sh' e)
permuteOp mf (TupRsingle (ArrayR shr' _), def) (Delayed (ArrayR shr tp') sh ain _)
  = (TupRsingle $ ArrayR shr' tp, adata `seq` Array sh' adata)
  where
    tp = case tp' of
           TupRpair _ (TupRpair _ (TupRpair _ t)) -> t
           _ -> error "unreachable"
    --
    sh'         = shape def
    n'          = size shr' sh'
    --
    (adata, _)  = runBuffers tp $ do
      aout <- newBuffers tp n'

      let -- initialise array with default values
          init i
            | i >= n'   = return ()
            | otherwise = do
                writeBuffers tp aout i ((tp, def) !! i)
                init (i+1)

          -- project each element onto the destination array
          updateScatter src
            = case ain src of
                (0,_)                 -> return ()
                (1,((),(((),dst),x))) -> do
                  let j = toIndex shr' sh' dst
                  writeBuffers tp aout j x
                _                     -> internalError "unexpected tag"

          -- project, but combine with the function f
          updateWith f src
            = case ain src of
                (0,_)                 -> return ()
                (1,((),(((),dst),x))) -> do
                  let j = toIndex shr' sh' dst
                  y <- readBuffers tp aout j
                  writeBuffers tp aout j (f x y)
                _                     -> internalError "unexpected tag"

      init 0
      iter shr sh (maybe updateScatter updateWith mf) (>>) (return ())
      return (aout, undefined)


backpermuteOp
    :: ShapeR sh'
    -> sh'
    -> (sh' -> sh)
    -> Delayed (Array sh e)
    -> WithReprs (Array sh' e)
backpermuteOp shr sh' p (Delayed (ArrayR _ tp) _ arr _)
  = fromFunction' (ArrayR shr tp) sh' (\ix -> arr $ p ix)


stencilOp
    :: HasCallStack
    => StencilR sh a stencil
    -> TypeR b
    -> (stencil -> b)
    -> Boundary (Array sh a)
    -> Delayed  (Array sh a)
    -> WithReprs (Array sh b)
stencilOp stencil tp f bnd arr@(Delayed _ sh _ _)
  = fromFunction' (ArrayR shr tp) sh
  $ f . stencilAccess stencil (bounded shr bnd arr)
  where
    shr = stencilShapeR stencil


stencil2Op
    :: HasCallStack
    => StencilR sh a stencil1
    -> StencilR sh b stencil2
    -> TypeR c
    -> (stencil1 -> stencil2 -> c)
    -> Boundary (Array sh a)
    -> Delayed  (Array sh a)
    -> Boundary (Array sh b)
    -> Delayed  (Array sh b)
    -> WithReprs (Array sh c)
stencil2Op s1 s2 tp stencil bnd1 arr1@(Delayed _ sh1 _ _) bnd2 arr2@(Delayed _ sh2 _ _)
  = fromFunction' (ArrayR shr tp) (intersect shr sh1 sh2) f
  where
    f ix  = stencil (stencilAccess s1 (bounded shr bnd1 arr1) ix)
                    (stencilAccess s2 (bounded shr bnd2 arr2) ix)
    shr = stencilShapeR s1

stencilAccess
    :: StencilR sh e stencil
    -> (sh -> e)
    -> sh
    -> stencil
stencilAccess stencil = goR (stencilShapeR stencil) stencil
  where
    -- Base cases, nothing interesting to do here since we know the lower
    -- dimension is Z.
    --
    goR :: ShapeR sh -> StencilR sh e stencil -> (sh -> e) -> sh -> stencil
    goR _ (StencilRunit3 _) rf ix =
      let
          (z, i) = ix
          rf' d  = rf (z, i+d)
      in
      ((( ()
      , rf' (-1))
      , rf'   0 )
      , rf'   1 )

    goR _ (StencilRunit5 _) rf ix =
      let (z, i) = ix
          rf' d  = rf (z, i+d)
      in
      ((((( ()
      , rf' (-2))
      , rf' (-1))
      , rf'   0 )
      , rf'   1 )
      , rf'   2 )

    goR _ (StencilRunit7 _) rf ix =
      let (z, i) = ix
          rf' d  = rf (z, i+d)
      in
      ((((((( ()
      , rf' (-3))
      , rf' (-2))
      , rf' (-1))
      , rf'   0 )
      , rf'   1 )
      , rf'   2 )
      , rf'   3 )

    goR _ (StencilRunit9 _) rf ix =
      let (z, i) = ix
          rf' d  = rf (z, i+d)
      in
      ((((((((( ()
      , rf' (-4))
      , rf' (-3))
      , rf' (-2))
      , rf' (-1))
      , rf'   0 )
      , rf'   1 )
      , rf'   2 )
      , rf'   3 )
      , rf'   4 )

    -- Recursive cases. Note that because the stencil pattern is defined with
    -- cons ordering, whereas shapes (and indices) are defined as a snoc-list,
    -- when we recurse on the stencil structure we must manipulate the
    -- _left-most_ index component.
    --
    goR (ShapeRsnoc shr) (StencilRtup3 s1 s2 s3) rf ix =
      let (i, ix') = uncons shr ix
          rf' d ds = rf (cons shr (i+d) ds)
      in
      ((( ()
      , goR shr s1 (rf' (-1)) ix')
      , goR shr s2 (rf'   0)  ix')
      , goR shr s3 (rf'   1)  ix')

    goR (ShapeRsnoc shr) (StencilRtup5 s1 s2 s3 s4 s5) rf ix =
      let (i, ix') = uncons shr ix
          rf' d ds = rf (cons shr (i+d) ds)
      in
      ((((( ()
      , goR shr s1 (rf' (-2)) ix')
      , goR shr s2 (rf' (-1)) ix')
      , goR shr s3 (rf'   0)  ix')
      , goR shr s4 (rf'   1)  ix')
      , goR shr s5 (rf'   2)  ix')

    goR (ShapeRsnoc shr) (StencilRtup7 s1 s2 s3 s4 s5 s6 s7) rf ix =
      let (i, ix') = uncons shr ix
          rf' d ds = rf (cons shr (i+d) ds)
      in
      ((((((( ()
      , goR shr s1 (rf' (-3)) ix')
      , goR shr s2 (rf' (-2)) ix')
      , goR shr s3 (rf' (-1)) ix')
      , goR shr s4 (rf'   0)  ix')
      , goR shr s5 (rf'   1)  ix')
      , goR shr s6 (rf'   2)  ix')
      , goR shr s7 (rf'   3)  ix')

    goR (ShapeRsnoc shr) (StencilRtup9 s1 s2 s3 s4 s5 s6 s7 s8 s9) rf ix =
      let (i, ix') = uncons shr ix
          rf' d ds = rf (cons shr (i+d) ds)
      in
      ((((((((( ()
      , goR shr s1 (rf' (-4)) ix')
      , goR shr s2 (rf' (-3)) ix')
      , goR shr s3 (rf' (-2)) ix')
      , goR shr s4 (rf' (-1)) ix')
      , goR shr s5 (rf'   0)  ix')
      , goR shr s6 (rf'   1)  ix')
      , goR shr s7 (rf'   2)  ix')
      , goR shr s8 (rf'   3)  ix')
      , goR shr s9 (rf'   4)  ix')

    -- Add a left-most component to an index
    --
    cons :: ShapeR sh -> Int -> sh -> (sh, Int)
    cons ShapeRz          ix ()       = ((), ix)
    cons (ShapeRsnoc shr) ix (sh, sz) = (cons shr ix sh, sz)

    -- Remove the left-most index of an index, and return the remainder
    --
    uncons :: ShapeR sh -> (sh, Int) -> (Int, sh)
    uncons ShapeRz          ((), v)  = (v, ())
    uncons (ShapeRsnoc shr) (v1, v2) = let (i, v1') = uncons shr v1
                                       in  (i, (v1', v2))


bounded
    :: HasCallStack
    => ShapeR sh
    -> Boundary (Array sh e)
    -> Delayed (Array sh e)
    -> sh
    -> e
bounded shr bnd (Delayed _ sh f _) ix =
  if inside shr sh ix
    then f ix
    else
      case bnd of
        Function g -> g ix
        Constant v -> v
        _          -> f (bound shr sh ix)

  where
    -- Whether the index (second argument) is inside the bounds of the given
    -- shape (first argument).
    --
    inside :: ShapeR sh -> sh -> sh -> Bool
    inside ShapeRz          ()       ()       = True
    inside (ShapeRsnoc shr) (sh, sz) (ih, iz) = iz >= 0 && iz < sz && inside shr sh ih

    -- Return the index (second argument), updated to obey the given boundary
    -- conditions when outside the bounds of the given shape (first argument)
    --
    bound :: HasCallStack => ShapeR sh -> sh -> sh -> sh
    bound ShapeRz () () = ()
    bound (ShapeRsnoc shr) (sh, sz) (ih, iz) = (bound shr sh ih, ih')
      where
        ih'
          | iz < 0 = case bnd of
                          Clamp  -> 0
                          Mirror -> -iz
                          Wrap   -> sz + iz
                          _      -> internalError "unexpected boundary condition"
          | iz >= sz  = case bnd of
                          Clamp  -> sz - 1
                          Mirror -> sz - (iz - sz + 2)
                          Wrap   -> iz - sz
                          _      -> internalError "unexpected boundary condition"
          | otherwise = iz


-- Stencil boundary conditions
-- ---------------------------

data Boundary t where
  Clamp    :: Boundary t
  Mirror   :: Boundary t
  Wrap     :: Boundary t
  Constant :: t -> Boundary (Array sh t)
  Function :: (sh -> e) -> Boundary (Array sh e)


evalBoundary :: HasCallStack => AST.Boundary aenv t -> Val aenv -> Boundary t
evalBoundary bnd aenv =
  case bnd of
    AST.Clamp      -> Clamp
    AST.Mirror     -> Mirror
    AST.Wrap       -> Wrap
    AST.Constant v -> Constant v
    AST.Function f -> Function (evalFun f aenv)

atraceOp :: Message as -> as -> IO ()
atraceOp (Message f _ msg) as =
  let str = f as
   in do
     if null str
        then T.hPutStrLn stderr msg
        else hprint stderr (stext % ": " % string % "\n") msg str
     hFlush stderr


-- Scalar expression evaluation
-- ----------------------------

-- Evaluate a closed scalar expression
--
evalExp :: HasCallStack => Exp aenv t -> Val aenv -> t
evalExp e aenv = evalOpenExp e (runArrayInstr aenv) Empty

-- Evaluate a closed scalar function
--
evalFun :: HasCallStack => Fun aenv t -> Val aenv -> t
evalFun f aenv = evalOpenFun f (runArrayInstr aenv) Empty

-- Evaluate an open scalar function
--
evalOpenFun :: HasCallStack => PreOpenFun arr env t -> (forall a b. arr (a -> b) -> a -> b) -> Val env -> t
evalOpenFun (Body e)    runarr env = evalOpenExp e runarr env
evalOpenFun (Lam lhs f) runarr env =
  \x -> evalOpenFun f runarr (env `push` (lhs, x))


-- Evaluate an open scalar expression
--
-- NB: The implementation of 'Index' and 'Shape' demonstrate clearly why
--     array expressions must be hoisted out of scalar expressions before code
--     execution. If these operations are in the body of a function that gets
--     mapped over an array, the array argument would be evaluated many times
--     leading to a large amount of wasteful recomputation.
--
evalOpenExp
    :: forall env arr t. HasCallStack
    => PreOpenExp arr env t
    -> (forall a b. arr (a -> b) -> a -> b)
    -> Val env
    -> t
evalOpenExp pexp runarr env =
  let
      evalE :: PreOpenExp arr env t' -> t'
      evalE e = evalOpenExp e runarr env

      evalF :: PreOpenFun arr env f' -> f'
      evalF f = evalOpenFun f runarr env
  in
  case pexp of
    Let lhs exp1 exp2           -> let !v1  = evalE exp1
                                       env' = env `push` (lhs, v1)
                                   in  evalOpenExp exp2 runarr env'
    Evar (Var _ ix)             -> prj ix env
    Const _ c                   -> c
    Undef tp                    -> undefElt (TupRsingle tp)
    PrimConst c                 -> evalPrimConst c
    PrimApp f x                 -> evalPrim f (evalE x)
    Nil                         -> ()
    Pair e1 e2                  -> let !x1 = evalE e1
                                       !x2 = evalE e2
                                   in  (x1, x2)
    VecPack   vecR e            -> pack   vecR $! evalE e
    VecUnpack vecR e            -> unpack vecR $! evalE e
    IndexSlice slice slix sh    -> restrict slice (evalE slix)
                                                  (evalE sh)
      where
        restrict :: SliceIndex slix sl co sh -> slix -> sh -> sl
        restrict SliceNil              ()        ()         = ()
        restrict (SliceAll sliceIdx)   (slx, ()) (sl, sz)   =
          let sl' = restrict sliceIdx slx sl
          in  (sl', sz)
        restrict (SliceFixed sliceIdx) (slx, _i)  (sl, _sz) =
          restrict sliceIdx slx sl

    IndexFull slice slix sh     -> extend slice (evalE slix)
                                                (evalE sh)
      where
        extend :: SliceIndex slix sl co sh -> slix -> sl -> sh
        extend SliceNil              ()        ()       = ()
        extend (SliceAll sliceIdx)   (slx, ()) (sl, sz) =
          let sh' = extend sliceIdx slx sl
          in  (sh', sz)
        extend (SliceFixed sliceIdx) (slx, sz) sl       =
          let sh' = extend sliceIdx slx sl
          in  (sh', sz)

    ToIndex shr sh ix           -> toIndex shr (evalE sh) (evalE ix)
    FromIndex shr sh ix         -> fromIndex shr (evalE sh) (evalE ix)
    Case e rhs def              -> evalE (caseof (evalE e) rhs)
      where
        caseof :: TAG -> [(TAG, PreOpenExp arr env t)] -> PreOpenExp arr env t
        caseof tag = go
          where
            go ((t,c):cs)
              | tag == t  = c
              | otherwise = go cs
            go []
              | Just d <- def = d
              | otherwise     = internalError "unmatched case"

    Cond c t e
      | toBool (evalE c)        -> evalE t
      | otherwise               -> evalE e

    While cond body seed        -> go (evalE seed)
      where
        f       = evalF body
        p       = evalF cond
        go !x
          | toBool (p x) = go (f x)
          | otherwise    = x

    ArrayInstr instr arg        -> runarr instr (evalE arg)

    ShapeSize shr sh            -> size shr (evalE sh)
    Foreign _ _ f e             -> evalOpenFun f (\case {}) Empty $ evalE e
    Coerce t1 t2 e              -> evalCoerceScalar t1 t2 (evalE e)

runArrayInstr :: forall aenv a b. HasCallStack => Val aenv -> ArrayInstr aenv (a -> b) -> a -> b
runArrayInstr aenv instr arg =
  case instr of
    Shape acc               -> shape $ snd $ evalA acc
    Index acc               -> let (TupRsingle repr, a) = evalA acc
                               in (repr, a) ! arg
    LinearIndex acc         -> let (TupRsingle repr, a) = evalA acc
                                   ix   = fromIndex (arrayRshape repr) (shape a) arg
                               in (repr, a) ! ix
  where
    evalA :: ArrayVar aenv t -> WithReprs t
    evalA (Var repr ix) = (TupRsingle repr, prj ix aenv)

-- Coercions
-- ---------

-- Coercion between two scalar types. We require that the size of the source and
-- destination values are equal (this is not checked at this point).
--
evalCoerceScalar :: ScalarType a -> ScalarType b -> a -> b
evalCoerceScalar SingleScalarType{}    SingleScalarType{} a = unsafeCoerce a
evalCoerceScalar VectorScalarType{}    VectorScalarType{} a = unsafeCoerce a  -- XXX: or just unpack/repack the (Vec ba#)
evalCoerceScalar (SingleScalarType ta) VectorScalarType{} a = vector ta a
  where
    vector :: SingleType a -> a -> Vec n b
    vector (NumSingleType t) = num t

    num :: NumType a -> a -> Vec n b
    num (IntegralNumType t) = integral t
    num (FloatingNumType t) = floating t

    integral :: IntegralType a -> a -> Vec n b
    integral TypeInt{}     = poke
    integral TypeInt8{}    = poke
    integral TypeInt16{}   = poke
    integral TypeInt32{}   = poke
    integral TypeInt64{}   = poke
    integral TypeWord{}    = poke
    integral TypeWord8{}   = poke
    integral TypeWord16{}  = poke
    integral TypeWord32{}  = poke
    integral TypeWord64{}  = poke

    floating :: FloatingType a -> a -> Vec n b
    floating TypeHalf{}    = poke
    floating TypeFloat{}   = poke
    floating TypeDouble{}  = poke

    {-# INLINE poke #-}
    poke :: forall a b n. Prim a => a -> Vec n b
    poke x = runST $ do
      mba <- newByteArray (sizeOf (undefined::a))
      writeByteArray mba 0 x
      ByteArray ba# <- unsafeFreezeByteArray mba
      return $ Vec ba#

evalCoerceScalar VectorScalarType{} (SingleScalarType tb) a = scalar tb a
  where
    scalar :: SingleType b -> Vec n a -> b
    scalar (NumSingleType t) = num t

    num :: NumType b -> Vec n a -> b
    num (IntegralNumType t) = integral t
    num (FloatingNumType t) = floating t

    integral :: IntegralType b -> Vec n a -> b
    integral TypeInt{}     = peek
    integral TypeInt8{}    = peek
    integral TypeInt16{}   = peek
    integral TypeInt32{}   = peek
    integral TypeInt64{}   = peek
    integral TypeWord{}    = peek
    integral TypeWord8{}   = peek
    integral TypeWord16{}  = peek
    integral TypeWord32{}  = peek
    integral TypeWord64{}  = peek

    floating :: FloatingType b -> Vec n a -> b
    floating TypeHalf{}    = peek
    floating TypeFloat{}   = peek
    floating TypeDouble{}  = peek

    {-# INLINE peek #-}
    peek :: Prim a => Vec n b -> a
    peek (Vec ba#) = indexByteArray (ByteArray ba#) 0


-- Scalar primitives
-- -----------------

evalPrimConst :: PrimConst a -> a
evalPrimConst (PrimMinBound ty) = evalMinBound ty
evalPrimConst (PrimMaxBound ty) = evalMaxBound ty
evalPrimConst (PrimPi       ty) = evalPi ty

evalPrim :: PrimFun (a -> r) -> (a -> r)
evalPrim (PrimAdd                ty) = evalAdd ty
evalPrim (PrimSub                ty) = evalSub ty
evalPrim (PrimMul                ty) = evalMul ty
evalPrim (PrimNeg                ty) = evalNeg ty
evalPrim (PrimAbs                ty) = evalAbs ty
evalPrim (PrimSig                ty) = evalSig ty
evalPrim (PrimQuot               ty) = evalQuot ty
evalPrim (PrimRem                ty) = evalRem ty
evalPrim (PrimQuotRem            ty) = evalQuotRem ty
evalPrim (PrimIDiv               ty) = evalIDiv ty
evalPrim (PrimMod                ty) = evalMod ty
evalPrim (PrimDivMod             ty) = evalDivMod ty
evalPrim (PrimBAnd               ty) = evalBAnd ty
evalPrim (PrimBOr                ty) = evalBOr ty
evalPrim (PrimBXor               ty) = evalBXor ty
evalPrim (PrimBNot               ty) = evalBNot ty
evalPrim (PrimBShiftL            ty) = evalBShiftL ty
evalPrim (PrimBShiftR            ty) = evalBShiftR ty
evalPrim (PrimBRotateL           ty) = evalBRotateL ty
evalPrim (PrimBRotateR           ty) = evalBRotateR ty
evalPrim (PrimPopCount           ty) = evalPopCount ty
evalPrim (PrimCountLeadingZeros  ty) = evalCountLeadingZeros ty
evalPrim (PrimCountTrailingZeros ty) = evalCountTrailingZeros ty
evalPrim (PrimFDiv               ty) = evalFDiv ty
evalPrim (PrimRecip              ty) = evalRecip ty
evalPrim (PrimSin                ty) = evalSin ty
evalPrim (PrimCos                ty) = evalCos ty
evalPrim (PrimTan                ty) = evalTan ty
evalPrim (PrimAsin               ty) = evalAsin ty
evalPrim (PrimAcos               ty) = evalAcos ty
evalPrim (PrimAtan               ty) = evalAtan ty
evalPrim (PrimSinh               ty) = evalSinh ty
evalPrim (PrimCosh               ty) = evalCosh ty
evalPrim (PrimTanh               ty) = evalTanh ty
evalPrim (PrimAsinh              ty) = evalAsinh ty
evalPrim (PrimAcosh              ty) = evalAcosh ty
evalPrim (PrimAtanh              ty) = evalAtanh ty
evalPrim (PrimExpFloating        ty) = evalExpFloating ty
evalPrim (PrimSqrt               ty) = evalSqrt ty
evalPrim (PrimLog                ty) = evalLog ty
evalPrim (PrimFPow               ty) = evalFPow ty
evalPrim (PrimLogBase            ty) = evalLogBase ty
evalPrim (PrimTruncate        ta tb) = evalTruncate ta tb
evalPrim (PrimRound           ta tb) = evalRound ta tb
evalPrim (PrimFloor           ta tb) = evalFloor ta tb
evalPrim (PrimCeiling         ta tb) = evalCeiling ta tb
evalPrim (PrimAtan2              ty) = evalAtan2 ty
evalPrim (PrimIsNaN              ty) = evalIsNaN ty
evalPrim (PrimIsInfinite         ty) = evalIsInfinite ty
evalPrim (PrimLt                 ty) = evalLt ty
evalPrim (PrimGt                 ty) = evalGt ty
evalPrim (PrimLtEq               ty) = evalLtEq ty
evalPrim (PrimGtEq               ty) = evalGtEq ty
evalPrim (PrimEq                 ty) = evalEq ty
evalPrim (PrimNEq                ty) = evalNEq ty
evalPrim (PrimMax                ty) = evalMax ty
evalPrim (PrimMin                ty) = evalMin ty
evalPrim PrimLAnd                    = evalLAnd
evalPrim PrimLOr                     = evalLOr
evalPrim PrimLNot                    = evalLNot
evalPrim (PrimFromIntegral ta tb)    = evalFromIntegral ta tb
evalPrim (PrimToFloating ta tb)      = evalToFloating ta tb


-- Implementation of scalar primitives
-- -----------------------------------

toBool :: PrimBool -> Bool
toBool 0 = False
toBool _ = True

fromBool :: Bool -> PrimBool
fromBool False = 0
fromBool True  = 1

evalLAnd :: (PrimBool, PrimBool) -> PrimBool
evalLAnd (x, y) = fromBool (toBool x && toBool y)

evalLOr  :: (PrimBool, PrimBool) -> PrimBool
evalLOr (x, y) = fromBool (toBool x || toBool y)

evalLNot :: PrimBool -> PrimBool
evalLNot = fromBool . not . toBool

evalFromIntegral :: IntegralType a -> NumType b -> a -> b
evalFromIntegral ta (IntegralNumType tb)
  | IntegralDict <- integralDict ta
  , IntegralDict <- integralDict tb
  = fromIntegral

evalFromIntegral ta (FloatingNumType tb)
  | IntegralDict <- integralDict ta
  , FloatingDict <- floatingDict tb
  = fromIntegral

evalToFloating :: NumType a -> FloatingType b -> a -> b
evalToFloating (IntegralNumType ta) tb
  | IntegralDict <- integralDict ta
  , FloatingDict <- floatingDict tb
  = realToFrac

evalToFloating (FloatingNumType ta) tb
  | FloatingDict <- floatingDict ta
  , FloatingDict <- floatingDict tb
  = realToFrac


-- Extract methods from reified dictionaries
--

-- Constant methods of Bounded
--

evalMinBound :: BoundedType a -> a
evalMinBound (IntegralBoundedType ty)
  | IntegralDict <- integralDict ty
  = minBound

evalMaxBound :: BoundedType a -> a
evalMaxBound (IntegralBoundedType ty)
  | IntegralDict <- integralDict ty
  = maxBound

-- Constant method of floating
--

evalPi :: FloatingType a -> a
evalPi ty | FloatingDict <- floatingDict ty = pi

evalSin :: FloatingType a -> (a -> a)
evalSin ty | FloatingDict <- floatingDict ty = sin

evalCos :: FloatingType a -> (a -> a)
evalCos ty | FloatingDict <- floatingDict ty = cos

evalTan :: FloatingType a -> (a -> a)
evalTan ty | FloatingDict <- floatingDict ty = tan

evalAsin :: FloatingType a -> (a -> a)
evalAsin ty | FloatingDict <- floatingDict ty = asin

evalAcos :: FloatingType a -> (a -> a)
evalAcos ty | FloatingDict <- floatingDict ty = acos

evalAtan :: FloatingType a -> (a -> a)
evalAtan ty | FloatingDict <- floatingDict ty = atan

evalSinh :: FloatingType a -> (a -> a)
evalSinh ty | FloatingDict <- floatingDict ty = sinh

evalCosh :: FloatingType a -> (a -> a)
evalCosh ty | FloatingDict <- floatingDict ty = cosh

evalTanh :: FloatingType a -> (a -> a)
evalTanh ty | FloatingDict <- floatingDict ty = tanh

evalAsinh :: FloatingType a -> (a -> a)
evalAsinh ty | FloatingDict <- floatingDict ty = asinh

evalAcosh :: FloatingType a -> (a -> a)
evalAcosh ty | FloatingDict <- floatingDict ty = acosh

evalAtanh :: FloatingType a -> (a -> a)
evalAtanh ty | FloatingDict <- floatingDict ty = atanh

evalExpFloating :: FloatingType a -> (a -> a)
evalExpFloating ty | FloatingDict <- floatingDict ty = exp

evalSqrt :: FloatingType a -> (a -> a)
evalSqrt ty | FloatingDict <- floatingDict ty = sqrt

evalLog :: FloatingType a -> (a -> a)
evalLog ty | FloatingDict <- floatingDict ty = log

evalFPow :: FloatingType a -> ((a, a) -> a)
evalFPow ty | FloatingDict <- floatingDict ty = uncurry (**)

evalLogBase :: FloatingType a -> ((a, a) -> a)
evalLogBase ty | FloatingDict <- floatingDict ty = uncurry logBase

evalTruncate :: FloatingType a -> IntegralType b -> (a -> b)
evalTruncate ta tb
  | FloatingDict <- floatingDict ta
  , IntegralDict <- integralDict tb
  = truncate

evalRound :: FloatingType a -> IntegralType b -> (a -> b)
evalRound ta tb
  | FloatingDict <- floatingDict ta
  , IntegralDict <- integralDict tb
  = round

evalFloor :: FloatingType a -> IntegralType b -> (a -> b)
evalFloor ta tb
  | FloatingDict <- floatingDict ta
  , IntegralDict <- integralDict tb
  = floor

evalCeiling :: FloatingType a -> IntegralType b -> (a -> b)
evalCeiling ta tb
  | FloatingDict <- floatingDict ta
  , IntegralDict <- integralDict tb
  = ceiling

evalAtan2 :: FloatingType a -> ((a, a) -> a)
evalAtan2 ty | FloatingDict <- floatingDict ty = uncurry atan2

evalIsNaN :: FloatingType a -> (a -> PrimBool)
evalIsNaN ty | FloatingDict <- floatingDict ty = fromBool . isNaN

evalIsInfinite :: FloatingType a -> (a -> PrimBool)
evalIsInfinite ty | FloatingDict <- floatingDict ty = fromBool . isInfinite


-- Methods of Num
--

evalAdd :: NumType a -> ((a, a) -> a)
evalAdd (IntegralNumType ty) | IntegralDict <- integralDict ty = uncurry (+)
evalAdd (FloatingNumType ty) | FloatingDict <- floatingDict ty = uncurry (+)

evalSub :: NumType a -> ((a, a) -> a)
evalSub (IntegralNumType ty) | IntegralDict <- integralDict ty = uncurry (-)
evalSub (FloatingNumType ty) | FloatingDict <- floatingDict ty = uncurry (-)

evalMul :: NumType a -> ((a, a) -> a)
evalMul (IntegralNumType ty) | IntegralDict <- integralDict ty = uncurry (*)
evalMul (FloatingNumType ty) | FloatingDict <- floatingDict ty = uncurry (*)

evalNeg :: NumType a -> (a -> a)
evalNeg (IntegralNumType ty) | IntegralDict <- integralDict ty = negate
evalNeg (FloatingNumType ty) | FloatingDict <- floatingDict ty = negate

evalAbs :: NumType a -> (a -> a)
evalAbs (IntegralNumType ty) | IntegralDict <- integralDict ty = abs
evalAbs (FloatingNumType ty) | FloatingDict <- floatingDict ty = abs

evalSig :: NumType a -> (a -> a)
evalSig (IntegralNumType ty) | IntegralDict <- integralDict ty = signum
evalSig (FloatingNumType ty) | FloatingDict <- floatingDict ty = signum

evalQuot :: IntegralType a -> ((a, a) -> a)
evalQuot ty | IntegralDict <- integralDict ty = uncurry quot

evalRem :: IntegralType a -> ((a, a) -> a)
evalRem ty | IntegralDict <- integralDict ty = uncurry rem

evalQuotRem :: IntegralType a -> ((a, a) -> (a, a))
evalQuotRem ty | IntegralDict <- integralDict ty = uncurry quotRem

evalIDiv :: IntegralType a -> ((a, a) -> a)
evalIDiv ty | IntegralDict <- integralDict ty = uncurry div

evalMod :: IntegralType a -> ((a, a) -> a)
evalMod ty | IntegralDict <- integralDict ty = uncurry mod

evalDivMod :: IntegralType a -> ((a, a) -> (a, a))
evalDivMod ty | IntegralDict <- integralDict ty = uncurry divMod

evalBAnd :: IntegralType a -> ((a, a) -> a)
evalBAnd ty | IntegralDict <- integralDict ty = uncurry (.&.)

evalBOr :: IntegralType a -> ((a, a) -> a)
evalBOr ty | IntegralDict <- integralDict ty = uncurry (.|.)

evalBXor :: IntegralType a -> ((a, a) -> a)
evalBXor ty | IntegralDict <- integralDict ty = uncurry xor

evalBNot :: IntegralType a -> (a -> a)
evalBNot ty | IntegralDict <- integralDict ty = complement

evalBShiftL :: IntegralType a -> ((a, Int) -> a)
evalBShiftL ty | IntegralDict <- integralDict ty = uncurry shiftL

evalBShiftR :: IntegralType a -> ((a, Int) -> a)
evalBShiftR ty | IntegralDict <- integralDict ty = uncurry shiftR

evalBRotateL :: IntegralType a -> ((a, Int) -> a)
evalBRotateL ty | IntegralDict <- integralDict ty = uncurry rotateL

evalBRotateR :: IntegralType a -> ((a, Int) -> a)
evalBRotateR ty | IntegralDict <- integralDict ty = uncurry rotateR

evalPopCount :: IntegralType a -> (a -> Int)
evalPopCount ty | IntegralDict <- integralDict ty = popCount

evalCountLeadingZeros :: IntegralType a -> (a -> Int)
evalCountLeadingZeros ty | IntegralDict <- integralDict ty = countLeadingZeros

evalCountTrailingZeros :: IntegralType a -> (a -> Int)
evalCountTrailingZeros ty | IntegralDict <- integralDict ty = countTrailingZeros

evalFDiv :: FloatingType a -> ((a, a) -> a)
evalFDiv ty | FloatingDict <- floatingDict ty = uncurry (/)

evalRecip :: FloatingType a -> (a -> a)
evalRecip ty | FloatingDict <- floatingDict ty = recip


evalLt :: SingleType a -> ((a, a) -> PrimBool)
evalLt (NumSingleType (IntegralNumType ty)) | IntegralDict <- integralDict ty = fromBool . uncurry (<)
evalLt (NumSingleType (FloatingNumType ty)) | FloatingDict <- floatingDict ty = fromBool . uncurry (<)

evalGt :: SingleType a -> ((a, a) -> PrimBool)
evalGt (NumSingleType (IntegralNumType ty)) | IntegralDict <- integralDict ty = fromBool . uncurry (>)
evalGt (NumSingleType (FloatingNumType ty)) | FloatingDict <- floatingDict ty = fromBool . uncurry (>)

evalLtEq :: SingleType a -> ((a, a) -> PrimBool)
evalLtEq (NumSingleType (IntegralNumType ty)) | IntegralDict <- integralDict ty = fromBool . uncurry (<=)
evalLtEq (NumSingleType (FloatingNumType ty)) | FloatingDict <- floatingDict ty = fromBool . uncurry (<=)

evalGtEq :: SingleType a -> ((a, a) -> PrimBool)
evalGtEq (NumSingleType (IntegralNumType ty)) | IntegralDict <- integralDict ty = fromBool . uncurry (>=)
evalGtEq (NumSingleType (FloatingNumType ty)) | FloatingDict <- floatingDict ty = fromBool . uncurry (>=)

evalEq :: SingleType a -> ((a, a) -> PrimBool)
evalEq (NumSingleType (IntegralNumType ty)) | IntegralDict <- integralDict ty = fromBool . uncurry (==)
evalEq (NumSingleType (FloatingNumType ty)) | FloatingDict <- floatingDict ty = fromBool . uncurry (==)

evalNEq :: SingleType a -> ((a, a) -> PrimBool)
evalNEq (NumSingleType (IntegralNumType ty)) | IntegralDict <- integralDict ty = fromBool . uncurry (/=)
evalNEq (NumSingleType (FloatingNumType ty)) | FloatingDict <- floatingDict ty = fromBool . uncurry (/=)

evalMax :: SingleType a -> ((a, a) -> a)
evalMax (NumSingleType (IntegralNumType ty)) | IntegralDict <- integralDict ty = uncurry max
evalMax (NumSingleType (FloatingNumType ty)) | FloatingDict <- floatingDict ty = uncurry max

evalMin :: SingleType a -> ((a, a) -> a)
evalMin (NumSingleType (IntegralNumType ty)) | IntegralDict <- integralDict ty = uncurry min
evalMin (NumSingleType (FloatingNumType ty)) | FloatingDict <- floatingDict ty = uncurry min
