{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE RankNTypes           #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns         #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeOperators        #-}
-- |
-- Module      : Data.Array.Accelerate.Trafo.Desugar
-- Copyright   : [2012..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.Trafo.Desugar
  where

import qualified Data.Array.Accelerate.AST as Named
import Data.Array.Accelerate.AST.Environment          hiding ( Val )
import Data.Array.Accelerate.AST.Idx
import Data.Array.Accelerate.AST.Var
import Data.Array.Accelerate.AST.Operation
import Data.Array.Accelerate.AST.LeftHandSide
import Data.Array.Accelerate.Analysis.Match           ((:~:)(..))
import Data.Array.Accelerate.Representation.Array
import Data.Array.Accelerate.Representation.Ground
import Data.Array.Accelerate.Representation.Shape
import Data.Array.Accelerate.Representation.Slice
import Data.Array.Accelerate.Representation.Stencil
import Data.Array.Accelerate.Representation.Type
import Data.Array.Accelerate.Sugar.Foreign
import Data.Array.Accelerate.Trafo.Exp.Substitution
import Data.Array.Accelerate.Trafo.Operation.Substitution
import Data.Array.Accelerate.Trafo.Var
import Data.Array.Accelerate.Type
import Data.Array.Accelerate.Error
import Data.Kind
import Data.Maybe (isJust)

type a $ b = a b
infixr 0 $

-- | Vanilla boundary condition specification for stencil operations
-- Note that this data type is not used in the actual AST, it is just
-- used to pass to 'mkStencil' or 'mkStencil2'.
--
data Boundary env t where
  -- Clamp coordinates to the extent of the array
  Clamp     :: Boundary env t

  -- Mirror coordinates beyond the array extent
  Mirror    :: Boundary env t

  -- Wrap coordinates around on each dimension
  Wrap      :: Boundary env t

  -- Use a constant value for outlying coordinates
  Constant  :: e
            -> Boundary env (Array sh e)

  -- Apply the given function to outlying coordinates
  Function  :: Fun env (sh -> e)
            -> Boundary env (Array sh e)


class NFData' op => DesugarAcc (op :: Type -> Type) where
  mkMap         :: Arg env (Fun' (s -> t))
                -> Arg env (In sh s)
                -> Arg env (Out sh t)
                -> OperationAcc op env ()
  mkMap f input output = mkTransform (ArgFun $ identity $ shapeType shr) f input output
    where
      ArrayR shr _ = argArrayR input

  mkBackpermute :: Arg env (Fun' (sh' -> sh))
                -> Arg env (In sh t)
                -> Arg env (Out sh' t)
                -> OperationAcc op env ()
  mkBackpermute f input output = mkTransform f (ArgFun $ identity tp) input output
    where
      ArrayR _ tp = argArrayR input

  -- TODO why does this exist? Transform is an artifact of the old fusion, so should never occur (or should simply be a composition of map and backpermute, in any order)
  mkTransform   :: Arg env (Fun' (sh' -> sh))
                -> Arg env (Fun' (s -> t))
                -> Arg env (In sh s)
                -> Arg env (Out sh' t)
                -> OperationAcc op env ()
  mkTransform (ArgFun f) (ArgFun g) (ArgArray _ repr sh buffers) output = mkGenerate (ArgFun h) output
    where
      h = g `compose` indexFunction repr sh buffers `compose` f

  mkGenerate    :: Arg env (Fun' (sh -> t))
                -> Arg env (Out sh t)
                -> OperationAcc op env ()

  -- Copies the contents of the (prefix of the) input to the output.
  -- The size of the input array is smaller than or equal to the size output.
  mkShrink      :: Arg env (In  sh t)
                -> Arg env (Out sh t)
                -> OperationAcc op env ()
  mkShrink input@( ArgArray _ (ArrayR shr _) sh1 _) 
           output@(ArgArray _ _              sh2 _) = if isJust (matchVars sh1 sh2)
             then mkCopy input output 
             else mkBackpermute (ArgFun $ identity $ shapeType shr) input output

  -- Copies a buffer. This is used before passing a buffer to a 'Mut' argument,
  -- to make sure it is unique. This may be removed during fusion to facilitate
  -- in-place updates
  -- TODO: Perform one map per buffer, instead of one for the whole array
  -- this gives more freedom to the ILP
  mkCopy        :: Arg env (In  sh t)
                -> Arg env (Out sh t)
                -> OperationAcc op env ()
  mkCopy input@(ArgArray _ (ArrayR _ tp) _ _) output = mkMap (ArgFun $ identity tp) input output

  mkZipWith     :: Arg env (Fun' (e1 -> e2 -> e3))
                -> Arg env (In  sh e1)
                -> Arg env (In  sh e2)
                -> Arg env (Out sh e3)
                -> OperationAcc op env ()
  mkZipWith (ArgFun f) 
            in1@(ArgArray _ (ArrayR _ ty1) _ _)
            in2@(ArgArray _ (ArrayR _ ty2) _ _)
                (ArgArray _ outR@(ArrayR shr _) sh buf)
    | DeclareVars lhs w k <- declareVars $ buffersR (TupRpair ty1 ty2) =
      let
        typ = TupRpair ty1 ty2
        zippedArg  = ArgArray Out (ArrayR shr typ) (weakenVars w sh) (k weakenId)
        zippedArg' = ArgArray In  (ArrayR shr typ) (weakenVars w sh) (k weakenId) in
      aletUnique lhs (desugarAlloc (ArrayR shr typ) (fromGrounds sh)) $
        alet LeftHandSideUnit
          (mkZip (weaken w in1) (weaken w in2) zippedArg) $
          mkMap (ArgFun . uncurry' $ weakenArrayInstr w f) zippedArg' $ ArgArray Out outR (weakenVars w sh) (weakenVars w buf)

  mkZip :: Arg env (In sh e1)
        -> Arg env (In sh e2)
        -> Arg env (Out sh (e1, e2))
        -> OperationAcc op env ()
  mkZip in1@(ArgArray _ (ArrayR shr ty1) _ _)
        in2@(ArgArray _ (ArrayR _   ty2) _ _) 
            (ArgArray _ (ArrayR _ _) sh (TupRpair buf1 buf2)) =
        alet LeftHandSideUnit
          (mkShrink in1 (ArgArray Out (ArrayR shr ty1) sh buf1))
          (mkShrink in2 (ArgArray Out (ArrayR shr ty2) sh buf2))


  mkZip _ _ _ = error "out buffer to mkZip is not a pair"


  mkReplicate   :: SliceIndex slix sl co sh
                -> Arg env (Var' slix)
                -> Arg env (In  sl e)
                -> Arg env (Out sh e)
                -> OperationAcc op env ()
  mkReplicate sliceIx slix = mkBackpermute (ArgFun $ extend sliceIx slix)

  mkSlice       :: SliceIndex slix sl co sh
                -> Arg env (Var' slix)
                -> Arg env (In  sh e)
                -> Arg env (Out sl e)
                -> OperationAcc op env ()
  mkSlice sliceIx slix = mkBackpermute (ArgFun $ restrict sliceIx slix)

  mkPermute     :: Arg env (Fun' (e -> e -> e))
                -> Arg env (Mut sh' e)
                -> Arg env (Fun' (sh -> PrimMaybe sh'))
                -> Arg env (In sh e)
                -> OperationAcc op env ()

  mkStencil     :: StencilR sh e stencil
                -> Arg env (Fun' (stencil -> e'))
                -> Boundary env (Array sh e)
                -> Arg env (In sh e)
                -> Arg env (Out sh e')
                -> OperationAcc op env ()
  -- Default implementation for mkStencil uses 'generate'. It includes the conditional code for the boundary on all elements, making it less efficient
  -- than a specialized implementation.
  --
  mkStencil sr (ArgFun f) boundary input output@(ArgArray _ (ArrayR _ tp) _ _)
    = mkGenerate (ArgFun $ desugarStencilFun sr tp f (Just boundary) input) output

  mkStencil2    :: StencilR sh a stencil1
                -> StencilR sh b stencil2
                -> Arg env (Fun' (stencil1 -> stencil2 -> c))
                -> Boundary env (Array sh a)
                -> Arg env (In sh a)
                -> Boundary env (Array sh b)
                -> Arg env (In sh b)
                -> Arg env (Out sh c)
                -> OperationAcc op env ()
  -- Default implementation for mkStencil uses 'generate'. It includes the conditional code for the boundary on all elements, making it less efficient
  -- than a specialized implementation.
  -- XXX: Could we define this in terms of mkStencil and a zip? Maybe only if the sizes of the two input arrays are equal?
  --
  mkStencil2 sr1 sr2 (ArgFun f) boundary1 input1 boundary2 input2 output@(ArgArray _ (ArrayR _ tp) _ _)
    = mkGenerate (ArgFun $ desugarStencil2Fun sr1 sr2 tp f (Just boundary1) input1 (Just boundary2) input2) output

  mkFold        :: Arg env (Fun' (e -> e -> e))
                -> Maybe (Arg env (Exp' e))
                -> Arg env (In  (sh, Int) e)
                -> Arg env (Out sh        e)
                -> OperationAcc op env ()
  mkFold f def input@(ArgArray _ _ _ _) output = mkDefaultFoldSequential f def input output

  mkFoldSeg     :: IntegralType i
                -> Arg env (Fun' (e -> e -> e))
                -> Maybe (Arg env (Exp' e))
                -> Arg env (In  (sh, Int) e)
                -> Arg env (In  DIM1      i)
                -> Arg env (Out (sh, Int) e)
                -> OperationAcc op env ()
  -- Default implementation using generate. It is sequential per segment, which is inefficient for some backends.
  mkFoldSeg itp f def input segments = mkGenerate (ArgFun $ mkDefaultFoldSegFunction itp f def input segments)

  mkScan        :: Direction
                -> Arg env (Fun' (e -> e -> e))
                -> Maybe (Arg env (Exp' e))
                -> Arg env (In  (sh, Int) e)
                -> Arg env (Out (sh, Int) e)
                -> OperationAcc op env ()
  mkScan dir f (Just def) argIn@(ArgArray _ (ArrayR shr tp) _ _) argOut@(ArgArray _ _ shOut _)
    | DeclareVars lhsTmp kTmp valueTmp <- declareVars $ buffersR tp -- Allocate buffers to prepend the default value
    = let
        shOut' = weakenVars kTmp shOut

        argG = ArgFun $ mkDefaultScanPrepend dir (weaken kTmp def) (weaken kTmp argIn)
        argTmp' = ArgArray Out (ArrayR shr tp) shOut' (valueTmp weakenId)
        argTmp  = ArgArray In  (ArrayR shr tp) shOut' (valueTmp weakenId)
      in
        aletUnique lhsTmp (desugarAlloc (ArrayR shr tp) $ groundToExpVar (shapeType shr) shOut)
          $ alet (LeftHandSideWildcard TupRunit) (mkGenerate argG argTmp')
          $ mkScan dir (weaken kTmp f) Nothing argTmp (weaken kTmp argOut)
  mkScan dir f Nothing (ArgArray _ (ArrayR shr tp) sh input) argOut
  -- (inc, tmp) = awhile (\(inc, _) -> inc < (n+1) / 2) (\(inc, a) -> (inc*2, generate {\i -> reduce i and i +/- inc in a})) input
  -- generate {\i -> reduce i and i +/- inc in tmp}
  -- 
  -- Note that the last iteration of the loop is decoupled, as that will output into argOut,
  -- instead of a temporary array.
    | DeclareVars lhsTmp   kTmp   valueTmp   <- declareVars $ buffersR tp
    , DeclareVars lhsAlloc kAlloc valueAlloc <- declareVars $ buffersR tp
    = let
        lhs = LeftHandSidePair (LeftHandSideSingle $ GroundRscalar scalarTypeInt) lhsTmp
        argTmp = ArgArray In (ArrayR shr tp) (weakenVars (weakenSucc $ weakenSucc kTmp) sh) (valueTmp weakenId)
        reduce = ArgFun $ mkDefaultScanFunction dir (weaken kTmp (Var (GroundRscalar $ scalarTypeInt) ZeroIdx)) (weaken (weakenSucc $ weakenSucc kTmp) f) argTmp

        n = case sh of
          TupRpair _ n' -> paramsIn (TupRsingle scalarTypeInt) $ weakenVars (weakenSucc $ weakenSucc weakenId) n'
          _ -> error "Impossible pair"

        -- Awhile condition
        c = Alam (LeftHandSidePair (LeftHandSideSingle $ GroundRscalar scalarTypeInt) $ LeftHandSideWildcard $ buffersR tp)
              $ Abody
              $ Compute
              $ mkBinary (PrimLt singleType) (paramIn' $ Var scalarTypeInt ZeroIdx)
              $ mkBinary
                (PrimBShiftR integralType)
                (mkBinary (PrimAdd numType) n (mkConstant (TupRsingle scalarTypeInt) 1))
                (mkConstant (TupRsingle scalarTypeInt) 1) -- (n+1)/2

        argAlloc = ArgArray Out (ArrayR shr tp) (weakenVars (weakenSucc $ weakenSucc $ kAlloc .> kTmp) sh) (valueAlloc weakenId)
        -- Awhile step function
        g = Alam lhs
              $ Abody
              $ aletUnique lhsAlloc (desugarAlloc (ArrayR shr tp) $ groundToExpVar (shapeType shr) $ weakenVars (weakenSucc $ weakenSucc kTmp) sh)
              $ alet (LeftHandSideWildcard TupRunit) (mkGenerate (weaken kAlloc reduce) argAlloc)
              $ alet (LeftHandSideSingle $ GroundRscalar scalarTypeInt)
                (Compute $ mkBinary (PrimBShiftL integralType) (paramIn' $ weaken (kAlloc .> kTmp) $ Var scalarTypeInt ZeroIdx) (mkConstant (TupRsingle scalarTypeInt) 1)) -- n * 2
              $ Return $ TupRsingle (Var (GroundRscalar scalarTypeInt) ZeroIdx) `TupRpair` valueAlloc (weakenSucc weakenId)
      in
        alet (LeftHandSideSingle $ GroundRscalar scalarTypeInt) (Compute $ mkConstant (TupRsingle scalarTypeInt) 1)
          $ alet lhs (Awhile (shared $ lhsToTupR lhs) c g (TupRsingle (Var (GroundRscalar scalarTypeInt) ZeroIdx) `TupRpair` weakenVars (weakenSucc weakenId) input))
          $ mkGenerate reduce (weaken (weakenSucc $ weakenSucc kTmp) argOut)

  mkScan'       :: Direction
                -> Arg env (Fun' (e -> e -> e))
                -> Arg env (Exp' e)
                -> Arg env (In  (sh, Int) e)
                -> Arg env (Out (sh, Int) e)
                -> Arg env (Out sh        e)
                -> OperationAcc op env ()
  mkScan' dir f def input@(ArgArray _ (ArrayR shr@(ShapeRsnoc shr') tp) sh _) out1 out2
    | DeclareVars lhsTmp kTmp valueTmp <- declareVars $ buffersR tp -- Allocate buffers for the output of scan
    , DeclareVars lhsSh  _    valueSh  <- declareVars $ shapeType shr' -- Used in the function in backpermute
    = let
        (x, y) = case sh of
          TupRpair x' y' -> (x', y')
          _ -> error "Impossible pair"

        shTmp'  = weakenVars (weakenSucc weakenId) x `TupRpair` TupRsingle (Var (GroundRscalar scalarTypeInt) ZeroIdx)
        shTmp   = weakenVars kTmp shTmp'
        k       = kTmp .> weakenSucc weakenId
        argTmp  = ArgArray In (ArrayR shr tp) shTmp (valueTmp weakenId)
        argTmp' = ArgArray Out (ArrayR shr tp) shTmp (valueTmp weakenId)

        -- Fills 'out2'
        argG = ArgFun $ Lam lhsSh $ Body $ Pair (expVars $ valueSh weakenId) $ case dir of
          LeftToRight -> paramsIn (TupRsingle scalarTypeInt) $ weakenVars k y
          RightToLeft -> mkConstant (TupRsingle scalarTypeInt) 0

        -- Fills 'out1' in case of a RightToLeft scan
        argH = ArgFun
              $ Lam (LeftHandSidePair lhsSh $ LeftHandSideSingle scalarTypeInt)
              $ Body
              $ Pair
                  (expVars $ valueSh $ weakenSucc weakenId)
                  (mkBinary (PrimAdd numType) (Evar (Var scalarTypeInt ZeroIdx)) (mkConstant (TupRsingle scalarTypeInt) 0))
      in
        alet (LeftHandSideSingle $ GroundRscalar scalarTypeInt) (Compute $ mkBinary (PrimAdd numType) (paramsIn (TupRsingle scalarTypeInt) y) $ mkConstant (TupRsingle scalarTypeInt) 1)
          $ aletUnique lhsTmp (desugarAlloc (ArrayR shr tp) $ groundToExpVar (shapeType shr) shTmp')
          $ alet (LeftHandSideWildcard TupRunit) (mkScan dir (weaken k f) (Just $ weaken k def) (weaken k input) argTmp')
          $ alet (LeftHandSideWildcard TupRunit) (case dir of
              LeftToRight -> mkShrink argTmp $ weaken k out1
              RightToLeft -> mkBackpermute argH argTmp $ weaken k out1
            )
          $ alet (LeftHandSideWildcard TupRunit) (mkBackpermute argG argTmp $ weaken k out2)
          $ Return TupRunit

  mkForeign     :: Foreign asm
                => ArraysR bs
                -> asm (as -> bs)
                -> GroundVars env (DesugaredArrays as)
                -> Maybe (OperationAcc op env (DesugaredArrays bs))
  mkForeign _ _ _ = Nothing

  -- Whether it is prefered to not use scalar operations.
  -- When this is true, a 0-dimensional generate or map will
  -- be converted to Compute nodes, instead of Exec nodes.
  desugarPreferNoScalar :: Bool
  desugarPreferNoScalar = True

desugar :: (HasCallStack, DesugarAcc op) => Named.Acc a -> OperationAcc op () (DesugaredArrays a)
desugar = desugarOpenAcc Empty

desugarAfun :: (HasCallStack, DesugarAcc op) => Named.Afun a -> OperationAfun op () (DesugaredAfun a)
desugarAfun = desugarOpenAfun Empty

data ArrayDescriptor env a where
  ArrayDescriptor :: ShapeR sh
                  -> GroundVars env sh
                  -> GroundVars env (Buffers e)
                  -> ArrayDescriptor env (Array sh e)

weakenArrayDescriptor :: (env :> env') -> ArrayDescriptor env a -> ArrayDescriptor env' a
weakenArrayDescriptor k (ArrayDescriptor shr sh buffers) = ArrayDescriptor shr (weakenVars k sh) (weakenVars k buffers)

type BEnv benv = Env (ArrayDescriptor benv)

desugarOpenAcc :: forall op benv aenv a.
                  (HasCallStack, DesugarAcc op)
               => BEnv benv aenv
               -> Named.OpenAcc aenv a
               -> OperationAcc op benv (DesugaredArrays a)
desugarOpenAcc env = travA
  where
    travE :: Named.Exp aenv t -> Exp benv t
    travE = desugarExp env

    travA :: Named.OpenAcc aenv arr -> OperationAcc op benv (DesugaredArrays arr)
    travA (Named.OpenAcc acc) = case acc of
      Named.Alet lhs bnd a
        | DesugaredLHS env' lhs' <- desugarLHS env lhs -> alet lhs' (travA bnd) (desugarOpenAcc env' a)
      Named.Avar (Var _ ix)
        | ArrayDescriptor _ sh bf <- prj' ix env -> Return (TupRpair sh bf)
      Named.Apair a b -> pair (travA a) (travA b)
      Named.Anil       -> Return TupRunit
      Named.Apply repr f arg -> case f of
        Named.Alam lhs (Named.Abody a) -> travA $ Named.OpenAcc $ Named.Alet lhs arg a
        Named.Abody a                  -> arraysRFunctionImpossible $ Named.arraysR a
        Named.Alam _ Named.Alam{}      -> arraysRFunctionImpossible repr
      Named.Aforeign repr asm (Named.Alam lhsA _) arg
        | DeclareVars lhs _ value <- declareVars $ desugarArraysR $ lhsToTupR lhsA
        , Just a <- mkForeign repr asm $ value weakenId
                                       -> alet lhs (travA arg) a
      Named.Aforeign repr _ f arg   -> travA $ Named.OpenAcc $ Named.Apply repr (weaken weakenEmpty f) $ arg
      Named.Acond c t f ->
        let
          lhs  = LeftHandSideSingle $ GroundRscalar scalarTypeWord8
          env' = weakenBEnv (weakenSucc weakenId) env
          var  = Var scalarTypeWord8 ZeroIdx
        in alet lhs (Compute $ travE c) $ Acond var (desugarOpenAcc env' t) (desugarOpenAcc env' f)
      Named.Awhile c f i
        | repr <- Named.arraysR acc
        , Refl <- desugaredAfunIsBody repr
        , DeclareVars lhs k value <- declareVars $ desugarArraysR repr ->
          let
            bufferType    = GroundRbuffer $ scalarTypeWord8
            lhsScalarBool = LeftHandSidePair (LeftHandSideWildcard TupRunit) (LeftHandSideSingle bufferType)
            env'          = weakenBEnv k env
            c'            = case desugarOpenAfun @op env' c of
              Alam lhs' (Abody body) -> Alam lhs' $ Abody $ alet lhsScalarBool body $ Compute $ ArrayInstr (Index $ Var bufferType ZeroIdx) $ Const scalarTypeInt 0
              Abody _                -> error "It's a long time since we last met"
            f'            = desugarOpenAfun env' f
          in alet lhs (travA i) $ awhileRemoveScalars repr (shared $ desugarArraysR repr) c' f' (value weakenId)
      Named.Use repr array -> desugarUse repr array
      Named.Unit tp e
        | DeclareVars lhs _ value <- declareVars tp ->
          let
            go :: forall benv' t. ExpVars benv' t -> OperationAcc op benv' (Buffers t)
            go (TupRpair v1 v2)           = go v1 `pairUnique` go v2
            go TupRunit                   = Return TupRunit
            go (TupRsingle v@(Var repr _))
              | Refl <- reprIsSingle @ScalarType @t @Buffer repr = Unit v
          in
            alet (mapLeftHandSide GroundRscalar lhs) (Compute $ travE e) $ pair (Return TupRunit) $ go (value weakenId)
      -- XXX: Should we check whether the sizes are equal? We could add an Assert constructor to PreOpenAcc,
      -- which we can use to verify the sizes at runtime.
      --
      Named.Reshape shr sh a
        | ArrayR oldShr tp <- Named.arrayR a
        , DeclareVars lhsSh kSh valueSh <- declareVars $ mapTupR GroundRscalar $ shapeType shr
        , DeclareVars lhsBf kBf valueBf <- declareVars $ buffersR tp ->
          alet lhsSh (Compute $ travE sh)
            $ alet (LeftHandSidePair (LeftHandSideWildcard $ mapTupR GroundRscalar $ shapeType oldShr) lhsBf) (desugarOpenAcc (weakenBEnv kSh env) a)
            $ Return (TupRpair (valueSh kBf) (valueBf weakenId))

      -- The remaining constructors of Named.OpenAcc are compiled into operations through the mkXX functions
      -- the type class DesugarAcc. We must here allocate the output arrays of the appropriate size and call
      -- the corresponding mkXX function.
      --

      Named.Permute c def f src
        | ArrayR shr' tp <- Named.arrayR def
        , ArrayR shr  _  <- Named.arrayR src
        , DeclareVars lhsSh' kSh' valueSh' <- declareVars $ shapeType shr'
        , DeclareVars lhsDef kDef valueDef <- declareVars $ buffersR tp
        -- Clone defaults array, to make sure that it is unique. The clone may be removed in a later pass.
        , DeclareVars lhsOut kOut valueOut <- declareVars $ buffersR tp
        , DeclareVars lhsSh  kSh  valueSh  <- declareVars $ shapeType shr
        , DeclareVars lhsSrc kSrc valueSrc <- declareVars $ buffersR tp ->
          let
            lhs'   = LeftHandSidePair (mapLeftHandSide GroundRscalar lhsSh') lhsDef
            lhs    = LeftHandSidePair (mapLeftHandSide GroundRscalar lhsSh)  lhsSrc
            sh'    = mapVars GroundRscalar $ valueSh' (kSrc .> kSh .> kOut .> kDef)
            sh     = mapVars GroundRscalar $ valueSh kSrc
            env'   = weakenBEnv (kSrc .> kSh .> kOut .> kDef .> kSh') env
            valOut = valueOut $ kSrc .> kSh
            argDef = ArgArray In  (ArrayR shr' tp) sh' (valueDef $ kSrc .> kSh .> kOut)
            argOut = ArgArray Out (ArrayR shr' tp) sh' valOut
            argMut = ArgArray Mut (ArrayR shr' tp) sh' valOut
            argSrc = ArgArray In  (ArrayR shr  tp) sh  (valueSrc weakenId)
            argC   = ArgFun $ desugarFun env' c
            argF   = ArgFun $ desugarFun env' f
          in
            alet lhs' (travA def)
              $ aletUnique lhsOut (desugarAlloc (ArrayR shr' tp) (valueSh' kDef))
              $ alet lhs    (desugarOpenAcc (weakenBEnv (kOut .> kDef .> kSh') env) src)
              $ alet (LeftHandSideWildcard TupRunit) (mkCopy argDef argOut)
              $ alet (LeftHandSideWildcard TupRunit) (mkPermute argC argMut argF argSrc)
              $ Return (sh' `TupRpair` valOut)

      Named.Generate (ArrayR ShapeRz tp) _ (Lam (LeftHandSideWildcard _) (Body expr))
        | desugarPreferNoScalar @op ->
          travA $ Named.OpenAcc $ Named.Unit tp expr
      Named.Generate (ArrayR shr tp) sh f
        | DeclareVars lhsSh kSh valueSh <- declareVars $ shapeType shr
        , DeclareVars lhsBf kBf valueBf <- declareVars $ buffersR tp ->
          let
            sh'    = mapVars GroundRscalar $ valueSh kBf
            argF   = ArgFun $ desugarFun (weakenBEnv (kBf .> kSh) env) f
            argOut = ArgArray Out (ArrayR shr tp) sh' (valueBf weakenId)
          in
            alet (mapLeftHandSide GroundRscalar lhsSh) (Compute $ travE sh)
              $ aletUnique lhsBf (desugarAlloc (ArrayR shr tp) (valueSh weakenId))
              $ alet (LeftHandSideWildcard TupRunit) (mkGenerate argF argOut)
              $ Return (sh' `TupRpair` valueBf weakenId)

      Named.Transform (ArrayR shrOut tpOut) shExp idxTransform valueTransform a
        | ArrayR shrIn tpIn <- Named.arrayR a
        , DeclareVars lhsShIn  kShIn  valueShIn  <- declareVars $ mapTupR GroundRscalar $ shapeType shrIn
        , DeclareVars lhsIn    kIn    valueIn    <- declareVars $ buffersR tpIn
        , DeclareVars lhsShOut kShOut valueShOut <- declareVars $ shapeType shrOut
        , DeclareVars lhsOut   kOut   valueOut   <- declareVars $ buffersR tpOut ->
          let
            shOut   = mapVars GroundRscalar $ valueShOut kOut
            bfOut   = valueOut weakenId
            env'    = weakenBEnv (kOut .> kShOut .> kIn .> kShIn) env
            argIdxF = ArgFun $ desugarFun env' idxTransform
            argValF = ArgFun $ desugarFun env' valueTransform
            argIn   = ArgArray In  (ArrayR shrIn  tpIn)  (valueShIn (kOut .> kShOut .> kIn)) (valueIn (kOut .> kShOut))
            argOut  = ArgArray Out (ArrayR shrOut tpOut) shOut bfOut
          in
            alet (LeftHandSidePair lhsShIn lhsIn) (travA a)
              $ alet (mapLeftHandSide GroundRscalar lhsShOut) (Compute $ desugarExp (weakenBEnv (kIn .> kShIn) env) shExp)
              $ aletUnique lhsOut (desugarAlloc (ArrayR shrOut tpOut) (valueShOut weakenId))
              $ alet (LeftHandSideWildcard TupRunit) (mkTransform argIdxF argValF argIn argOut)
              $ Return (shOut `TupRpair` bfOut)

      Named.Map tp (Lam lhs (Body expr)) a
        | desugarPreferNoScalar @op
        , repr@(ArrayR ShapeRz _) <- Named.arrayR a ->
          travA $ Named.OpenAcc
            $ Named.Alet (LeftHandSideSingle repr) a
            $ Named.OpenAcc
            $ Named.Unit tp
            $ Let lhs (ArrayInstr (Named.Index (Var repr ZeroIdx)) Nil)
            $ mapArrayInstr (weaken $ weakenSucc weakenId) expr

      Named.Map _ (Lam lhs (Body e)) a
        | Just vars <- extractExpVars e
        , ArrayR shr oldTp <- Named.arrayR a
        , DeclareVars lhsSh _   valueSh <- declareVars $ mapTupR GroundRscalar $ shapeType shr
        , DeclareVars lhsIn kIn valueIn <- declareVars $ buffersR oldTp ->
          alet (LeftHandSidePair lhsSh lhsIn) (travA a)
            $ Return (valueSh kIn `TupRpair` desugarUnzip (valueIn weakenId) lhs vars)

      Named.Map tp f a
        | ArrayR shr oldTp <- Named.arrayR a
        , DeclareVars lhsSh  kSh  valueSh  <- declareVars $ shapeType shr
        , DeclareVars lhsIn  kIn  valueIn  <- declareVars $ buffersR oldTp
        , DeclareVars lhsOut kOut valueOut <- declareVars $ buffersR tp ->
          let
            lhs    = LeftHandSidePair (mapLeftHandSide GroundRscalar lhsSh) lhsIn
            sh     = mapVars GroundRscalar $ valueSh (kOut .> kIn)
            argF   = ArgFun $ desugarFun (weakenBEnv (kOut .> kIn .> kSh) env) f
            argIn  = ArgArray In (ArrayR shr oldTp) sh (valueIn kOut)
            argOut = ArgArray Out (ArrayR shr tp)   sh (valueOut weakenId)
          in
            alet lhs (travA a)
              $ aletUnique lhsOut (desugarAlloc (ArrayR shr tp) (valueSh kIn))
              $ alet (LeftHandSideWildcard TupRunit) (mkMap argF argIn argOut)
              $ Return (sh `TupRpair` valueOut weakenId)

      Named.Backpermute shrOut shExp f a
        | ArrayR shrIn tp <- Named.arrayR a
        , DeclareVars lhsShIn  kShIn  valueShIn  <- declareVars $ mapTupR GroundRscalar $ shapeType shrIn
        , DeclareVars lhsIn    kIn    valueIn    <- declareVars $ buffersR tp
        , DeclareVars lhsShOut kShOut valueShOut <- declareVars $ shapeType shrOut
        , DeclareVars lhsOut   kOut   valueOut   <- declareVars $ buffersR tp ->
          let
            shOut  = mapVars GroundRscalar $ valueShOut kOut
            bfOut  = valueOut weakenId
            env'   = weakenBEnv (kOut .> kShOut .> kIn .> kShIn) env
            argF   = ArgFun $ desugarFun env' f
            argIn  = ArgArray In  (ArrayR shrIn  tp) (valueShIn (kOut .> kShOut .> kIn)) (valueIn (kOut .> kShOut))
            argOut = ArgArray Out (ArrayR shrOut tp) shOut bfOut
          in
            alet (LeftHandSidePair lhsShIn lhsIn) (travA a)
              $ alet (mapLeftHandSide GroundRscalar lhsShOut) (Compute $ desugarExp (weakenBEnv (kIn .> kShIn) env) shExp)
              $ aletUnique lhsOut (desugarAlloc (ArrayR shrOut tp) (valueShOut weakenId))
              $ alet (LeftHandSideWildcard TupRunit) (mkBackpermute argF argIn argOut)
              $ Return (shOut `TupRpair` bfOut)

      -- Zip (or a combination of unzip & zip)
      Named.ZipWith _ (Lam elhs1 (Lam elhs2 (Body e))) a1 a2
        | Just vars <- extractExpVars e
        , ArrayR shr t1 <- Named.arrayR a1
        , ArrayR _   t2 <- Named.arrayR a2
        , DeclareVars lhsSh1  kSh1  valueSh1  <- declareVars $ shapeType shr
        , DeclareVars lhsIn1  kIn1  valueIn1  <- declareVars $ buffersR t1
        , DeclareVars lhsSh2  kSh2  valueSh2  <- declareVars $ shapeType shr
        , DeclareVars lhsIn2  kIn2  valueIn2  <- declareVars $ buffersR t2
        , DeclareVars lhsSh   kSh   valueSh   <- declareVars $ shapeType shr
        , DeclareVars lhsOut1 kOut1 valueOut1 <- declareVars $ buffersR t1
        , DeclareVars lhsOut2 kOut2 valueOut2 <- declareVars $ buffersR t2 ->
          let
            lhs1    = LeftHandSidePair (mapLeftHandSide GroundRscalar lhsSh1) lhsIn1
            lhs2    = LeftHandSidePair (mapLeftHandSide GroundRscalar lhsSh2) lhsIn2
            sh1     = mapVars GroundRscalar $ valueSh1 $ kOut2 .> kOut1 .> kSh .> kIn2 .> kSh2 .> kIn1
            sh2     = mapVars GroundRscalar $ valueSh2 $ kOut2 .> kOut1 .> kSh .> kIn2
            sh      = mapVars GroundRscalar $ valueSh (kOut2 .> kOut1)
            argIn1  = ArgArray In  (ArrayR shr t1) sh1 (valueIn1 $ kOut2 .> kOut1 .> kSh .> kIn2 .> kSh2)
            argIn2  = ArgArray In  (ArrayR shr t2) sh2 (valueIn2 $ kOut2 .> kOut1 .> kSh)
            argOut1 = ArgArray Out (ArrayR shr t1) sh  (valueOut1 kOut2)
            argOut2 = ArgArray Out (ArrayR shr t2) sh  (valueOut2 weakenId)
          in
            alet lhs1 (travA a1)
              $ alet lhs2 (desugarOpenAcc (weakenBEnv (kIn1 .> kSh1) env) a2)
              $ alet (mapLeftHandSide GroundRscalar lhsSh) (Compute $ mkIntersect shr (valueSh1 $ kIn2 .> kSh2 .> kIn1) (valueSh2 kIn2))
              $ aletUnique lhsOut1 (desugarAlloc (ArrayR shr t1) (valueSh weakenId))
              $ aletUnique lhsOut2 (desugarAlloc (ArrayR shr t2) (valueSh kOut1))
              $ alet (LeftHandSideWildcard TupRunit) (mkShrink argIn1 argOut1)
              $ alet (LeftHandSideWildcard TupRunit) (mkShrink argIn2 argOut2)
              $ Return (sh `TupRpair` desugarUnzip (valueOut1 kOut2 `TupRpair` valueOut2 weakenId) (LeftHandSidePair elhs1 elhs2) vars)

      Named.ZipWith tp f a1 a2
        | ArrayR shr t1 <- Named.arrayR a1
        , ArrayR _   t2 <- Named.arrayR a2
        , DeclareVars lhsSh1  kSh1  valueSh1  <- declareVars $ shapeType shr
        , DeclareVars lhsIn1  kIn1  valueIn1  <- declareVars $ buffersR t1
        , DeclareVars lhsSh2  kSh2  valueSh2  <- declareVars $ shapeType shr
        , DeclareVars lhsIn2  kIn2  valueIn2  <- declareVars $ buffersR t2
        , DeclareVars lhsSh   kSh   valueSh   <- declareVars $ shapeType shr
        , DeclareVars lhsOut  kOut  valueOut  <- declareVars $ buffersR tp 
        , DeclareVars lhsOut' kOut' valueOut' <- declareVars $ buffersR tp ->
          let
            lhs1    = LeftHandSidePair (mapLeftHandSide GroundRscalar lhsSh1) lhsIn1
            lhs2    = LeftHandSidePair (mapLeftHandSide GroundRscalar lhsSh2) lhsIn2
            sh1     = mapVars GroundRscalar $ valueSh1 $ kOut .> kSh .> kIn2 .> kSh2 .> kIn1
            sh1'    = mapVars GroundRscalar $ valueSh1 $ kOut'       .> kIn2 .> kSh2 .> kIn1
            sh2     = mapVars GroundRscalar $ valueSh2 $ kOut .> kSh .> kIn2
            sh2'    = mapVars GroundRscalar $ valueSh2 $ kOut'       .> kIn2
            sh      = mapVars GroundRscalar $ valueSh kOut
            argF    = ArgFun $ desugarFun (weakenBEnv (kOut .> kSh .> kIn2 .> kSh2 .> kIn1 .> kSh1) env) f
            argF'   = ArgFun $ desugarFun (weakenBEnv (kOut'       .> kIn2 .> kSh2 .> kIn1 .> kSh1) env) f
            argIn1  = ArgArray In  (ArrayR shr t1) sh1  (valueIn1 $ kOut .> kSh .> kIn2 .> kSh2)
            argIn1' = ArgArray In  (ArrayR shr t1) sh1' (valueIn1 $ kOut'       .> kIn2 .> kSh2)
            argIn2  = ArgArray In  (ArrayR shr t2) sh2  (valueIn2 $ kOut .> kSh)
            argIn2' = ArgArray In  (ArrayR shr t2) sh2' (valueIn2 $ kOut')
            argOut  = ArgArray Out (ArrayR shr tp) sh   (valueOut weakenId)
            argOut' = ArgArray Out (ArrayR shr tp) sh1' (valueOut' weakenId)
          in
            alet lhs1 (travA a1)
              $ alet lhs2 (desugarOpenAcc (weakenBEnv (kIn1 .> kSh1) env) a2)
              $ case matchVars (valueSh1 $ kIn2 .> kSh2 .> kIn1) (valueSh2 kIn2) of
                Just Refl ->
                    aletUnique lhsOut' (desugarAlloc (ArrayR shr tp) (valueSh2 kIn2))
                  $ alet LeftHandSideUnit (mkZipWith argF' argIn1' argIn2' argOut')
                  $ Return (sh1' `TupRpair` valueOut' weakenId)
                Nothing ->
                    alet (mapLeftHandSide GroundRscalar lhsSh) (Compute $ mkIntersect shr (valueSh1 $ kIn2 .> kSh2 .> kIn1) (valueSh2 kIn2))
                  $ aletUnique lhsOut (desugarAlloc (ArrayR shr tp) (valueSh weakenId))
                  $ alet LeftHandSideUnit (mkZipWith argF argIn1 argIn2 argOut)
                  $ Return (sh `TupRpair` valueOut weakenId)
      Named.Slice sliceIx a slix
        | ArrayR shr tp <- Named.arrayR a
        , slr <- sliceShapeR sliceIx
        , DeclareVars lhsSh   kSh   valueSh   <- declareVars $ shapeType shr
        , DeclareVars lhsIn   kIn   valueIn   <- declareVars $ buffersR tp
        , DeclareVars lhsSlix kSlix valueSlix <- declareVars $ sliceEltR sliceIx
        , DeclareVars lhsSl   kSl   valueSl   <- declareVars $ shapeType slr
        , DeclareVars lhsOut  kOut  valueOut  <- declareVars $ buffersR tp ->
          let
            lhs     = LeftHandSidePair (mapLeftHandSide GroundRscalar lhsSh) lhsIn
            slix'   = desugarExp (weakenBEnv (kIn .> kSh) env) slix
            sh      = mapVars GroundRscalar $ valueSh $ kOut .> kSl .> kSlix .> kIn
            sl      = mapVars GroundRscalar $ valueSl kOut
            argSlix = ArgVar $ valueSlix $ kOut .> kSl
            argIn   = ArgArray In  (ArrayR shr tp) sh (valueIn $ kOut .> kSl .> kSlix)
            argOut  = ArgArray Out (ArrayR slr tp) sl (valueOut weakenId)
          in
            alet lhs (travA a)
              $ alet (mapLeftHandSide GroundRscalar lhsSlix) (Compute slix')
              $ alet (mapLeftHandSide GroundRscalar lhsSl)   (Compute $ IndexSlice sliceIx (paramsIn' $ valueSlix weakenId) (paramsIn' $ valueSh $ kSlix .> kIn))
              $ aletUnique lhsOut (desugarAlloc (ArrayR slr tp) (valueSl weakenId))
              $ alet (LeftHandSideWildcard TupRunit) (mkSlice sliceIx argSlix argIn argOut)
              $ Return (sl `TupRpair` valueOut weakenId)

      Named.Replicate sliceIx slix a
        | ArrayR slr tp <- Named.arrayR a
        , shr <- sliceDomainR sliceIx
        , DeclareVars lhsSl   kSl   valueSl   <- declareVars $ shapeType slr
        , DeclareVars lhsIn   kIn   valueIn   <- declareVars $ buffersR tp
        , DeclareVars lhsSlix kSlix valueSlix <- declareVars $ sliceEltR sliceIx
        , DeclareVars lhsSh   kSh   valueSh   <- declareVars $ shapeType shr
        , DeclareVars lhsOut  kOut  valueOut  <- declareVars $ buffersR tp ->
          let
            lhs     = LeftHandSidePair (mapLeftHandSide GroundRscalar lhsSl) lhsIn
            slix'   = desugarExp (weakenBEnv (kIn .> kSl) env) slix
            sl      = mapVars GroundRscalar $ valueSl $ kOut .> kSh .> kSlix .> kIn
            sh      = mapVars GroundRscalar $ valueSh kOut
            argSlix = ArgVar $ valueSlix $ kOut .> kSh
            argIn   = ArgArray In  (ArrayR slr tp) sl (valueIn $ kOut .> kSh .> kSlix)
            argOut  = ArgArray Out (ArrayR shr tp) sh (valueOut weakenId)
          in
            alet lhs (travA a)
              $ alet (mapLeftHandSide GroundRscalar lhsSlix) (Compute slix')
              $ alet (mapLeftHandSide GroundRscalar lhsSh)   (Compute $ IndexFull sliceIx (paramsIn' $ valueSlix weakenId) (paramsIn' $ valueSl $ kSlix .> kIn))
              $ aletUnique lhsOut (desugarAlloc (ArrayR shr tp) (valueSh weakenId))
              $ alet (LeftHandSideWildcard TupRunit) (mkReplicate sliceIx argSlix argIn argOut)
              $ Return (sh `TupRpair` valueOut weakenId)

      Named.Fold f def a
        | ArrayR (shapeInit -> shr) tp <- Named.arrayR a
        , DeclareVars lhsSh  kSh  valueSh  <- declareVars $ shapeType $ ShapeRsnoc shr
        , DeclareVars lhsIn  kIn  valueIn  <- declareVars $ buffersR tp
        , DeclareVars lhsOut kOut valueOut <- declareVars $ buffersR tp ->
          let
            shIn   = mapVars GroundRscalar $ valueSh (kOut .> kIn)
            shOut' = case valueSh kIn of
              TupRpair sh _ -> sh
              TupRsingle _  -> error "Impossible pair"
            shOut  = case shIn of
              TupRpair sh _ -> sh
              TupRsingle _  -> error "Impossible pair"
            k = kOut .> kIn .> kSh
            argF   = ArgFun $ desugarFun (weakenBEnv k env) f
            argDef = fmap (ArgExp . desugarExp (weakenBEnv k env)) def
            argIn  = ArgArray In (ArrayR (ShapeRsnoc shr) tp) shIn (valueIn kOut)
            argOut = ArgArray Out (ArrayR shr tp) shOut (valueOut weakenId)
          in
            alet (LeftHandSidePair (mapLeftHandSide GroundRscalar lhsSh) lhsIn) (travA a)
              $ aletUnique lhsOut (desugarAlloc (ArrayR shr tp) shOut')
              $ alet (LeftHandSideWildcard TupRunit) (mkFold argF argDef argIn argOut)
              $ Return (shOut `TupRpair` valueOut weakenId)

      Named.FoldSeg (i :: IntegralType i) f def a segments
        | ArrayR shr tp <- Named.arrayR a
        , Refl <- reprIsSingle @ScalarType @i @Buffer (SingleScalarType $ NumSingleType $ IntegralNumType i)
        , DeclareVars lhsSh  kSh  valueSh  <- declareVars $ shapeType shr
        , DeclareVars lhsIn  kIn  valueIn  <- declareVars $ buffersR tp
        , DeclareVars lhsOut kOut valueOut <- declareVars $ buffersR tp ->
          let
            itp = SingleScalarType $ NumSingleType $ IntegralNumType i
            lhsSeg
              = LeftHandSidePair
                  -- DIM1 = ((), Int)
                  (LeftHandSidePair (LeftHandSideWildcard TupRunit) (LeftHandSideSingle $ GroundRscalar scalarTypeInt))
                  -- Buffer of integral type i
                  $ LeftHandSideSingle $ GroundRbuffer itp
            kSeg = weakenSucc $ weakenSucc weakenId

            sh  = mapVars GroundRscalar $ valueSh (kSeg .> kOut .> kIn)
            sh' = valueSh kIn

            k = kSeg .> kOut .> kIn .> kSh
            argF   = ArgFun $ desugarFun (weakenBEnv k env) f
            argDef = fmap (ArgExp . desugarExp (weakenBEnv k env)) def
            argIn  = ArgArray In (ArrayR shr tp) sh (valueIn $ kSeg .> kOut)
            argOut = ArgArray Out (ArrayR shr tp) sh (valueOut $ kSeg)
            argSeg = ArgArray In  (ArrayR dim1 $ TupRsingle itp) (TupRpair TupRunit $ TupRsingle $ Var (GroundRscalar scalarTypeInt) $ SuccIdx ZeroIdx) (TupRsingle $ Var (GroundRbuffer itp) ZeroIdx)
          in
            alet (LeftHandSidePair (mapLeftHandSide GroundRscalar lhsSh) lhsIn) (travA a)
              $ aletUnique lhsOut (desugarAlloc (ArrayR shr tp) sh')
              $ alet lhsSeg (desugarOpenAcc (weakenBEnv (kOut .> kIn .> kSh) env) segments)
              $ alet (LeftHandSideWildcard TupRunit) (mkFoldSeg i argF argDef argIn argSeg argOut)
              $ Return (sh `TupRpair` valueOut kSeg)

      -- scan1
      Named.Scan dir f Nothing a
        | ArrayR shr tp <- Named.arrayR a
        , DeclareVars lhsSh  kSh  valueSh  <- declareVars $ shapeType shr
        , DeclareVars lhsIn  kIn  valueIn  <- declareVars $ buffersR tp
        , DeclareVars lhsOut kOut valueOut <- declareVars $ buffersR tp ->
          let
            sh   = mapVars GroundRscalar $ valueSh (kOut .> kIn)
            k = kOut .> kIn .> kSh
            argF = ArgFun $ desugarFun (weakenBEnv k env) f
            argIn  = ArgArray In (ArrayR shr tp) sh (valueIn kOut)
            argOut = ArgArray Out (ArrayR shr tp) sh (valueOut weakenId)
          in
            alet (LeftHandSidePair (mapLeftHandSide GroundRscalar lhsSh) lhsIn) (travA a)
              $ aletUnique lhsOut (desugarAlloc (ArrayR shr tp) $ valueSh kIn)
              $ alet (LeftHandSideWildcard TupRunit) (mkScan dir argF Nothing argIn argOut)
              $ Return (sh `TupRpair` valueOut weakenId)

      Named.Scan dir f (Just def) a
        | ArrayR shr tp <- Named.arrayR a
        , DeclareVars lhsShIn  kShIn  valueShIn  <- declareVars $ shapeType shr
        , DeclareVars lhsIn    kIn    valueIn    <- declareVars $ buffersR tp
        -- The rightmost dimension is incremented by 1. This variable only contains the rightmost dimension
        , DeclareVars lhsShOut kShOut valueShOut <- declareVars $ TupRsingle $ scalarTypeInt
        , DeclareVars lhsOut   kOut   valueOut   <- declareVars $ buffersR tp ->
          let
            shIn  = mapVars GroundRscalar $ valueShIn (kOut .> kShOut .> kIn)
            shIn1 = case valueShIn kIn of
              TupRpair _ (TupRsingle sh) -> sh
              _ -> error "Impossible pair"
            shOut = case shIn of
              TupRpair sh _ -> TupRpair sh $ mapVars GroundRscalar $ valueShOut kOut
              _ -> error "Impossible pair"
            shOut' = case valueShIn (kShOut .> kIn) of
              TupRpair sh _ -> TupRpair sh $ valueShOut weakenId
              _ -> error "Impossible pair"

            k = kOut .> kShOut .> kIn .> kShIn

            argF   = ArgFun $ desugarFun (weakenBEnv k env) f
            argDef = Just $ ArgExp $ desugarExp (weakenBEnv k env) def
            argIn  = ArgArray In (ArrayR shr tp)  shIn  (valueIn $ kOut .> kShOut)
            argOut = ArgArray Out (ArrayR shr tp) shOut (valueOut weakenId)
          in
            alet (LeftHandSidePair (mapLeftHandSide GroundRscalar lhsShIn) lhsIn) (travA a)
              $ alet (mapLeftHandSide GroundRscalar lhsShOut) (Compute $ mkBinary (PrimAdd numType) (ArrayInstr (Parameter shIn1) Nil) (mkConstant (TupRsingle scalarTypeInt) 1))
              $ aletUnique lhsOut (desugarAlloc (ArrayR shr tp) $ shOut')
              $ alet (LeftHandSideWildcard TupRunit) (mkScan dir argF argDef argIn argOut)
              $ Return (shOut `TupRpair` valueOut weakenId)

      Named.Scan' dir f def a
        | ArrayR (shapeInit -> shr) tp <- Named.arrayR a
        , DeclareVars lhsSh kSh valueSh <- declareVars $ shapeType $ ShapeRsnoc shr
        , DeclareVars lhsIn kIn valueIn <- declareVars $ buffersR tp
        -- The prefix values
        , DeclareVars lhsOut1 kOut1 valueOut1 <- declareVars $ buffersR tp
        -- The final reduced value
        , DeclareVars lhsOut2 kOut2 valueOut2 <- declareVars $ buffersR tp ->
          let
            sh = mapVars GroundRscalar $ valueSh (kOut2 .> kOut1 .> kIn)

            shOut1' = valueSh kIn
            shOut2' = case valueSh (kOut1 .> kIn) of
              TupRpair sh' _ -> sh'
              _ -> error "Impossible pair"
            shOut2 = case sh of
              TupRpair sh' _ -> sh'
              _ -> error "Impossible pair"

            k = kOut2 .> kOut1 .> kIn .> kSh

            argF = ArgFun $ desugarFun (weakenBEnv k env) f
            argDef = ArgExp $ desugarExp (weakenBEnv k env) def
            argIn = ArgArray In (ArrayR (ShapeRsnoc shr) tp) sh (valueIn $ kOut2 .> kOut1)
            argOut1 = ArgArray Out (ArrayR (ShapeRsnoc shr) tp) sh (valueOut1 kOut2)
            argOut2 = ArgArray Out (ArrayR shr tp) shOut2 (valueOut2 weakenId)
          in
            alet (LeftHandSidePair (mapLeftHandSide GroundRscalar lhsSh) lhsIn) (travA a)
              $ aletUnique lhsOut1 (desugarAlloc (ArrayR (ShapeRsnoc shr) tp) $ shOut1')
              $ aletUnique lhsOut2 (desugarAlloc (ArrayR shr tp) $ shOut2')
              $ alet (LeftHandSideWildcard TupRunit) (mkScan' dir argF argDef argIn argOut1 argOut2)
              $ Return (TupRpair sh (valueOut1 kOut2) `TupRpair` TupRpair shOut2 (valueOut2 weakenId))

      Named.Stencil sr tp f boundary a
        | shr <- stencilShapeR sr
        , oldTp <- stencilEltR sr
        , DeclareVars lhsSh  kSh  valueSh  <- declareVars $ shapeType shr
        , DeclareVars lhsIn  kIn  valueIn  <- declareVars $ buffersR oldTp
        , DeclareVars lhsOut kOut valueOut <- declareVars $ buffersR tp ->
          let
            lhs       = LeftHandSidePair (mapLeftHandSide GroundRscalar lhsSh) lhsIn
            sh        = mapVars GroundRscalar $ valueSh (kOut .> kIn)
            env'      = weakenBEnv (kOut .> kIn .> kSh) env
            argF      = ArgFun $ desugarFun env' f
            argIn     = ArgArray In (ArrayR shr oldTp) sh (valueIn kOut)
            argOut    = ArgArray Out (ArrayR shr tp)   sh (valueOut weakenId)
            boundary' = desugarBoundary env' boundary
          in
            alet lhs (travA a)
              $ aletUnique lhsOut (desugarAlloc (ArrayR shr tp) (valueSh kIn))
              $ alet (LeftHandSideWildcard TupRunit) (mkStencil sr argF boundary' argIn argOut)
              $ Return (sh `TupRpair` valueOut weakenId)

      Named.Stencil2 sr1 sr2 tp3 f b1 a1 b2 a2
        | shr <- stencilShapeR sr1
        , tp1 <- stencilEltR sr1
        , tp2 <- stencilEltR sr2
        , DeclareVars lhsSh1 kSh1 valueSh1 <- declareVars $ shapeType shr
        , DeclareVars lhsIn1 kIn1 valueIn1 <- declareVars $ buffersR tp1
        , DeclareVars lhsSh2 kSh2 valueSh2 <- declareVars $ shapeType shr
        , DeclareVars lhsIn2 kIn2 valueIn2 <- declareVars $ buffersR tp2
        , DeclareVars lhsSh  kSh  valueSh  <- declareVars $ shapeType shr
        , DeclareVars lhsOut kOut valueOut <- declareVars $ buffersR tp3 ->
          let
            lhs1      = LeftHandSidePair (mapLeftHandSide GroundRscalar lhsSh1) lhsIn1
            lhs2      = LeftHandSidePair (mapLeftHandSide GroundRscalar lhsSh2) lhsIn2
            sh        = mapVars GroundRscalar $ valueSh kOut
            sh1       = mapVars GroundRscalar $ valueSh1 (kOut .> kSh .> kIn2 .> kSh2 .> kIn1)
            sh2       = mapVars GroundRscalar $ valueSh2 (kOut .> kSh .> kIn2)
            env'      = weakenBEnv (kOut .> kSh .> kIn2 .> kSh2 .> kIn1 .> kSh1) env
            argF      = ArgFun $ desugarFun env' f
            b1'       = desugarBoundary env' b1
            b2'       = desugarBoundary env' b2
            argIn1    = ArgArray In (ArrayR shr tp1) sh1 (valueIn1 $ kOut .> kSh .> kIn2 .> kSh2)
            argIn2    = ArgArray In (ArrayR shr tp2) sh2 (valueIn2 $ kOut .> kSh)
            argOut    = ArgArray Out (ArrayR shr tp3) sh (valueOut weakenId)
          in
            alet lhs1 (travA a1)
              $ alet lhs2 (desugarOpenAcc (weakenBEnv (kIn1 .> kSh1) env) a2)
              $ alet (mapLeftHandSide GroundRscalar lhsSh) (Compute $ mkIntersect shr (valueSh1 $ kIn2 .> kSh2 .> kIn1) (valueSh2 kIn2))
              $ aletUnique lhsOut (desugarAlloc (ArrayR shr tp3) (valueSh weakenId))
              $ alet (LeftHandSideWildcard TupRunit) (mkStencil2 sr1 sr2 argF b1' argIn1 b2' argIn2 argOut)
              $ Return (sh `TupRpair` valueOut weakenId)
      Named.Atrace _ _ _ -> error "implement me"

desugarAlloc :: forall benv op sh a. ArrayR (Array sh a) -> ExpVars benv sh -> OperationAcc op benv (Buffers a)
desugarAlloc (ArrayR _   TupRunit        ) _  = Return TupRunit
desugarAlloc (ArrayR shr (TupRpair t1 t2)) sh = desugarAlloc (ArrayR shr t1) sh `pairUnique` desugarAlloc (ArrayR shr t2) sh
desugarAlloc (ArrayR shr (TupRsingle tp) ) sh
  | Refl <- reprIsSingle @ScalarType @a @Buffer tp = Alloc shr tp sh

desugarBoundary :: HasCallStack
                => BEnv benv aenv
                -> Named.Boundary aenv (Array sh e)
                -> Boundary benv (Array sh e)
desugarBoundary _   Named.Clamp        = Clamp
desugarBoundary _   Named.Mirror       = Mirror
desugarBoundary _   Named.Wrap         = Wrap
desugarBoundary _   (Named.Constant e) = Constant e
desugarBoundary env (Named.Function f) = Function $ desugarFun env f

desugarOpenAfun :: (HasCallStack, DesugarAcc op)
                => BEnv benv aenv
                -> Named.OpenAfun aenv a
                -> OperationAfun op benv (DesugaredAfun a)
desugarOpenAfun env (Named.Abody a) = case Named.arraysR a of
  -- We must pattern match on the arrays representation of the body
  -- to inform the type checker that 'a' is not a function, and thus
  -- that 'DesugaredAfun a' is equal to 'DesugaredArrays a'
  TupRsingle ArrayR{} -> Abody $ desugarOpenAcc env a
  TupRunit            -> Abody $ desugarOpenAcc env a
  TupRpair _ _        -> Abody $ desugarOpenAcc env a
desugarOpenAfun env (Named.Alam lhs f)
  | DesugaredLHS env' lhs' <- desugarLHS env lhs = Alam lhs' $ desugarOpenAfun env' f

data DesugaredLHS b aenv' benv where
  DesugaredLHS :: BEnv benv' aenv' -> GLeftHandSide b benv benv' -> DesugaredLHS b aenv' benv

desugarLHS :: BEnv benv aenv -> Named.ALeftHandSide a aenv aenv' -> DesugaredLHS (DesugaredArrays a) aenv' benv
desugarLHS env (LeftHandSideWildcard repr)      = DesugaredLHS env $ LeftHandSideWildcard $ desugarArraysR repr
desugarLHS env (LeftHandSidePair l1 l2)
  | DesugaredLHS env1 l1' <- desugarLHS env  l1
  , DesugaredLHS env2 l2' <- desugarLHS env1 l2 = DesugaredLHS env2 $ LeftHandSidePair l1' l2'
desugarLHS env (LeftHandSideSingle (ArrayR shr tp))
  | DeclareVars lhsSh kSh valueSh <- declareVars $ mapTupR GroundRscalar $ shapeType shr
  , DeclareVars lhsBf kBf valueBf <- declareVars $ buffersR tp
  = DesugaredLHS (mapEnv (weakenArrayDescriptor $ kBf .> kSh) env `Push` ArrayDescriptor shr (valueSh kBf) (valueBf weakenId)) $ LeftHandSidePair lhsSh lhsBf

desugarExp :: HasCallStack
           => BEnv benv aenv
           -> Named.OpenExp env aenv e
           -> OpenExp env benv e
desugarExp env = rebuildArrayInstr (desugarArrayInstr env)

desugarFun :: HasCallStack
           => BEnv benv aenv
           -> Named.Fun aenv e
           -> Fun benv e
desugarFun env = rebuildArrayInstr (desugarArrayInstr env)

desugarArrayInstr :: BEnv benv aenv -> Named.ArrayInstr aenv (s -> t) -> OpenExp env benv s -> OpenExp env benv t
desugarArrayInstr env (Named.Shape (Var (ArrayR shr _) array)) _
  | ArrayDescriptor _ sh _ <- prj' array env = paramsIn (shapeType shr) sh
desugarArrayInstr env (Named.LinearIndex (Var (ArrayR _ tp) array)) ix
  = Let lhs ix $ linearIndex tp buffers $ Var int ZeroIdx
  where
    ArrayDescriptor _ _ buffers = prj' array env
    int = SingleScalarType $ NumSingleType $ IntegralNumType TypeInt
    lhs = LeftHandSideSingle int
desugarArrayInstr env (Named.Index (Var (ArrayR shr tp) array)) ix
  = Let lhs (ToIndex shr sh' ix) $ linearIndex tp buffers $ Var int ZeroIdx
  where
    ArrayDescriptor _ sh buffers = prj' array env
    sh' = paramsIn (shapeType shr) sh
    int = SingleScalarType $ NumSingleType $ IntegralNumType TypeInt
    lhs = LeftHandSideSingle int

weakenBEnv :: forall benv benv' aenv. benv :> benv' -> BEnv benv aenv -> BEnv benv' aenv
weakenBEnv k = mapEnv f
  where
    f :: ArrayDescriptor benv a -> ArrayDescriptor benv' a
    f (ArrayDescriptor shr sh buffers) = ArrayDescriptor shr (weakenVars k sh) (weakenVars k buffers)

desugarUnzip :: GroundVars benv (Buffers s) -> ELeftHandSide s () env -> ExpVars env t -> GroundVars benv (Buffers t)
desugarUnzip _       _   TupRunit                 = TupRunit
desugarUnzip buffers lhs (TupRpair v1 v2)         = desugarUnzip buffers lhs v1 `TupRpair` desugarUnzip buffers lhs v2
desugarUnzip buffers lhs (TupRsingle (Var _ idx)) = case lookupVar buffers lhs idx of
    Right u -> u
    Left (VoidIdx void) -> void
    -- Left branch is unreachable, as `Idx () y` is an empty type
  where
    lookupVar :: GroundVars benv (Buffers x) -> ELeftHandSide x env1 env2 -> Idx env2 y -> Either (Idx env1 y) (GroundVars benv (Buffers y))
    lookupVar _                (LeftHandSideWildcard _) ix = Left ix
    lookupVar buffers'         (LeftHandSideSingle _)   ix = case ix of
      ZeroIdx     -> Right buffers'
      SuccIdx ix' -> Left ix'
    lookupVar (TupRpair b1 b2) (LeftHandSidePair l1 l2) ix = case lookupVar b2 l2 ix of
      Right u  -> Right u
      Left ix' -> lookupVar b1 l1 ix'
    lookupVar _ _ _ = error "Impossible pair"

-- Utilities
--

index :: ArrayR (Array sh e) -> GroundVars benv sh -> GroundVars benv (Buffers e) -> OpenExp env benv sh -> OpenExp env benv e
index (ArrayR shr tp) sh buffers ix = Let lhs (ToIndex shr (paramsIn (shapeType shr) sh) ix) $ linearIndex tp buffers $ Var int ZeroIdx
  where
    int = SingleScalarType $ NumSingleType $ IntegralNumType TypeInt
    lhs = LeftHandSideSingle int

indexFunction :: ArrayR (Array sh e) -> GroundVars benv sh -> GroundVars benv (Buffers e) -> OpenFun env benv (sh -> e)
indexFunction repr@(ArrayR shr _) sh buffers
  | DeclareVars lhs _ value <- declareVars $ shapeType shr
    = Lam lhs $ Body $ index repr sh buffers (expVars $ value weakenId)

linearIndex :: forall e benv env. HasCallStack => TypeR e -> GroundVars benv (Buffers e) -> ExpVar env Int -> OpenExp env benv e
linearIndex TupRunit         TupRunit         _   = Nil
linearIndex (TupRpair t1 t2) (TupRpair b1 b2) ix  = linearIndex t1 b1 ix `Pair` linearIndex t2 b2 ix
linearIndex (TupRsingle t)   (TupRsingle var@(Var (GroundRbuffer _) _)) ix
  | Refl <- reprIsSingle @ScalarType @e @Buffer t = ArrayInstr (Index var) (Evar ix)
linearIndex _                _                _   = internalError "Tuple mismatch"

extend :: SliceIndex slix sl co sh
       -> Arg env (Var' slix)
       -> Fun env (sh -> sl)
extend sliceIx (ArgVar slix)
  | DeclareVars lhs _ value <- declareVars $ shapeType $ sliceDomainR sliceIx
  = Lam lhs $ Body $ IndexSlice sliceIx (paramsIn' slix) $ expVars $ value weakenId

restrict :: SliceIndex slix sl co sh
         -> Arg env (Var' slix)
         -> Fun env (sl -> sh)
restrict sliceIx (ArgVar slix)
  | DeclareVars lhs _ value <- declareVars $ shapeType $ sliceShapeR sliceIx
  = Lam lhs $ Body $ IndexFull sliceIx (paramsIn' slix) $ expVars $ value weakenId

-- Utility function to reduce the dimension by one. Defined as a function,
-- as doing pattern matching in the guards in desugarOpenAcc will cause
-- a false warning "pattern matches are non-exhaustive".
shapeInit :: ShapeR (sh, Int) -> ShapeR sh
shapeInit (ShapeRsnoc shr) = shr

desugarUse :: ArrayR (Array sh e) -> Array sh e -> OperationAcc op benv (DesugaredArrays (Array sh e))
desugarUse (ArrayR shr tp) (Array sh buffers) = Compute (mkConstant (shapeType shr) sh) `pair` desugarBuffers tp (size shr sh) buffers

desugarBuffers :: forall e op benv. TypeR e -> Int -> Buffers e -> OperationAcc op benv (Buffers e)
desugarBuffers TupRunit         _ ()       = Return TupRunit
desugarBuffers (TupRpair t1 t2) n (b1, b2) = desugarBuffers t1 n b1 `pair` desugarBuffers t2 n b2
desugarBuffers (TupRsingle tp)  n buffer
  | Refl <- reprIsSingle @ScalarType @e @Buffer tp = Use tp n buffer

desugarBoundaryToFunction :: forall benv sh e. Boundary benv (Array sh e) -> Arg benv (In sh e) -> Fun benv (sh -> e)
desugarBoundaryToFunction boundary (ArgArray _ repr@(ArrayR shr tp) sh buffers) = case boundary of
  Function f -> f
  Constant e -> Lam (LeftHandSideWildcard $ shapeType shr) $ Body $ mkConstant tp e
  Clamp      -> reindex clamp
  Mirror     -> reindex mirror
  Wrap       -> reindex wrap
  where

    -- Note: the expressions passed as argument may be duplicated in the resulting code.
    -- This doesn't explode the code size as they are always an Evar or a Parameter.
    --
    clamp, mirror, wrap :: OpenExp env benv Int -> OpenExp env benv Int -> OpenExp env benv Int
    -- clamp ix sz = max(0, min(ix, sz - 1))
    clamp ix sz = mkBinary (PrimMax singleType) (Const scalarTypeInt 0) $ mkBinary (PrimMin singleType) ix $ sub sz $ Const scalarTypeInt 0

    -- if ix < 0 then -ix
    mirror ix sz = Cond (mkBinary (PrimLt singleType) ix (Const scalarTypeInt 0)) (PrimApp (PrimNeg numType) ix)
                 -- else if ix >= sz then sz - ((ix - sz) + 2)
                 $ Cond (mkBinary (PrimGtEq singleType) ix sz) (sub sz (add (sub ix sz) $ Const scalarTypeInt 2))
                 -- else ix
                 $ ix

    -- if ix < 0 then sz + ix
    wrap ix sz = Cond (mkBinary (PrimLt singleType) ix (Const scalarTypeInt 0)) (add sz ix)
                 -- else if ix >= sz then ix - sz
                 $ Cond (mkBinary (PrimGtEq singleType) ix sz) (sub ix sz)
                 -- else ix
                 $ ix

    add = mkBinary (PrimAdd numType)
    sub = mkBinary (PrimSub numType)

    reindex :: (forall env'. OpenExp env' benv Int -> OpenExp env' benv Int -> OpenExp env' benv Int) -> Fun benv (sh -> e)
    reindex f
      | DeclareVars lhs _ value <- declareVars $ shapeType shr
        = Lam lhs $ Body $ index repr sh buffers $ getIndex f shr (value weakenId) sh

    getIndex :: (OpenExp env benv Int -> OpenExp env benv Int -> OpenExp env benv Int) -> ShapeR sh' -> ExpVars env sh' -> GroundVars benv sh' -> OpenExp env benv sh'
    getIndex _ ShapeRz           _                              _                              = Nil
    getIndex f (ShapeRsnoc shr') (TupRpair ixs (TupRsingle ix)) (TupRpair szs (TupRsingle sz)) = getIndex f shr' ixs szs `Pair` f (Evar ix) (paramIn scalarTypeInt sz)
    getIndex _ _                 _                              _                              = internalError "Illegal tuple for shape"

desugarStencilFun :: StencilR sh e stencil -> TypeR e' -> Fun benv (stencil -> e') -> Maybe (Boundary benv (Array sh e)) -> Arg benv (In sh e) -> Fun benv (sh -> e')
desugarStencilFun sr _ f boundary array = f `compose` stencilAccess sr boundary array

desugarStencil2Fun :: StencilR sh a stencil1 -> StencilR sh b stencil2 -> TypeR c -> Fun benv (stencil1 -> stencil2 -> c) -> Maybe (Boundary benv (Array sh a)) -> Arg benv (In sh a) -> Maybe (Boundary benv (Array sh b)) -> Arg benv (In sh b) -> Fun benv (sh -> c)
desugarStencil2Fun sr1 sr2 tp f boundary1 array1@(ArgArray _ (ArrayR shr _) _ _) boundary2 array2
  | DeclareVars lhs _ value <- declareVars $ shapeType shr
  , vars <- expVars $ value weakenId
    = Lam lhs $ Body $ apply2 tp f (apply1 (stencilR sr1) (stencilAccess sr1 boundary1 array1) vars)
                                   (apply1 (stencilR sr2) (stencilAccess sr2 boundary2 array2) vars)

stencilAccess :: forall sh e stencil benv. StencilR sh e stencil -> Maybe (Boundary benv (Array sh e)) -> Arg benv (In sh e) -> Fun benv (sh -> stencil)
stencilAccess sr boundary array@(ArgArray _ repr@(ArrayR shr tp) sh buffers)
  | DeclareVars lhs _ value <- declareVars $ shapeType shr = Lam lhs $ Body $ stencilAccess' shr sr readFunction (value weakenId)
  where
    readFunction :: env :> env' -> ExpVars env' sh -> OpenExp env' benv e
    readFunction _ = readFunction' . expVars

    readFunction' :: OpenExp env' benv sh -> OpenExp env' benv e
    readFunction' = apply1 tp $ case boundary of
      Just b  -> desugarBoundaryToFunction b array
      Nothing -> indexFunction repr sh buffers

stencilAccess' :: forall env benv sh e stencil. ShapeR sh -> StencilR sh e stencil -> (forall env'. env :> env' -> ExpVars env' sh -> OpenExp env' benv e) -> ExpVars env sh -> OpenExp env benv stencil
stencilAccess' shr sr rf ix = case sr of
  -- Base cases, nothing interesting to do here since we know the lower
  -- dimension is Z.
  --
  StencilRunit3 _ -> Nil `Pair` rf' (-1)
                         `Pair` center
                         `Pair` rf'   1
  StencilRunit5 _ -> Nil `Pair` rf' (-2)
                         `Pair` rf' (-1)
                         `Pair` center
                         `Pair` rf'   1
                         `Pair` rf'   2
  StencilRunit7 _ -> Nil `Pair` rf' (-3)
                         `Pair` rf' (-2)
                         `Pair` rf' (-1)
                         `Pair` center
                         `Pair` rf'   1
                         `Pair` rf'   2
                         `Pair` rf'   3
  StencilRunit9 _ -> Nil `Pair` rf' (-4)
                         `Pair` rf' (-3)
                         `Pair` rf' (-2)
                         `Pair` rf' (-1)
                         `Pair` center
                         `Pair` rf'   1
                         `Pair` rf'   2
                         `Pair` rf'   3
                         `Pair` rf'   4

  -- Recursive cases. Note that because the stencil pattern is defined with
  -- a cons ordering, whereas shapes (indices) are defined as a snoc list,
  -- when we recurse on the stencil structure we must manipulate the
  -- _left-most_ index component
  --
  StencilRtup3 s1 s2 s3 ->
    Nil `Pair` go s1 (-1)
        `Pair` go s2 0
        `Pair` go s3 1

  StencilRtup5 s1 s2 s3 s4 s5 ->
    Nil `Pair` go s1 (-2)
        `Pair` go s2 (-1)
        `Pair` go s3 0
        `Pair` go s4 1
        `Pair` go s5 2

  StencilRtup7 s1 s2 s3 s4 s5 s6 s7 ->
    Nil `Pair` go s1 (-3)
        `Pair` go s2 (-2)
        `Pair` go s3 (-1)
        `Pair` go s4 0
        `Pair` go s5 1
        `Pair` go s6 2
        `Pair` go s7 3

  StencilRtup9 s1 s2 s3 s4 s5 s6 s7 s8 s9 ->
    Nil `Pair` go s1 (-4)
        `Pair` go s2 (-3)
        `Pair` go s3 (-2)
        `Pair` go s4 (-1)
        `Pair` go s5 0
        `Pair` go s6 1
        `Pair` go s7 2
        `Pair` go s8 3
        `Pair` go s9 4
  where
    center :: sh ~ DIM1 => OpenExp env benv e
    center = rf weakenId ix

    -- read function for 1 dimensional cases
    rf' :: sh ~ DIM1 => Int -> OpenExp env benv e
    rf' d
      | TupRpair _ (TupRsingle i) <- ix = Let (LeftHandSideSingle scalarTypeInt) (mkBinary (PrimAdd numType) (Evar i) $ Const scalarTypeInt d)
                                        $ rf (weakenSucc weakenId) $ TupRpair TupRunit $ TupRsingle $ Var scalarTypeInt ZeroIdx
    rf' _ = internalError "Shape tuple mismatch"

    go :: forall sh' stencil'. sh ~ (sh', Int) => StencilR sh' e stencil' -> Int -> OpenExp env benv stencil'
    go sr' d = stencilAccess' shr' sr' rf'' ix'
      where
        ShapeRsnoc shr' = shr
        (i, ix') = uncons shr' ix

        rf'' :: (env :> env') -> ExpVars env' sh' -> OpenExp env' benv e
        rf'' k ds
          | d == 0 = rf k (cons shr' (weakenE k i) ds)
          | otherwise = Let (LeftHandSideSingle scalarTypeInt) (mkBinary (PrimAdd numType) (Evar $ weakenE k i) $ Const scalarTypeInt d)
                      $ rf (weakenSucc' k) $ cons shr' (Var scalarTypeInt ZeroIdx) $ weakenVars (weakenSucc weakenId) ds

-- Add a _left-most_ dimension to a shape
--
cons :: ShapeR sh -> ExpVar env Int -> ExpVars env sh -> ExpVars env (sh, Int)
cons ShapeRz          ix _                = TupRpair TupRunit $ TupRsingle ix
cons (ShapeRsnoc shr) ix (TupRpair sh sz) = TupRpair (cons shr ix sh) sz
cons _                _  _                = internalError "Illegal shape tuple"


-- Remove the _left-most_ index to a shape, and return the remainder
--
uncons :: ShapeR sh -> ExpVars env (sh, Int) -> (ExpVar env Int, ExpVars env sh)
uncons ShapeRz          (TupRpair _ (TupRsingle v2)) = (v2, TupRunit)
uncons (ShapeRsnoc shr) (TupRpair v1 v3)
  = let (i, v1') = uncons shr v1
    in  (i, TupRpair v1' v3)
uncons _ _ = internalError "Illegal shape tuple"

mkIntersect :: ShapeR sh -> ExpVars benv sh -> ExpVars benv sh -> PreOpenExp (ArrayInstr benv) env sh
mkIntersect shr' x y
  | Just Refl <- matchVars x y = paramsIn' x
  | otherwise = mkIntersect' shr' x y
  where
    mkIntersect' :: ShapeR sh -> ExpVars benv sh -> ExpVars benv sh -> PreOpenExp (ArrayInstr benv) env sh
    mkIntersect' ShapeRz          _                _                = Nil
    mkIntersect' (ShapeRsnoc shr) (TupRpair s1 x1) (TupRpair s2 x2) = mkIntersect' shr s1 s2 `Pair` mkBinary (PrimMin singleType) (paramsIn' x1) (paramsIn' x2)
    mkIntersect' (ShapeRsnoc _)   _                _                = error "Impossible pair"

mkDefaultFoldSequential :: forall benv op sh e. DesugarAcc op => Arg benv (Fun' (e -> e -> e)) -> Maybe (Arg benv (Exp' e)) -> Arg benv (In (sh, Int) e) -> Arg benv (Out sh e) -> OperationAcc op benv ()
mkDefaultFoldSequential op def argIn = mkGenerate (mkDefaultFoldFunction op def argIn)

mkDefaultFoldFunction :: Arg benv (Fun' (e -> e -> e)) -> Maybe (Arg benv (Exp' e)) -> Arg benv (In (sh, Int) e) -> Arg benv (Fun' (sh -> e))
mkDefaultFoldFunction (ArgFun op) def (ArgArray _ (ArrayR (ShapeRsnoc shr) tp) (sh `TupRpair` n) buffers)
  | DeclareVars lhsIdx _k1 valueIdx <- declareVars $ shapeType shr
  , DeclareVars lhsVal k2 valueVal <- declareVars tp =
    let
      initial = case def of
        Nothing ->
          Pair
            (mkConstant (TupRsingle scalarTypeInt) 1)
            (index (ArrayR (ShapeRsnoc shr) tp) (sh `TupRpair` n) buffers (expVars (valueIdx weakenId) `Pair` mkConstant (TupRsingle scalarTypeInt) 0))
        Just (ArgExp d) ->
          Pair
            (mkConstant (TupRsingle scalarTypeInt) 0)
            (weakenE weakenEmpty d)

      lhs = LeftHandSidePair (LeftHandSideSingle scalarTypeInt) lhsVal
      -- \(idx, accum)
      step = Lam lhs $ Body $ Pair
        -- (idx + 1
        (mkBinary (PrimAdd numType) (Evar $ Var scalarTypeInt $ k2 >:> ZeroIdx) (mkConstant (TupRsingle scalarTypeInt) 1))
        -- , op accum (input !! idx)
        $ apply2 tp op (expVars $ valueVal weakenId)
        $ index (ArrayR (ShapeRsnoc shr) tp) (sh `TupRpair` n) buffers
        $ expVars (valueIdx $ weakenSucc k2) `Pair` Evar (Var scalarTypeInt $ k2 >:> ZeroIdx)

      condition =
        Lam (LeftHandSidePair (LeftHandSideSingle scalarTypeInt) (LeftHandSideWildcard tp))
        $ Body $ mkBinary (PrimLt singleType) (Evar $ Var scalarTypeInt ZeroIdx) (paramsIn (TupRsingle scalarType) n)
    in
      ArgFun $ Lam lhsIdx $ Body
        $ Let lhs (While condition step initial)
        $ expVars $ valueVal weakenId
mkDefaultFoldFunction _ _ _ = internalError "Fun impossible"

-- In case of a scan with a default value, prepends the initial value before the other elements
-- The default value is placed as the first value in case of a left-to-right scan, or as the
-- last value for a right-to-left scan.
mkDefaultScanPrepend :: Direction -> Arg benv (Exp' e) -> Arg benv (In (sh, Int) e) -> Fun benv ((sh, Int) -> e)
mkDefaultScanPrepend dir (ArgExp def) (ArgArray _ repr@(ArrayR (ShapeRsnoc shr) _) sh input)
  | DeclareVars lhs k value <- declareVars $ shapeType shr
  = let
      first = case dir of
        LeftToRight -> mkConstant (TupRsingle scalarTypeInt) 0
        RightToLeft -> case sh of
          TupRpair _ n -> paramsIn (TupRsingle scalarTypeInt) n
          _ -> error "Impossible pair"
      x = case dir of
        LeftToRight -> mkBinary (PrimSub numType) (Evar $ Var scalarTypeInt ZeroIdx) (mkConstant (TupRsingle scalarType) 1)
        RightToLeft -> Evar $ Var scalarTypeInt ZeroIdx
    in
      Lam (lhs `LeftHandSidePair` LeftHandSideSingle scalarTypeInt)
        $ Body
        $ Cond (mkBinary (PrimEq singleType) (Evar $ Var scalarTypeInt ZeroIdx) first) (weakenE (weakenSucc' k) def)
        $ index repr sh input
        $ Pair (expVars $ value $ weakenSucc weakenId) x

mkDefaultScanFunction :: Direction -> GroundVar benv Int -> Arg benv (Fun' (e -> e -> e)) -> Arg benv (In (sh, Int) e) -> Fun benv ((sh, Int) -> e)
mkDefaultScanFunction dir inc (ArgFun f) (ArgArray _ repr@(ArrayR (ShapeRsnoc shr) tp) sh input)
  | DeclareVars lhs _ value <- declareVars $ shapeType shr
  = let
      op = case dir of
        LeftToRight -> PrimSub
        RightToLeft -> PrimAdd
      x = Evar $ Var scalarTypeInt ZeroIdx
      y = mkBinary (op numType) x (paramIn scalarTypeInt inc)
      condition = case dir of
        LeftToRight -> mkBinary (PrimGtEq singleType) y (mkConstant (TupRsingle scalarTypeInt) 0)
        RightToLeft -> case sh of
          TupRpair _ n -> mkBinary (PrimLt singleType) y (paramsIn (TupRsingle scalarTypeInt) n)
          _ -> error "Impossible pair"
      ix = expVars $ value $ weakenSucc weakenId
      index' = index repr sh input . Pair ix
    in
      Lam (lhs `LeftHandSidePair` LeftHandSideSingle scalarTypeInt)
        $ Body
        $ Cond condition
          (
            case dir of
              LeftToRight -> apply2 tp f (index' y) (index' x)
              RightToLeft -> apply2 tp f (index' x) (index' y)
          )
          (index' x)

mkDefaultFoldSegFunction
  :: IntegralType i
  -> Arg benv (Fun' (e -> e -> e))
  -> Maybe (Arg benv (Exp' e))
  -> Arg benv (In  (sh, Int) e)
  -> Arg benv (In  DIM1      i)
  -> Fun benv ((sh, Int) -> e)
mkDefaultFoldSegFunction itp (ArgFun f) def (ArgArray _ (ArrayR shr tp) sh input) (ArgArray _ reprSeg shSeg segments)
  | DeclareVars lhsSh kSh valueSh <- declareVars $ shapeType shr
  , DeclareVars lhsE  kE  valueE  <- declareVars tp =
    let
      x1 = case valueSh weakenId of
        TupRpair _ x' -> expVars x'
        _ -> error "Impossible pair"
      x2 = case valueSh (weakenSucc' kE) of
        TupRpair _ x' -> expVars x'
        _ -> error "Impossible pair"
      start  = PrimApp (PrimFromIntegral itp numType) $ index reprSeg shSeg segments $ Pair Nil x1
      end    = PrimApp (PrimFromIntegral itp numType) $ index reprSeg shSeg segments $ Pair Nil $ mkBinary (PrimAdd numType) x2 (mkConstant (TupRsingle scalarTypeInt) 1)
      index' = index (ArrayR shr tp) sh input
      cond   = Lam (lhsE `LeftHandSidePair` LeftHandSideSingle scalarTypeInt) $ Body $ mkBinary (PrimLt singleType) (Evar $ Var scalarTypeInt ZeroIdx) end
      step   = Lam (lhsE `LeftHandSidePair` LeftHandSideSingle scalarTypeInt) $ Body $ Pair
        (apply2 tp f (expVars $ valueE $ weakenSucc weakenId) (index' $ Pair (expVars $ fst' $ valueSh (weakenSucc' kE)) $ Evar $ Var scalarTypeInt ZeroIdx))
        (mkBinary (PrimAdd numType) (Evar $ Var scalarTypeInt ZeroIdx) (mkConstant (TupRsingle scalarTypeInt) 1))
      initial = case def of
        Just (ArgExp d) -> Pair (weakenE kSh d) start
        Nothing -> Pair (index (ArrayR shr tp) sh input $ Pair (expVars $ fst' $ valueSh weakenId) start) (mkBinary (PrimAdd numType) start $ mkConstant (TupRsingle scalarTypeInt) 1)

      fst' :: ExpVars env (a, b) -> ExpVars env a
      fst' (TupRpair a _) = a
      fst' _ = error "Impossible pair"
    in
      Lam lhsSh
        $ Body
        $ Let (lhsE `LeftHandSidePair` LeftHandSideWildcard (TupRsingle scalarTypeInt)) (While cond step initial)
        $ expVars $ valueE weakenId


uncurry' :: Fun env (a -> b -> c) -> Fun env ((a, b) -> c)
uncurry' (Lam lhs1 (Lam lhs2 f)) = Lam (LeftHandSidePair lhs1 lhs2) f
uncurry' (Lam _ (Body _)) = error "impossible: Expression of function type"
uncurry' (Body _) = error "impossible: Expression of function type"

-- Replaces scalar arrays with expression variables in the state of an awhile loop.

data RemoveScalars before after where
  RemoveScalarsKeep :: RemoveScalars t t
  RemoveScalarsPair
    :: RemoveScalars before1 after1
    -> RemoveScalars before2 after2
    -> RemoveScalars (before1, before2) (after1, after2)
  RemoveScalarsScalar :: ScalarType t -> RemoveScalars (Buffer t) t

removeScalarsForType :: ArraysR t -> Exists (RemoveScalars (DesugaredArrays t))
removeScalarsForType TupRunit = Exists RemoveScalarsKeep
removeScalarsForType (TupRsingle (ArrayR shr tp)) = case shr of
  ShapeRz -> Exists $ RemoveScalarsPair RemoveScalarsKeep $ go tp
  _ -> Exists RemoveScalarsKeep
  where
    go :: forall e. TypeR e -> RemoveScalars (Buffers e) e
    go (TupRpair t1 t2) = RemoveScalarsPair (go t1) (go t2)
    go TupRunit = RemoveScalarsKeep
    go (TupRsingle t)
      | Refl <- reprIsSingle @ScalarType @e @Buffer t = RemoveScalarsScalar t
removeScalarsForType (TupRpair l r)
  | Exists RemoveScalarsKeep <- l'
  , Exists RemoveScalarsKeep <- r'
  = Exists RemoveScalarsKeep
  | Exists l'' <- l'
  , Exists r'' <- r'
  = Exists $ RemoveScalarsPair l'' r''
  where
    l' = removeScalarsForType l
    r' = removeScalarsForType r

data RemoveScalarsInTerm op env t where
  RemoveScalarsInTerm
    :: (forall r. OperationAcc op env' r -> OperationAcc op env r)
    -> env :> env'
    -> (forall env''. env' :> env'' -> GroundVars env'' t)
    -> RemoveScalarsInTerm op env t

awhileRemoveScalars
  :: forall tp op env.
     DesugarAcc op
  => ArraysR tp
  -> Uniquenesses (DesugaredArrays tp)
  -> OperationAfun op env (DesugaredArrays tp -> PrimBool)
  -> OperationAfun op env (DesugaredArrays tp -> DesugaredArrays tp)
  -> GroundVars env (DesugaredArrays tp)
  -> OperationAcc op env (DesugaredArrays tp)
awhileRemoveScalars repr us cond step initial
  | not $ desugarPreferNoScalar @op
  = Awhile us cond step initial
  | Exists RemoveScalarsKeep <- remove'
  = Awhile us cond step initial
  | Exists remove <- remove'
  -- Convert initial value
  , RemoveScalarsInTerm b1 k1 res1 <- removeScalarsInTerm' remove weakenId initial
  , us' <- uniquenesses remove us
  , initial' <- res1 weakenId
  = removeScalarsInTermInv (varsType initial') us' remove
  $ b1
  $ Awhile
    us'
    (weaken k1 $ removeBoundScalars remove us cond)
    (weaken k1 $ removeBoundScalars remove us $ removeScalarsInFun tp us remove step)
    initial'
  where
    remove' = removeScalarsForType repr
    tp = varsType initial

    uniquenesses :: RemoveScalars b a -> Uniquenesses b -> Uniquenesses a
    uniquenesses RemoveScalarsKeep u = u
    uniquenesses (RemoveScalarsPair r1 r2) (TupRpair u1 u2) = uniquenesses r1 u1 `TupRpair` uniquenesses r2 u2
    uniquenesses (RemoveScalarsScalar _) _ = TupRsingle Shared
    uniquenesses _ _ = internalError "Tuple mismatch"

removeBoundScalars
  :: RemoveScalars before after
  -> Uniquenesses before
  -> OperationAfun op env (before -> t)
  -> OperationAfun op env (after -> t)
removeBoundScalars remove us (Alam lhs (Abody body))
  | DeclareVars lhsNew k0 value <- declareVars $ tp remove $ lhsToTupR lhs
  , RemoveScalarsInTerm b k1 res <- removeScalarsInTermInv' remove weakenId (value weakenId)
  , Exists lhs' <- rebuildLHS lhs
  = Alam lhsNew
  $ Abody
  $ b
  $ alet' lhs' us (Return $ res weakenId)
  $ weaken (sinkWithLHS lhs lhs' (k1 .> k0)) body
  where
    tp :: RemoveScalars b a -> GroundsR b -> GroundsR a
    tp RemoveScalarsKeep t = t
    tp (RemoveScalarsPair r1 r2) (TupRpair t1 t2) = tp r1 t1 `TupRpair` tp r2 t2
    tp (RemoveScalarsScalar t) _ = TupRsingle $ GroundRscalar t
    tp _ _ = internalError "Tuple mismatch"
removeBoundScalars _ _ _ = internalError "Expected unary function"

removeScalarsInFun
  :: GroundsR before
  -> Uniquenesses before
  -> RemoveScalars before after
  -> OperationAfun op env (t -> before)
  -> OperationAfun op env (t -> after)
removeScalarsInFun tp us r (Alam lhs (Abody body))
  = Alam lhs $ Abody $ removeScalarsInTerm tp us r body
removeScalarsInFun _ _ _ _ = internalError "Expected unary function"

removeScalarsInTerm
  :: GroundsR before
  -> Uniquenesses before
  -> RemoveScalars before after
  -> OperationAcc op env before
  -> OperationAcc op env after
removeScalarsInTerm tp us r term
  | DeclareVars lhs _ value <- declareVars tp
  , RemoveScalarsInTerm bind _ result <- removeScalarsInTerm' r weakenId (value weakenId) =
    alet' lhs us term $ bind $ Return $ result weakenId

removeScalarsInTerm'
  :: RemoveScalars before after
  -> env0 :> env
  -> GroundVars env0 before
  -> RemoveScalarsInTerm op env after
removeScalarsInTerm' RemoveScalarsKeep k0 vars =
  RemoveScalarsInTerm id weakenId $ \k -> mapTupR (weaken (k .> k0)) vars
removeScalarsInTerm' (RemoveScalarsPair r1 r2) k0 (TupRpair v1 v2)
  | RemoveScalarsInTerm b1 k1 res1 <- removeScalarsInTerm' r1 k0 v1
  , RemoveScalarsInTerm b2 k2 res2 <- removeScalarsInTerm' r2 (k1 .> k0) v2
  = RemoveScalarsInTerm
    (b1 . b2)
    (k2 .> k1)
    $ \k -> res1 (k .> k2) `TupRpair` res2 k
removeScalarsInTerm' (RemoveScalarsScalar tp) k0 (TupRsingle buffer) =
  RemoveScalarsInTerm
    (alet'
      (LeftHandSideSingle $ GroundRscalar tp)
      (TupRsingle Shared)
      (Compute $ ArrayInstr (Index $ weaken k0 buffer) $ Const scalarTypeInt 0))
    (weakenSucc weakenId)
    $ \k -> TupRsingle $ Var (GroundRscalar tp) $ weaken k ZeroIdx
removeScalarsInTerm' _ _ _ = internalError "Tuple mismatch"

removeScalarsInTermInv
  :: GroundsR after
  -> Uniquenesses after
  -> RemoveScalars before after
  -> OperationAcc op env after
  -> OperationAcc op env before
removeScalarsInTermInv tp us r term
  | DeclareVars lhs _ value <- declareVars tp
  , RemoveScalarsInTerm bind _ result <- removeScalarsInTermInv' r weakenId (value weakenId) =
    alet' lhs us term $ bind $ Return $ result weakenId

removeScalarsInTermInv'
  :: RemoveScalars before after
  -> env0 :> env
  -> GroundVars env0 after
  -> RemoveScalarsInTerm op env before
removeScalarsInTermInv' RemoveScalarsKeep k0 vars =
  RemoveScalarsInTerm id weakenId $ \k -> mapTupR (weaken (k .> k0)) vars
removeScalarsInTermInv' (RemoveScalarsPair r1 r2) k0 (TupRpair v1 v2)
  | RemoveScalarsInTerm b1 k1 res1 <- removeScalarsInTermInv' r1 k0 v1
  , RemoveScalarsInTerm b2 k2 res2 <- removeScalarsInTermInv' r2 (k1 .> k0) v2
  = RemoveScalarsInTerm
    (b1 . b2)
    (k2 .> k1)
    $ \k -> res1 (k .> k2) `TupRpair` res2 k
removeScalarsInTermInv' (RemoveScalarsScalar tp) k0 (TupRsingle var) =
  RemoveScalarsInTerm
    (alet'
      (LeftHandSideSingle $ GroundRbuffer tp)
      (TupRsingle Shared)
      (Unit var'))
    (weakenSucc weakenId)
    $ \k -> TupRsingle $ Var (GroundRbuffer tp) $ weaken k ZeroIdx
  where
    var' = Var tp $ weaken k0 $ varIdx var
removeScalarsInTermInv' _ _ _ = internalError "Tuple mismatch"
