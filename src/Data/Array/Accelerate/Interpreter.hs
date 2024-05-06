{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE BangPatterns        #-}
{-# LANGUAGE BlockArguments      #-}
{-# LANGUAGE EmptyCase           #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE InstanceSigs        #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE MagicHash           #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE PatternGuards       #-}
{-# LANGUAGE PatternSynonyms     #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TupleSections       #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeOperators       #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns        #-}

{-# OPTIONS_GHC -fno-warn-name-shadowing #-}
{-# OPTIONS_HADDOCK prune #-}
-- |
-- Module      : Data.Array.Accelerate.Interpreter
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

module Data.Array.Accelerate.Interpreter (
  module Data.Array.Accelerate.Interpreter,
  UniformScheduleFun
) where

import Prelude                                                      hiding (take, (!!), sum, Either(..) )
import Data.Array.Accelerate.AST.Partitioned hiding (Empty)
import Data.Array.Accelerate.AST.Operation
import Data.Array.Accelerate.AST.Kernel
import Data.Array.Accelerate.Trafo.Desugar
import qualified Data.Array.Accelerate.Debug.Internal as Debug
import Data.Array.Accelerate.Representation.Array
import Data.Array.Accelerate.Error
import Data.Array.Accelerate.Analysis.Hash.Exp ( intHost, hashQ )
import Data.Array.Accelerate.Analysis.Hash.Operation
import Data.Array.Accelerate.Representation.Ground
import Data.Array.Accelerate.Representation.Type
import Data.Array.Accelerate.Representation.Shape
import Data.Array.Accelerate.Representation.Slice
import Data.Array.Accelerate.AST.Environment
import Data.Array.Accelerate.Type
import Data.Primitive.Vec
import Data.Primitive.Types
import Data.Primitive.ByteArray
import Formatting hiding (int)
import Data.Text.Lazy.Builder
import Data.Array.Accelerate.Representation.Elt
import Data.Array.Accelerate.Representation.Vec
import Data.Array.Accelerate.Trafo.Exp.Substitution
import Unsafe.Coerce (unsafeCoerce)
import Control.Monad.ST
import Data.Bits
import Data.Array.Accelerate.Backend
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Graph (Var (..), (-?>), fused, infusibleEdges, manifest, LabelledArgOp (LOp))
import qualified Data.Array.Accelerate.Trafo.Partitioning.ILP.Graph as Graph
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Labels
import qualified Data.Set as Set
import Data.Array.Accelerate.Trafo.Partitioning.ILP.Solver
import Lens.Micro ((.~), (&))
import Data.Array.Accelerate.Array.Buffer
import Data.Array.Accelerate.Pretty.Partitioned ()
import Data.Array.Accelerate.AST.Idx
import Data.Array.Accelerate.AST.LeftHandSide (LeftHandSide (LeftHandSideWildcard, LeftHandSideUnit))
import Data.Array.Accelerate.AST.Schedule

import Control.Concurrent (forkIO)
import Data.IORef
import Control.Concurrent.MVar

import Data.Array.Accelerate.AST.Schedule.Uniform (UniformScheduleFun)
import Data.Array.Accelerate.Trafo.Schedule.Uniform ()
import Data.Array.Accelerate.Pretty.Schedule.Uniform ()
import qualified Data.Array.Accelerate.AST.Schedule.Uniform as S
import qualified Data.Map as M
import Control.Monad (when)
import Data.Array.Accelerate.Trafo.Var (DeclareVars(DeclareVars), declareVars)
import Data.Array.Accelerate.Trafo.Operation.Substitution (alet, aletUnique, weaken, LHS (LHS), mkLHS)
import Control.DeepSeq (rnf)
import Data.Map (Map)
import System.IO.Unsafe (unsafePerformIO)

import Data.Array.Accelerate.Eval
import qualified Data.Array.Accelerate.AST.Partitioned as P
import Data.Functor.Identity
import Data.Array.Accelerate.Trafo.LiveVars
import qualified Debug.Trace
import Data.Maybe (fromJust)

data Interpreter
instance Backend Interpreter where
  type Schedule Interpreter = UniformScheduleFun
  type Kernel Interpreter = InterpretKernel


map !?! key = case map M.!? key of
  Just x -> x
  Nothing -> error ("error: map "<> show map <> "does not contain key " <> show key)


-- Pushes backpermute information through the cluster and stores it in the arguments, for use at the start of the loop (indexing) and in generates.
-- makeBackpermuteArg :: Args env args -> Val env -> Clustered InterpretOp args -> BackendArgs InterpretOp env args
-- makeBackpermuteArg = makeBackendArg

instance Eq (BackendClusterArg2 InterpretOp env arg) where
  -- this is just a sanity check
  BCA f x == BCA g y = map f [1..100] == map g [1..100] && x == y

instance Show (BackendClusterArg2 InterpretOp env arg) where
  show (BCA f a) = "bca"

instance StaticClusterAnalysis InterpretOp where
  data BackendClusterArg2 InterpretOp env arg = BCA (Int -> Int) Int -- backpermute function and iteration size

  onOp IBackpermute (BCA outF sz :>: ArgsNil) (ArgFun f :>: i :>: o :>: ArgsNil) env =
    let ArgArray In  (ArrayR shr  _) (flip varsGetVal env -> sh ) _ = i
        ArgArray Out (ArrayR shr' _) (flip varsGetVal env -> sh') _ = o in
                      BCA id 0 :>: BCA (toIndex shr sh . evalFun f (evalArrayInstrDefault env) . fromIndex shr' sh' . outF) sz :>: BCA outF sz :>: ArgsNil
  onOp IGenerate    (BCA outF sz :>: ArgsNil) _ _ =
                      BCA outF sz :>: BCA outF sz :>: ArgsNil -- important: we store the Int -> Int besides the function argument!
  onOp IMap         (BCA outF sz :>: ArgsNil) _ _ =
                      BCA id 0 :>: BCA outF sz :>: BCA outF sz :>: ArgsNil
  onOp IPermute ArgsNil (_ :>: _ :>: _ :>: ArgArray In (ArrayR shr _) sh _ :>: ArgsNil) env =
    let sz = size shr (varsGetVal sh env) in
    BCA id 0 :>: BCA id 0 :>: BCA id 0 :>: BCA id sz :>: ArgsNil
  onOp (IFold1 _) (BCA outF szO :>: ArgsNil) (_ :>: i :>: _ :>: ArgsNil) env =
    let ArgArray In _ (flip varsGetVal env -> (_, sz)) _ = i
        inF x = (+ x `mod` sz) $ outF (x `div` sz) -- this is where the magic happens to fuse backpermute . fold. Would be cleaner on shapes instead of Ints
    in BCA id 0 :>: BCA inF (szO*sz) :>: BCA outF szO :>: ArgsNil
  onOp (IScan1 _ _) _ _ _ = undefined -- BCA id :>: BCA id :>: BCA id :>: ArgsNil -- here we trust that our ILP prevented any backpermutes after the scan
  -- onOp (IAppend Left n) (BCA outF :>: ArgsNil) (_ :>: i :>: _ :>: ArgsNil) env =
  --   let ArgArray In _ (flip varsGetVal env -> (_, sz)) _ = i
  --       inF x = outF $ (+ (x `mod` sz) * (sz + n)) $ n + (x `div` sz) -- or something like this :)
  --   in BCA outF :>: BCA inF :>: BCA outF :>: ArgsNil
  -- onOp (IAppend Right _) (BCA outF :>: ArgsNil) _ _ =
  --   BCA outF :>: BCA outF :>: BCA outF :>: ArgsNil

  valueToIn    (BCA f sz) = BCA f sz
  valueToOut   (BCA f sz) = BCA f sz
  inToValue    (BCA f sz) = BCA f sz
  outToValue   (BCA f sz) = BCA f sz
  outToSh      (BCA f sz) = BCA f sz
  shToOut      (BCA f sz) = BCA f sz
  shToValue    (BCA f sz) = BCA f sz
  varToValue   (BCA f sz) = BCA f sz
  varToSh      (BCA f sz) = BCA f sz
  shToVar      (BCA f sz) = BCA f sz
  shrinkOrGrow (BCA f sz) = BCA f sz
  addTup       (BCA f sz) = BCA f sz
  unitToVar    (BCA f sz) = BCA f sz
  varToUnit    (BCA f sz) = BCA f sz
  inToVar (BCA f sz) = BCA f sz
  def (ArgVar _) _ BCAI = BCA id 0
  def (ArgExp _) _ BCAI = BCA id 0
  def (ArgFun _) _ BCAI = BCA id 0
  def (ArgArray Mut _ _ _) _ BCAI = BCA id 0
  def (ArgArray In  (ArrayR shr _) sh _) env BCAI = BCA id (size shr $ varsGetVal sh env)
  def (ArgArray Out (ArrayR shr _) sh _) env BCAI = BCA id (size shr $ varsGetVal sh env)


-- we can implement stencils using clamp, mirror or wrap with backpermute and zipwith(map), but for stencils using function we need a little extra.
data InterpretOp args where
  IMap         :: InterpretOp (Fun' (s -> t)    -> In sh s -> Out sh  t -> ())
  IBackpermute :: InterpretOp (Fun' (sh' -> sh) -> In sh t -> Out sh' t -> ())
  -- -- backpermute which doesn't error when the target index is out of bounds, but then evaluates the other function like a `generate` at the target index.
  -- -- Generalisation of a 'backpermute with default', but not as general as a generate
  -- IBackpermuteOr :: InterpretOp (Fun' (sh' -> sh) -> Fun' (sh -> t) -> In sh t -> Out sh' t -> ())
  IGenerate    :: InterpretOp (Fun' (sh -> t)              -> Out sh  t -> ())
  IPermute     :: InterpretOp (Fun' (e -> e -> e)
                              -> Mut sh' e
                              -> Fun' (sh -> PrimMaybe sh')
                              -> In sh e
                              -> ())
  -- The interpreter doesn't have 'communication' with other 'threads' like the other backends do, to simulate cooperative scan/fold we use an IORef instead
  IFold1       :: IORef (Map Int e) -> InterpretOp (Fun' (e -> e -> e) -> In (sh, Int) e -> Out sh e -> ())
  IScan1      :: Direction -> IORef (Map Int e) -> InterpretOp (Fun' (e -> e -> e) -> In (sh, Int) e -> Out (sh, Int) e -> ())
  -- append a number of elements to the left or right of each innermost row using the generate function
  -- IAppend :: Side -> Int -> InterpretOp (Fun' ((sh, Int) -> e) -> In (sh, Int) e -> Out (sh, Int) e -> ())

instance DesugarAcc InterpretOp where
  mkMap         a b c   = Exec IMap         (a :>: b :>: c :>:       ArgsNil)
  mkBackpermute a b c   = Exec IBackpermute (a :>: b :>: c :>:       ArgsNil)
  mkGenerate    a b     = Exec IGenerate    (a :>: b :>:             ArgsNil)
  mkPermute     a b c d = Exec IPermute     (a :>: b :>: c :>: d :>: ArgsNil)
  mkFold        a Nothing b c = Exec (IFold1 $ unsafePerformIO $ newIORef mempty) (a :>: b :>: c :>:       ArgsNil)
  -- we desugar a Fold with seed element into a Fold1 followed by a map which prepends the seed
  mkFold a@(ArgFun f) (Just (ArgExp seed)) b@(ArgArray In (ArrayR _ tp) _ _) c@(ArgArray _ arr' sh' _)
    | DeclareVars lhsTemp wTemp kTemp <- declareVars $ buffersR tp =
      aletUnique lhsTemp (desugarAlloc arr' $ fromGrounds sh') $
        alet LeftHandSideUnit
          (mkFold (weaken wTemp a) Nothing (weaken wTemp b) (ArgArray Out arr' (weakenVars wTemp sh') (kTemp weakenId))) $
          case mkLHS tp of
            LHS lhs vars ->
              mkMap
                (ArgFun $
                  Lam lhs $ Body $ (\f -> apply2 tp f (weakenThroughReindex wTemp reindexExp $
                    weakenE weakenEmpty seed) (expVars vars)) $ weakenThroughReindex wTemp reindexExp f)
                (ArgArray In arr' (weakenVars wTemp sh') (kTemp weakenId))
                (weaken wTemp c)
  -- mkScan dir a Nothing b c = Exec (IScan1 dir $ unsafePerformIO $ newIORef mempty) (a :>: b :>: c :>: ArgsNil)
  -- mkScan _ _ _ _ _ = error "exclusive scan not implemented"
  -- we desugar a Scan with seed into a scan1 followed by a map followed by an append
  -- mkScan dir comb (Just (ArgExp seed)) i@(ArgArray In arr@(ArrayR shr tp) sh _) o
  --   | DeclareVars lhsTemp1 wTemp  kTemp1 <- declareVars $ buffersR tp
  --   , DeclareVars lhsTemp2 wTemp2 kTemp2 <- declareVars $ buffersR tp
  --   , wTemp1 <- wTemp2 .> wTemp =
  --     aletUnique lhsTemp1 (desugarAlloc arr $ fromGrounds sh) $
  --       aletUnique lhsTemp2 (desugarAlloc arr $ fromGrounds $ weakenVars wTemp sh) $
  --         alet LeftHandSideUnit
  --           (alet LeftHandSideUnit
  --             (mkScan dir (weaken wTemp1 comb) Nothing (weaken wTemp1 i) (ArgArray Out arr (weakenVars wTemp1 sh) (kTemp1 wTemp2)))
  --             (mkMap (ArgFun $ case mkLHS tp of
  --                     LHS lhs vars ->
  --                       Lam lhs $ Body $ (\f -> apply2 tp f (weakenThroughReindex wTemp1 reindexExp $
  --                         weakenE weakenEmpty seed) (expVars vars)) $ weakenThroughReindex wTemp1 reindexExp $ (\(ArgFun f) -> f) comb)
  --                    (ArgArray In  arr (weakenVars wTemp1 sh) (kTemp1 wTemp2))
  --                    (ArgArray Out arr (weakenVars wTemp1 sh) (kTemp2 weakenId)))) $
  --           mkAppend
  --             (case dir of
  --               LeftToRight -> Left
  --               RightToLeft -> Right)
  --             1
  --             (ArgFun $ Lam (LeftHandSideWildcard $ shapeType shr) $ Body $ weakenThroughReindex wTemp1 reindexExp seed)
  --             (ArgArray In arr (weakenVars wTemp1 sh) (kTemp2 weakenId))
  --             (weaken wTemp1 o)

            -- mkBackpermuteOr 
            --   (case dir of
            --     -- The easy direction: identity backpermute, the default case will trigger on the last element
            --     RightToLeft -> case mkLHS (shapeType shr) of
            --       LHS lhs vars ->
            --         ArgFun $ Lam lhs $ 
            --           Body $ expVars vars
            --     -- The difficult direction: backpermute does a +1, the default case will trigger on the first element
            --     LeftToRight -> case mkLHS (shapeType shr') of
            --       LHS lhs vars ->
            --         ArgFun $ Lam (lhs `LeftHandSidePair` LeftHandSideSingle scalarTypeInt) $ 
            --           Body $ Pair (expVars $ weakenVars (weakenSucc' weakenId) vars) (PrimApp (PrimMin $ NumSingleType $ IntegralNumType TypeInt) $ Pair (Evar (Var scalarTypeInt ZeroIdx)) (Const scalarTypeInt 1))
            --   )

instance EncodeOperation InterpretOp where
  encodeOperation IMap                 = intHost $(hashQ ("Map" :: String))
  encodeOperation IBackpermute         = intHost $(hashQ ("Backpermute" :: String))
  encodeOperation IGenerate            = intHost $(hashQ ("Generate" :: String))
  encodeOperation IPermute             = intHost $(hashQ ("Permute" :: String))
  encodeOperation (IFold1 _)           = intHost $(hashQ ("Fold1" :: String))
  encodeOperation (IScan1 LeftToRight _) = intHost $(hashQ ("Scanl1" :: String))
  encodeOperation (IScan1 RightToLeft _) = intHost $(hashQ ("Scanr1" :: String))
  -- encodeOperation (IAppend Left  n)    = intHost $(hashQ ("Appendl" :: String)) <> intHost n
  -- encodeOperation (IAppend Right n)    = intHost $(hashQ ("Appendr" :: String)) <> intHost n

-- mkAppend :: Side -> Int -> Arg env (Fun' ((sh, Int) -> e)) -> Arg env (In (sh, Int) e) -> Arg env (Out (sh, Int) e) -> OperationAcc InterpretOp env ()
-- mkAppend side i a b c = Exec (IAppend side i) (a :>: b :>: c :>: ArgsNil)

-- mkBackpermuteOr :: Arg env (Fun' (sh' -> sh))
--                 -> Arg env (Fun' (sh  -> t ))
--                 -> Arg env (In sh t)
--                 -> Arg env (Out sh' t)
--                 -> OperationAcc InterpretOp env ()
-- mkBackpermuteOr a b c d = Exec IBackpermuteOr (a :>: b :>: c :>: d :>: ArgsNil)

instance SimplifyOperation InterpretOp where
  detectCopy _          IMap         = detectMapCopies
  detectCopy matchVars' IBackpermute = detectBackpermuteCopies matchVars'
  detectCopy _ _                     = const []

instance SLVOperation InterpretOp where
  slvOperation IGenerate    = defaultSlvGenerate    IGenerate
  slvOperation IMap         = defaultSlvMap         IMap
  slvOperation IBackpermute = defaultSlvBackpermute IBackpermute
  slvOperation _            = Nothing

data InterpretKernel env where
  InterpretKernel :: Clustered InterpretOp args -> Args env args -> InterpretKernel env

instance NFData' InterpretKernel where
  rnf' (InterpretKernel cluster args) = undefined cluster `seq` rnfArgs args

instance IsKernel InterpretKernel where
  type KernelOperation InterpretKernel = InterpretOp
  type KernelMetadata  InterpretKernel = NoKernelMetadata

  compileKernel = const InterpretKernel

instance PrettyKernel InterpretKernel where
  -- PrettyKernelBody provides a Val but prettyOpWithArgs expects a Val', should we change them to have the
  -- same type (either Val or Val'?)
  prettyKernel = PrettyKernelBody False $ \env (InterpretKernel cluster args) -> prettyOpWithArgs env cluster args

-- -- -2 is left>right, -1 is right>left, n is 'according to computation n' (e.g. Backpermute) 
-- -- (Note that Labels are uniquely identified by an Int, the parent just gives extra information)
-- -- Use Output = -3 for 'cannot be fused with consumer', as that is more difficult to express (we don't know the consumer yet)
-- -- We restrict all the Inputs to >= -2.
-- data InterpreterVariables = DimensionsPerThread InOut Label
--                           | IdleThreads InOut Side Label
type InterpreterVariables = ()
  -- deriving (Eq, Ord, Show)
data InOut = InArr | OutArr
  deriving (Eq, Ord, Show)
data Side = Left | Right
  deriving (Eq, Ord, Show)


instance MakesILP InterpretOp where
  type BackendVar InterpretOp = InterpreterVariables
  type BackendArg InterpretOp = Maybe Int
  data BackendClusterArg InterpretOp arg where
    -- ArrayInfo :: { dim :: Int, idleLeft :: Int, idleRight :: Int} -> BackendClusterArg InterpretOp arg -- can't do (m sh e) because vertically fused arrays get a Var' argument
    -- NonArray :: BackendClusterArg InterpretOp arg
    BCAI :: BackendClusterArg InterpretOp arg
  -- each array argument gets labelled with its order,
  -- this ensures that e.g. multiple inputs of the same array
  -- in different orders won't fuse horizontally, and that
  -- the correct one will be used by each consumer
  labelLabelledArg solution l (L arg@(ArgArray In  _ _ _) al) = LOp arg al . Just $ (solution !?! Graph.InDir  l) --, (solution !?! BackendSpecific (DimensionsPerThread  InArr l), solution !?! BackendSpecific (IdleThreads  InArr Left l), solution !?! BackendSpecific (IdleThreads  InArr Right l)))
  labelLabelledArg solution l (L arg@(ArgArray Out _ _ _) al) = LOp arg al . Just $ (solution !?! Graph.OutDir l) --, (solution !?! BackendSpecific (DimensionsPerThread OutArr l), solution !?! BackendSpecific (IdleThreads OutArr Left l), solution !?! BackendSpecific (IdleThreads OutArr Right l)))
  labelLabelledArg _ _ (L arg al) = LOp arg al Nothing

  getClusterArg (LOp ArgArray{} _ (Just _)) = BCAI
  getClusterArg (LOp ArgVar{}   _ (Just _)) = BCAI -- vertically fused array
  getClusterArg (LOp ArgArray{} _ Nothing) = error "TODO: make a nice error"
  getClusterArg (LOp _ _ Nothing) = BCAI
  getClusterArg (LOp _ _ (Just _))         = error "TODO: make a nice error"

  finalize = foldMap $ \l -> timesN (manifest l) .>. c (OutDir l)

  mkGraph IBackpermute (_ :>: ((L _ (_, Set.toList -> lIns)) :>: _ :>: ArgsNil)) l@(Label i _) =
    Graph.Info
      mempty
      (  inputConstraints l lIns
      <> c (InDir l) .==. int i
      -- <> c (BackendSpecific $ IdleThreads InArr Left l) .==. c (BackendSpecific $ IdleThreads OutArr Left l)
      -- <> c (BackendSpecific $ IdleThreads InArr Right l) .==. c (BackendSpecific $ IdleThreads OutArr Right l)
      -- TODO reconsider: this has difficult consequences, because if we're backpermuting a matrix from a vector and Dims was 1, does it make sense still?
      -- Need to just work out some examples by hand

-- seems like we might need not just #dimsperthread (shapeR), but also the size of those dims (shape)
-- like the backpermute functions; these are not known to the ILP but can be statically threaded through back-to-front before evaluating a cluster, using the env
--        or more precisely, we can thread a computation through the cluster at compile time, which can (at run time, before eval of cluster) use the env
--        to compute them
-- it's beginning to feel a lot like this is too much for the interpreter? But a nice little generalisation which allows the backends to use it too would be great.
-- maybe find a way to make interpret without dimsperthread first though

      -- <> c (BackendSpecific $ DimensionsPerThread InArr l) .==. c (BackendSpecific $ DimensionsPerThread OutArr l)
      ) -- enforce that the backpermute follows its own rules, but the output can be anything
      (defaultBounds l)
  mkGraph IGenerate _ l = Graph.Info mempty mempty (defaultBounds l) -- creats some superfluous variables, oh well
  mkGraph IMap (_ :>: L _ (_, Set.toList -> lIns) :>: _ :>: ArgsNil) l =
    Graph.Info
      mempty
      (  inputConstraints l lIns
      <> c (InDir l) .==. c (OutDir l)
      -- <> c (BackendSpecific $ IdleThreads InArr Left l) .==. c (BackendSpecific $ IdleThreads OutArr Left l)
      -- <> c (BackendSpecific $ IdleThreads InArr Right l) .==. c (BackendSpecific $ IdleThreads OutArr Right l)
      -- <> c (BackendSpecific $ DimensionsPerThread InArr l) .==. c (BackendSpecific $ DimensionsPerThread OutArr l)
      )
      (defaultBounds l)
  mkGraph IPermute (_ :>: L _ (_, lTargets) :>: _ :>: L _ (_, Set.toList -> lIns) :>: ArgsNil) l@(Label i _) =
    Graph.Info
      (  mempty & infusibleEdges .~ Set.map (-?> l) lTargets) -- Cannot fuse with the producer of the target array
      (  inputConstraints l lIns <> c (OutDir l) .==. int (-3-i)) -- convention meaning infusible
      (  lower (-2) (InDir l)
      -- <> lower 0 (BackendSpecific $ IdleThreads InArr Left l)
      -- <> lower 0 (BackendSpecific $ IdleThreads InArr Right l)
      -- <> equal 0 (BackendSpecific $ IdleThreads OutArr Left l)
      -- <> equal 0 (BackendSpecific $ IdleThreads OutArr Right l)
      -- <> equal 0 (BackendSpecific $ DimensionsPerThread OutArr l)
      )

  mkGraph (IFold1 _) (_ :>: L _ (_, Set.toList -> lIns) :>: _ :>: ArgsNil) l =
    Graph.Info
      mempty
      ( inputConstraints l lIns
        <> c (InDir l) .==. c (OutDir l)
        -- <> c (BackendSpecific $ IdleThreads InArr Left l) .==. c (BackendSpecific $ IdleThreads OutArr Left l)
        -- <> c (BackendSpecific $ IdleThreads InArr Right l) .==. c (BackendSpecific $ IdleThreads OutArr Right l)
        -- <> c (BackendSpecific $ DimensionsPerThread InArr l) .+. int 1 .==. c (BackendSpecific $ DimensionsPerThread OutArr l)
        )
      (defaultBounds l)

  mkGraph (IScan1 _ _) (_ :>: L _ (_, Set.toList -> lIns) :>: _ :>: ArgsNil) l =
    Graph.Info
      mempty
      ( inputConstraints l lIns
        <> c (InDir l) .==. c (OutDir l)
        <> c (InDir l) .<=. int 0
        -- <> c (BackendSpecific $ IdleThreads InArr Left l) .==. c (BackendSpecific $ IdleThreads OutArr Left l)
        -- <> c (BackendSpecific $ IdleThreads InArr Right l) .==. c (BackendSpecific $ IdleThreads OutArr Right l)
        -- <> c (BackendSpecific $ DimensionsPerThread InArr l) .+. int 1 .==. c (BackendSpecific $ DimensionsPerThread OutArr l)
        )
      (defaultBounds l)

  -- mkGraph (IAppend side n) (_ :>: L _ (_, Set.toList -> lIns) :>: _ :>: ArgsNil) l =
  --   Graph.Info
  --     mempty
  --     ( inputConstraints l lIns
  --       <> c (InDir l) .==. c (OutDir l)
  --       -- <> c (BackendSpecific $ IdleThreads InArr Left l) .==. c (BackendSpecific $ IdleThreads OutArr Left l)   .+. int (if side == Left  then n else 0)
  --       -- <> c (BackendSpecific $ IdleThreads InArr Right l) .==. c (BackendSpecific $ IdleThreads OutArr Right l) .+. int (if side == Right then n else 0)
  --       -- <> c (BackendSpecific $ DimensionsPerThread InArr l) .==. c (BackendSpecific $ DimensionsPerThread OutArr l)
  --       )
  --     (defaultBounds l)

  -- encodeBackendClusterArg (ArrayInfo d l r) = intHost $(hashQ ("ArrayInfo" :: String)) <> intHost d <> intHost l <> intHost r
  -- encodeBackendClusterArg NonArray          = intHost $(hashQ ("NonArray" :: String))
  encodeBackendClusterArg BCAI = intHost $(hashQ ("BCAI" :: String))

  -- mkGraph IBackpermuteOr (_ :>: _ :>: ((L _ (_, Set.toList -> lIns)) :>: _)) l@(Label i _) =
  --   Info
  --     mempty
  --     (  inputConstraints l lIns
  --     <> c (InDir l) .==. int i
  --     -- <> c (BackendSpecific $ IdleThreads InArr Left l) .==. c (BackendSpecific $ IdleThreads OutArr Left l)
  --     -- <> c (BackendSpecific $ IdleThreads InArr Right l) .==. c (BackendSpecific $ IdleThreads OutArr Right l)
  --     <> c (BackendSpecific $ DimensionsPerThread InArr l) .==. c (BackendSpecific $ DimensionsPerThread OutArr l)
  --     ) 
  --     (defaultBounds l)

-- | If l and lIn are fused, the out-order of lIn and the in-order of l should match
inputConstraints :: Label -> [Label] -> Constraint InterpretOp
inputConstraints l = foldMap $ \lIn ->
                timesN (fused lIn l) .>=. c (InDir l) .-. c (OutDir lIn)
    <> (-1) .*. timesN (fused lIn l) .<=. c (InDir l) .-. c (OutDir lIn)
    -- <>          timesN (fused lIn l) .>=. c (BackendSpecific $ DimensionsPerThread InArr l) .-. c (BackendSpecific $ DimensionsPerThread OutArr lIn)
    -- <> (-1) .*. timesN (fused lIn l) .<=. c (BackendSpecific $ DimensionsPerThread InArr l) .-. c (BackendSpecific $ DimensionsPerThread OutArr lIn)
    -- <>          timesN (fused lIn l) .>=. c (BackendSpecific $ IdleThreads InArr Left  l) .-. c (BackendSpecific $ IdleThreads OutArr Left  lIn)
    -- <> (-1) .*. timesN (fused lIn l) .<=. c (BackendSpecific $ IdleThreads InArr Left  l) .-. c (BackendSpecific $ IdleThreads OutArr Left  lIn)
    -- <>          timesN (fused lIn l) .>=. c (BackendSpecific $ IdleThreads InArr Right l) .-. c (BackendSpecific $ IdleThreads OutArr Right lIn)
    -- <> (-1) .*. timesN (fused lIn l) .<=. c (BackendSpecific $ IdleThreads InArr Right l) .-. c (BackendSpecific $ IdleThreads OutArr Right lIn)

defaultBounds :: Label -> Bounds InterpretOp
defaultBounds l = lower (-2) (InDir l) <> lower (-2) (OutDir l)
                -- <> lower 0 (BackendSpecific $ IdleThreads InArr Left l)
                -- <> lower 0 (BackendSpecific $ IdleThreads InArr Right l)
                -- <> lower 0 (BackendSpecific $ IdleThreads OutArr Left l)
                -- <> lower 0 (BackendSpecific $ IdleThreads OutArr Right l)


instance NFData' (BackendClusterArg InterpretOp) where
  -- rnf' (ArrayInfo x y z) = rnf x `seq` rnf y `seq` rnf z
  -- rnf' NonArray = ()
  rnf' BCAI = ()

instance ShrinkArg (BackendClusterArg InterpretOp) where
  -- shrinkArg _ (ArrayInfo x y z) = ArrayInfo x y z
  -- shrinkArg _ _ = error "impossible"
  -- deadArg (ArrayInfo x y z) = ArrayInfo x y z
  -- deadArg _ = error "impossible"
  shrinkArg _ BCAI = BCAI
  deadArg BCAI = BCAI

instance NFData' InterpretOp where
  rnf' (IScan1 dir lookup) = lookup `seq` dir `seq` ()
  rnf' (IFold1 lookup) = lookup `seq` ()
  -- rnf' (IAppend side n) = side `seq` n `seq` ()
  rnf' IMap = ()
  rnf' IBackpermute = ()
  rnf' IGenerate = ()
  rnf' IPermute = ()

instance PrettyOp InterpretOp where
  prettyOp IMap         = "map"
  prettyOp IBackpermute = "backpermute"
  prettyOp IGenerate    = "generate"
  prettyOp IPermute     = "permute"
  prettyOp (IFold1 _)   = "fold1"
  -- prettyOp IBackpermuteOr = "backpermute_with_default_generate"
  prettyOp (IScan1 LeftToRight _) = "scanl1"
  prettyOp (IScan1 RightToLeft _) = "scanr1"
  -- prettyOp (IAppend _ _) = "append"

instance Execute UniformScheduleFun InterpretKernel where
  executeAfunSchedule = const $ executeScheduleFun Empty

executeScheduleFun :: Val env -> UniformScheduleFun InterpretKernel env t -> IOFun t
executeScheduleFun env (S.Sbody schedule) = executeSchedule env schedule
executeScheduleFun env (S.Slam lhs fun) = \input -> executeScheduleFun (env `push` (lhs, input)) fun

executeSchedule :: Val env -> S.UniformSchedule InterpretKernel env -> IO ()
executeSchedule !env = \case
  S.Return -> return ()
  S.Alet lhs binding body -> do
    value <- executeBinding env binding
    let env' = env `push` (lhs, value)
    executeSchedule env' body
  S.Effect effect next -> do
    executeEffect env effect
    executeSchedule env next
  S.Acond var true false next -> do
    let value = prj (varIdx var) env
    let branch = if value == 1 then true else false
    executeSchedule env branch
    executeSchedule env next
  S.Awhile io step input next -> do
    executeAwhile env io step (prjVars input env)
    executeSchedule env next
  S.Spawn a b -> do
    _ <- forkIO (executeSchedule env a)
    executeSchedule env b

executeBinding :: Val env -> S.Binding env t -> IO t
executeBinding env = \case
  S.Compute expr ->
    return $ evalExp expr (evalArrayInstrDefault env)
  S.NewSignal _ -> do
    mvar <- newEmptyMVar
    return (S.Signal mvar, S.SignalResolver mvar)
  S.NewRef _ -> do
    ioref <- newIORef $ internalError "Illegal schedule: Read from ref without value. Some synchronization might be missing."
    return (S.Ref ioref, S.OutputRef ioref)
  S.Alloc shr tp sh -> do
    let n = size shr $ prjVars sh env
    MutableBuffer n buffer <- newBuffer tp n
    return $ Buffer n buffer
  S.Use _ _ buffer ->
    return buffer
  S.Unit (Var tp ix) -> do
    mbuffer@(MutableBuffer 1 buffer) <- newBuffer tp 1
    writeBuffer tp mbuffer 0 $ prj ix env
    return $ Buffer 1 buffer
  S.RefRead ref -> do
    let S.Ref ioref = prj (varIdx ref) env
    readIORef ioref

executeEffect :: forall env. Val env -> S.Effect InterpretKernel env -> IO ()
executeEffect env = \case
  S.Exec _ kernelFun args ->
    executeKernelFun env Empty kernelFun args
  S.SignalAwait signals -> mapM_ await signals
  S.SignalResolve signals -> mapM_ resolve signals
  S.RefWrite ref valueVar -> do
    let S.OutputRef ioref = prj (varIdx ref) env
    let value = prj (varIdx valueVar) env
    writeIORef ioref value
  where
    await :: Idx env S.Signal -> IO ()
    await idx = do
      let S.Signal mvar = prj idx env
      readMVar mvar

    resolve :: Idx env S.SignalResolver -> IO ()
    resolve idx = do
      let S.SignalResolver mvar = prj idx env
      putMVar mvar ()

executeKernelFun :: Val env -> Val kenv -> OpenKernelFun InterpretKernel kenv t -> S.SArgs env t -> IO ()
executeKernelFun env kernelEnv (KernelFunLam KernelArgRscalar{} fun) (S.SArgScalar var :>: args)
  = executeKernelFun env (Push' kernelEnv (prj (varIdx var) env)) fun args
executeKernelFun env kernelEnv (KernelFunLam KernelArgRbuffer{} fun) (S.SArgBuffer _ var :>: args)
  = executeKernelFun env (Push' kernelEnv (prj (varIdx var) env)) fun args
executeKernelFun _   kernelEnv (KernelFunBody (InterpretKernel cluster args)) ArgsNil = evalClusterInterpreter cluster args kernelEnv

executeAwhile
  :: Val env
  -> S.InputOutputR input output
  -> UniformScheduleFun InterpretKernel env (input -> S.Output PrimBool -> output -> ())
  -> input
  -> IO ()
executeAwhile env io step input = do
  -- Set up the output variables for this iteration (and the input for the next)
  (S.Signal mvarCondition, signalResolverCondition) <- executeBinding env (S.NewSignal "interpreter signal")
  (S.Ref iorefCondition, outputRefCondition) <- executeBinding env $ S.NewRef $ GroundRscalar scalarType
  (output, nextInput) <- bindAwhileIO io

  -- Execute a step
  executeScheduleFun env step input (signalResolverCondition, outputRefCondition) output

  -- Check condition
  readMVar mvarCondition
  condition <- readIORef iorefCondition
  when (condition == 1) $
    executeAwhile env io step nextInput

bindAwhileIO :: S.InputOutputR input output -> IO (output, input)
bindAwhileIO S.InputOutputRsignal = do
  mvar <- newEmptyMVar
  return (S.SignalResolver mvar, S.Signal mvar)
bindAwhileIO (S.InputOutputRref _) = do
  ioref <- newIORef $ internalError "Illegal schedule: Read from ref without value. Some synchronization might be missing."
  return (S.OutputRef ioref, S.Ref ioref)
bindAwhileIO (S.InputOutputRpair io1 io2) = do
  (output1, input1) <- bindAwhileIO io1
  (output2, input2) <- bindAwhileIO io2
  return ((output1, output2), (input1, input2))
bindAwhileIO S.InputOutputRunit =
  return ((), ())

prjVars :: Vars s env t -> Val env -> t
prjVars TupRunit         _   = ()
prjVars (TupRpair v1 v2) env = (prjVars v1 env, prjVars v2 env)
prjVars (TupRsingle var) env = prj (varIdx var) env

instance TupRmonoid Identity where
  pair' (Identity a) (Identity b) = Identity (a,b)
  unpair' (Identity (a,b)) = (Identity a, Identity b)

instance EvalOp InterpretOp where
  -- We have to sprinkle 'Identity' around a bit here, to allow other backends to use different types
  type EvalMonad InterpretOp = IO
  type Index InterpretOp = Int
  type Embed' InterpretOp = Identity
  type EnvF InterpretOp = Identity

  unit = Identity ()

  evalOp _ _ IMap env (Push (Push _ (BAE (Value' (Identity x) (Shape' shr sh)) _)) (BAE f _)) =
    pure $ Push Empty (FromArg $ Value' (Identity $ evalFun f (evalArrayInstrDefault env) x) (Shape' shr sh))
  evalOp _ _ IBackpermute _ (Push (Push (Push _ (BAE sh _)) (BAE (Value' x _) _)) _) =
    pure $ Push Empty (FromArg $ Value' x sh) -- We evaluated the backpermute at the start already, now simply relabel the shape info
  evalOp i _ IGenerate env (Push (Push _ (BAE (Shape' shr sh) (BCA bp sz))) (BAE f _)) =
    pure $ Push Empty (FromArg $ Value' (Identity $ evalFun f (evalArrayInstrDefault env) (linearIndexToSh shr (runIdentity sh) (bp i))) (Shape' shr sh))
  evalOp i _ IPermute env (Push (Push (Push (Push _ (BAE (Value' (Identity x) (Shape' shr (Identity sh))) (BCA bp sz))) (BAE shf _)) (BAE (ArrayDescriptor shr' sh' buf, typ) _)) (BAE ef _)) = 
    do
      case evalFun shf (evalArrayInstrDefault env) $ linearIndexToSh shr sh (bp i) of
        (0,_) -> pure ()
        (1,((),target)) -> do
          let j = shToLinearIndex shr' (varsGetVal sh' env) target
          old <- indexBuffers' typ (varsGetVal buf env) j
          writeOutputInterpreter typ buf env j (evalFun ef (evalArrayInstrDefault env) x old) 
        _ -> error "primMaybe with weird tag"
      pure Empty
  evalOp i _ (IFold1 acc) env (Push (Push _ (BAE (Value' (Identity x) (Shape' shr@(ShapeRsnoc shr') (Identity sh@(sh',_)))) (BCA bp sz))) (BAE f _)) = 
    do
      let ix = firstOfRow (bp i) (Shape shr sh) 0
      x' <- if bp i == ix 
        then modifyIORef acc (M.insert ix x) >> pure x
        -- todo: check with non-commutative operator. We might need to keep track of the reduction direction
        else modifyIORef acc (M.update (Just . evalFun f (evalArrayInstrDefault env) x) ix) >> (M.! ix) <$> readIORef acc
      pure $ Push Empty $ FromArg $ Value' (Identity x') (Shape' shr' (Identity sh'))
    

  evalOp _ _ (IScan1 _ acc) env _ = error "todo"

  writeOutput r _ buf env n (Identity x) = writeOutputInterpreter (TupRsingle r) buf env n x
  readInput r _ buf env (BCA f sz) n = Identity <$> indexBuffers' (TupRsingle r) (varsGetVal buf env) (f n)

  indexsh  gvs env = pure . Identity $ varsGetVal gvs env
  indexsh' evs env = pure . Identity $ varsGetVal evs env
  subtup s = Identity . subTup s . runIdentity
  
writeOutputInterpreter :: TypeR e -> Vars s env (Buffers e) -> Val env -> Int -> e -> IO ()
writeOutputInterpreter r buf env n x = writeBuffers r (veryUnsafeUnfreezeBuffers r $ varsGetVal buf env) n x

evalClusterInterpreter :: Clustered InterpretOp args -> Args env args -> Val env -> IO ()
evalClusterInterpreter (Clustered c b) args env = 
  let b' = makeBackendArg args env c b in
  doNTimes (iterationsize c b') $ evalCluster c b args env
-- evalClusterInterpreter c@(Cluster _ (Cluster' io _)) args env = doNTimes (iterationsize io args env) $ evalCluster c args env


iterationsize :: Cluster InterpretOp args -> BackendArgs InterpretOp env args -> Int
iterationsize (Op _ _) ArgsNil = 0
iterationsize (Op _ _) ((BCA _ n) :>: args) = if n==0 then iterationsize (Op undefined undefined) args else n
iterationsize (P.Fused f l r) b = 
  let lsz = iterationsize l (left' (\(BCA f x) -> BCA f x) f b) 
  in if lsz == 0 
     then iterationsize r (right' (\(BCA f x)->BCA f x) (\(BCA f x)->BCA f x) f b) 
     else lsz

-- iterationsize (Op _) ArgsNil env = Nothing
-- iterationsize (Op _) ((ArgVar _) :>: args) env = iterationsize (Op undefined) args env
-- iterationsize (Op _) ((ArgExp _) :>: args) env = iterationsize (Op undefined) args env
-- iterationsize (Op _) ((ArgFun _) :>: args) env = iterationsize (Op undefined) args env
-- iterationsize (Op _) ((ArgArray Mut ar tr tr') :>: args) env = iterationsize (Op undefined) args env
-- iterationsize (Op _) ((ArgArray In ar tr tr') :>: args) env = _wo
-- iterationsize (Op _) ((ArgArray Out ar tr tr') :>: args) env = _wp
-- iterationsize (P.Fused fu clus clus') args env = _wd


-- TODO update when we add folds, reconsider when we add scans that add 1 to the size...
-- iterationsize :: ClusterIO args i o -> Args env args -> Val env -> Int
-- iterationsize io args env = case io of
--   P.Empty -> error "no size"
--   P.Output {}   -> case args of ArgArray Out (ArrayR shr _) sh _ :>: _ -> arrsize shr (varsGetVal sh env)
--   P.Vertical _ _ io' -> case args of -- skip past this one
--     ArgVar _ :>: args' -> iterationsize io' args' env
--   P.Input  io'       -> case args of ArgArray In  _ _ _ :>: args' -> iterationsize io' args' env   -- -> arrsize shr (varsGetVal sh env)
--   P.MutPut io'       -> case args of ArgArray Mut _ _ _ :>: args' -> iterationsize io' args' env -- arrsize shr (varsGetVal sh env)
--   P.ExpPut' io' -> case args of _ :>: args' -> iterationsize io' args' env -- skip past this one
--   P.Trivial io' -> case args of _ :>: args' -> iterationsize io' args' env


arrsize :: ShapeR sh -> sh -> Int
arrsize ShapeRz () = 1
arrsize (ShapeRsnoc shr) (sh,x) = x * arrsize shr sh


doNTimes :: Monad m => Int -> (Int -> m ()) -> m ()
doNTimes n f
  | n == 0 = pure ()
  | otherwise = f (n-1) >> doNTimes (n-1) f

linearIndexToSh :: ShapeR sh -> sh -> Int -> sh
linearIndexToSh ShapeRz () 0 = ()
linearIndexToSh ShapeRz () _ = error "non-zero index in unit array"
linearIndexToSh (ShapeRsnoc shr) (sh, outer) i = let
  innerSize = arrsize shr sh
  outerIndex = i `div` innerSize
  innerIndex = linearIndexToSh shr sh (i `mod` innerSize)
  in (innerIndex, outerIndex)

shToLinearIndex :: ShapeR sh -> sh -> sh -> Int
shToLinearIndex ShapeRz () () = 0
shToLinearIndex (ShapeRsnoc shr) (sh, x) (sh', y) = let
  innerSize = arrsize shr sh
  innerIndex = shToLinearIndex shr sh sh'
  in y*innerSize+innerIndex


-- TODO make these think about the new info: pass if idle, and loop if nested
  -- make a little combinator for that
-- evalOp _ IMap         env (PushBPFA _ f    infoF (PushBPFA _ (Value x (Shape shr sh)) infoX _)) = pure $ PushFA (Value (evalFun f env x) (Shape shr sh)) Empty
-- evalOp _ IBackpermute _   (PushBPFA _ _    infoF (PushBPFA _ (Value x _) infoI (PushBPFA _ sh infoO _))) = pure $ PushFA (Value x sh) Empty -- We evaluated the backpermute at the start already, now simply relabel the shape info
-- evalOp i IGenerate    env (PushBPFA f' f   infoF (PushBPFA _ (Shape shr sh) infoSh _)) = pure $ PushFA (Value (evalFun f env $ fromIndex shr sh (f' i)) (Shape shr sh)) Empty -- apply f', the Int->Int backpermute function, to our index before evaluating the generate function.
-- evalOp i IPermute     env (PushBPFA _ comb infoC (PushBPFA _ target         infoT (PushBPFA _ f infoF (PushBPFA _ (Value (e :: e) (Shape shr sh)) infoI _)))) =
--   let typer = case comb of
--         Lam lhs _ -> lhsToTupR lhs
--         _ -> error "impossible; is a function"
--   in
--   case evalFun f env (fromIndex shr sh i) of
--     (0, _) -> pure $ PushFA target Empty
--     (1, ((), sh)) -> case target of
--       ArrayDescriptor shr shvars bufvars -> do
--         let shsize = varsGetVal shvars env
--         let j = toIndex shr shsize sh
--         let buf = varsGetVal bufvars env
--         let buf' = veryUnsafeUnfreezeBuffers @e typer buf
--         x <- readBuffers @e typer buf' j
--         let x' = evalFun comb env x e
--         writeBuffers typer buf' j x'
--         return $ PushFA target Empty
--     _ -> error "PrimMaybe's tag was non-zero and non-one"
-- evalOp i (IAppend side n) env (PushBPFA f' f   infoF (PushBPFA _ (Value x shX) infoX (PushBPFA _ (Shape shr sh) infoO _))) = 
--   if f' i - firstOfRow (f' i) (Shape shr sh) (idleLeft infoO) <= n
--     then pure $ PushFA (Value x (Shape shr sh)) Empty
--     else pure $ PushFA (Value (evalFun f env $ fromIndex shr sh (f' i)) (Shape shr sh)) Empty

-- -- TODO the backpermute function!!!!!
-- evalOp i (IFold1 lookup) env (PushBPFA _ f infoF (PushBPFA _ (Value x sh) infoX (PushBPFA _ outSh _ _)))
--   | i == firstOfRow i sh (idleLeft infoX) = do -- write input to output
--       lookupmap <- readIORef lookup
--       writeIORef lookup (M.insert i x lookupmap)
--       pure $ PushFA (Value x outSh) Empty
--   | otherwise = do -- combine input with output using f
--       lookupmap <- readIORef lookup
--       let y = lookupmap !?! firstOfRow i sh (idleLeft infoX)
--       let z = evalFun f env y x
--       writeIORef lookup (M.insert (firstOfRow i sh (idleLeft infoX)) z lookupmap)
--       pure $ PushFA (Value z outSh) Empty
-- evalOp i (IScan1 dir lookup) env (PushBPFA _ f infoF (PushBPFA _ (Value x sh) infoX _outputstuff))
--   | i == firstOfRow i sh (idleLeft infoX) = do -- write input to output
--       lookupmap <- readIORef lookup
--       writeIORef lookup $ M.insert i x lookupmap
--       pure $ PushFA (Value x sh) Empty
--   | otherwise = do -- combine input with previous output using f
--       lookupmap <- readIORef lookup
--       let y = lookupmap !?! (i - 1)
--       let z = evalFun f env y x
--       writeIORef lookup $ M.insert i z lookupmap
--       pure $ PushFA (Value z sh) Empty

firstOfRow :: Int -> Sh sh e -> Int -> Int
firstOfRow i (Shape ShapeRz ()) idleRowsLeft
  | i > idleRowsLeft = i - idleRowsLeft
  | otherwise = error "not in a row"
firstOfRow i (Shape (ShapeRsnoc _) (_, n)) idleRowsLeft = (i `mod` (n + idleRowsLeft)) - idleRowsLeft




-- Program execution
-- -----------------

-- | Run a complete embedded array program using the reference interpreter.
--

-- run :: forall a. (HasCallStack, Sugar.Arrays a) => Smart.Acc a -> a
-- run _ = unsafePerformIO execute
--   where
--     acc :: PartitionedAcc InterpretOp () (DesugaredArrays (Sugar.ArraysR a))
--     !acc    = undefined -- convertAcc a
--     execute = do
--       Debug.dumpGraph $!! acc
--       Debug.dumpSimplStats
--       res <- phase "execute" Debug.elapsed $ undefined
--       return $ Sugar.toArr $ snd res

-- -- | This is 'runN' specialised to an array program of one argument.
-- --
-- run1 :: (HasCallStack, Sugar.Arrays a, Sugar.Arrays b) => (Smart.Acc a -> Smart.Acc b) -> a -> b
-- run1 = runN

-- -- | Prepare and execute an embedded array program.
-- --
-- runN :: forall f. (HasCallStack, Afunction f) => f -> AfunctionR f
-- runN f = go
--   where
--     !acc    = convertAfun f
--     !afun   = unsafePerformIO $ do
--                 Debug.dumpGraph $!! acc
--                 Debug.dumpSimplStats
--                 return acc
--     !go     = eval (afunctionRepr @f) afun Empty
--     --
--     eval :: AfunctionRepr g (AfunctionR g) (ArraysFunctionR g)
--          -> DelayedOpenAfun aenv (ArraysFunctionR g)
--          -> Val aenv
--          -> AfunctionR g
--     eval (AfunctionReprLam reprF) (Alam lhs f) aenv = \a -> eval reprF f $ aenv `push` (lhs, Sugar.fromArr a)
--     eval AfunctionReprBody        (Abody b)    aenv = unsafePerformIO $ phase "execute" Debug.elapsed (Sugar.toArr . snd <$> evaluate (evalOpenAcc b aenv))
--     eval _                        _aenv        _    = error "Two men say they're Jesus; one of them must be wrong"


-- Debugging
-- ---------

phase :: Builder -> Format Builder (Double -> Double -> Builder) -> IO a -> IO a
phase n fmt = Debug.timed Debug.dump_phases (now ("phase " <> n <> ": ") % fmt)




-- Array expression evaluation
-- ---------------------------

type WithReprs acc = (ArraysR acc, acc)

fromFunction' :: ArrayR (Array sh e) -> sh -> (sh -> e) -> WithReprs (Array sh e)
fromFunction' repr sh f = (TupRsingle repr, fromFunction repr sh f)





-- Scalar expression evaluation
-- ----------------------------

newtype EvalArrayInstr arr = EvalArrayInstr (forall s t. arr (s -> t) -> s -> t)

evalArrayInstrDefault :: Val aenv -> EvalArrayInstr (ArrayInstr aenv)
evalArrayInstrDefault aenv = EvalArrayInstr $ \instr arg -> case instr of
  Index buffer  -> indexBuffer (groundRelt $ varType buffer) (prj (varIdx buffer) aenv) arg
  Parameter var -> prj (varIdx var) aenv

evalNoArrayInstr :: EvalArrayInstr NoArrayInstr
evalNoArrayInstr = EvalArrayInstr $ \case {}

-- Evaluate a closed scalar expression
--
evalExp :: HasCallStack => PreOpenExp arr () t -> EvalArrayInstr arr -> t
evalExp e = evalOpenExp e Empty

-- Evaluate a closed scalar function
--
evalFun :: HasCallStack => PreOpenFun arr () t -> EvalArrayInstr arr -> t
evalFun f = evalOpenFun f Empty

-- Evaluate an open scalar function
--
evalOpenFun :: HasCallStack => PreOpenFun arr env t -> Val env -> EvalArrayInstr arr -> t
evalOpenFun (Body e)    env arr = evalOpenExp e env arr
evalOpenFun (Lam lhs f) env arr =
  \x -> evalOpenFun f (env `push` (lhs, x)) arr


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
    -> Val env
    -> EvalArrayInstr arr
    -> t
evalOpenExp pexp env arr@(EvalArrayInstr runArrayInstr) =
  let
      evalE :: PreOpenExp arr env t' -> t'
      evalE e = evalOpenExp e env arr

      evalF :: PreOpenFun arr env f' -> f'
      evalF f = evalOpenFun f env arr
  in
  case pexp of
    Let lhs exp1 exp2           -> let !v1  = evalE exp1
                                       env' = env `push` (lhs, v1)
                                   in  evalOpenExp exp2 env' arr
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

    ArrayInstr instr ix         -> runArrayInstr instr (evalE ix)
    ShapeSize shr sh            -> size shr (evalE sh)
    Foreign _ _ f e             -> evalOpenFun f Empty evalNoArrayInstr $ evalE e
    Coerce t1 t2 e              -> evalCoerceScalar t1 t2 (evalE e)


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

