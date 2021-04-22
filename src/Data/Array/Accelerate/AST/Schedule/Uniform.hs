{-# LANGUAGE GADTs           #-}
{-# LANGUAGE RankNTypes      #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeOperators   #-}
{-# LANGUAGE TypeFamilies    #-}
{-# OPTIONS_HADDOCK hide #-}
-- |
-- Module      : Data.Array.Accelerate.Schedule.Uniform
-- Copyright   : [2008..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.AST.Schedule.Uniform (
  UniformSchedule(..), UniformScheduleFun(..),
  Input, Output, InputOutputR(..),
  Binding(..), Effect(..),
  BaseR(..), BasesR, BaseVar, BaseVars, BLeftHandSide,
  Signal(..), SignalResolver(..), Ref(..), OutputRef(..),
  module Partitioned,
) where

import Data.Array.Accelerate.AST.Exp
import Data.Array.Accelerate.AST.Idx
import Data.Array.Accelerate.AST.LeftHandSide
import Data.Array.Accelerate.AST.Var
import Data.Array.Accelerate.Type
import Data.Array.Accelerate.Representation.Array
import Data.Array.Accelerate.Representation.Shape
import Data.Array.Accelerate.Representation.Type
import Data.Array.Accelerate.AST.Partitioned as Partitioned         hiding (PartitionedAcc, PartitionedAfun, PreOpenAcc(..), PreOpenAfun(..))
import Control.Concurrent.MVar
import Data.IORef

-- Generic schedule for a uniform memory space and uniform scheduling.
-- E.g., we don't have host and device memory or scheduling.
-- The schedule will exploit task parallelism.

-- The schedule consists of bindings, effects and (parallel) control flow
data UniformSchedule exe env where
  Return  :: UniformSchedule exe env

  Alet    :: BLeftHandSide t env env'
          -> Binding env t
          -> UniformSchedule exe env'
          -> UniformSchedule exe env

  Effect  :: Effect exe env
          -> UniformSchedule exe env
          -> UniformSchedule exe env

  Acond   :: ExpVar env PrimBool
          -> UniformSchedule exe env
          -> UniformSchedule exe env
          -> UniformSchedule exe env

  Awhile  :: InputOutputR input output
          -> UniformScheduleFun exe env (input -> Output PrimBool -> ())
          -> UniformScheduleFun exe env (input -> output -> ())
          -> BaseVars env input
          -> UniformSchedule exe env

  Fork    :: UniformSchedule exe env
          -> UniformSchedule exe env
          -> UniformSchedule exe env

data UniformScheduleFun exe env t where
  Slam  :: BLeftHandSide s env env'
        -> UniformScheduleFun exe env' t
        -> UniformScheduleFun exe env  (s -> t)

  Sbody :: UniformSchedule    exe env'
        -> UniformScheduleFun exe env ()

type family Input t where
  Input ()     = ()
  Input (a, b) = (Input a, Input b)
  Input t      = (Signal, Ref t)

type family Output t where
  Output ()     = ()
  Output (a, b) = (Output a, Output b)
  Output t      = (SignalResolver, OutputRef t)

-- Relation between input and output
data InputOutputR input output where
  InputOutputRsignal :: InputOutputR Signal  SignalResolver
  InputOutputRref    :: InputOutputR (Ref f) (OutputRef t)
  InputOutputRpair   :: InputOutputR i1 o1
                     -> InputOutputR i2 o2
                     -> InputOutputR (i1, i2) (o1, o2)
  InputOutputRunit   :: InputOutputR () ()

-- Bindings of instructions which have some return value.
-- They cannot perform side effects.
--
data Binding env t where
  Compute       :: Exp env t
                -> Binding env t

  NewSignal     :: Binding env (Signal, SignalResolver)

  NewRef        :: GroundR t
                -> Binding env (Ref t, OutputRef t)

  Alloc         :: ShapeR sh
                -> ScalarType e
                -> ExpVars env sh
                -> Binding env (Buffer e)

  Use           :: ScalarType e
                -> Buffer e
                -> Binding env (Buffer e)

  Unit          :: ExpVar env e
                -> Binding env (Buffer e)

  -- undefined result if the Ref hasn't been written
  RefRead       :: BaseVar env (Ref t) -> Binding env t

-- Effects do not have a return value.
data Effect exe env where
  Exec          :: exe args
                -> Args env args
                -> Effect exe env

  SignalAwait   :: [Idx env Signal] -> Effect exe env

  SignalResolve :: [Idx env SignalResolver] -> Effect exe env

  RefWrite      :: BaseVar env (OutputRef t) -> BaseVar env t -> Effect exe env

-- A base value in the schedule is a scalar, buffer, a signal (resolver)
-- or a (possibly mutable) reference
--
data BaseR t where
  BaseRground         :: GroundR t -> BaseR t
  BaseRsignal         :: BaseR Signal
  BaseRsignalResolver :: BaseR SignalResolver
  BaseRref            :: GroundR t -> BaseR (Ref t)
  BaseRrefWrite       :: GroundR t -> BaseR (OutputRef t)

-- Tuples of base values
type BasesR = TupR BaseR

type BaseVar      = Var BaseR
type BaseVars env = Vars BaseR env

type BLeftHandSide = LeftHandSide BaseR

newtype Signal = Signal (MVar ())
newtype SignalResolver = SignalResolver (MVar ())

-- Note: Refs should only be assigned once. They start undefined, and are at some point resolved to a value
newtype Ref t  = Ref (IORef t)
newtype OutputRef t = OutputRef (IORef t)
