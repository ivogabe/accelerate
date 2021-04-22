{-# LANGUAGE AllowAmbiguousTypes  #-}
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
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE ViewPatterns         #-}

-- |
-- Module      : Data.Array.Accelerate.Schedule
-- Copyright   : [2012..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--
-- This module should implement fusion.
--

module Data.Array.Accelerate.Schedule (
  IsSchedule(..),
  convertSchedule,
  Scheduled,
  reprIsBody,
) where

import Data.Array.Accelerate.AST.Partitioned
import Data.Array.Accelerate.Error
import Data.Array.Accelerate.Type
import Data.Array.Accelerate.Representation.Type
import Data.Typeable                                                ( (:~:)(..) )

import Data.Array.Accelerate.Debug.Internal.Flags                ( array_fusion )

class IsSchedule sched where
  -- 'a' is a ground type (ie, can be represented using GroundR)
  type ScheduleInput  sched a
  type ScheduleOutput sched a

  convertScheduleFun :: PartitionedAfun op () t -> sched (Cluster op) (Scheduled sched t)

  mapSchedule :: (forall env'. exe env' -> exe' env') -> sched exe env -> sched exe' env

convertSchedule :: forall sched op t. IsSchedule sched => PartitionedAcc op () t -> sched (Cluster op) (ScheduleOutput sched t -> ())
convertSchedule acc
  | Refl <- reprIsBody @sched $ groundsR acc = convertScheduleFun (Abody acc)

type family Scheduled sched a where
  Scheduled sched (a -> b) = ScheduleInput  sched a -> Scheduled sched b
  Scheduled sched a        = ScheduleOutput sched a -> ()

reprIsBody :: forall sched t. GroundsR t -> Scheduled sched t :~: (ScheduleOutput sched t -> ())
reprIsBody TupRunit = Refl
reprIsBody TupRpair{} = Refl
reprIsBody (TupRsingle (GroundRbuffer _)) = Refl
reprIsBody (TupRsingle (GroundRscalar (VectorScalarType _))) = Refl
reprIsBody (TupRsingle (GroundRscalar (SingleScalarType (NumSingleType t)))) = case t of
  IntegralNumType TypeInt    -> Refl
  IntegralNumType TypeInt8   -> Refl
  IntegralNumType TypeInt16  -> Refl
  IntegralNumType TypeInt32  -> Refl
  IntegralNumType TypeInt64  -> Refl
  IntegralNumType TypeWord   -> Refl
  IntegralNumType TypeWord8  -> Refl
  IntegralNumType TypeWord16 -> Refl
  IntegralNumType TypeWord32 -> Refl
  IntegralNumType TypeWord64 -> Refl
  FloatingNumType TypeHalf   -> Refl
  FloatingNumType TypeFloat  -> Refl
  FloatingNumType TypeDouble -> Refl

