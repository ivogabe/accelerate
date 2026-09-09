{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE RankNTypes           #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

-- |
-- Module      : Data.Array.Accelerate.AST.Schedule
-- Copyright   : [2012..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--
-- This module defines the interface for schedules, to be implemented
-- in other modules.
--

module Data.Array.Accelerate.AST.Schedule (
  IsSchedule(..),
  convertSchedule,
  Scheduled,
  reprIsBody,
  IOFun, FullIOFun, FullIOFun',
  flattenIOFun, unsafePerformIOFun,
  generateKernelNameAndDescription
) where

import Data.Array.Accelerate.AST.Partitioned
import Data.Array.Accelerate.AST.Kernel
import Data.Array.Accelerate.AST.LeftHandSide
import Data.Array.Accelerate.Type
import Data.Array.Accelerate.Representation.Ground
import Data.Array.Accelerate.Representation.Type
import Data.Typeable                                                ( (:~:)(..) )
import Data.List (sortOn, group)
import Data.Ord
import Control.Monad
import System.IO.Unsafe

class IsSchedule sched where
  -- 'a' is a ground type (ie, can be represented using GroundR)
  type ScheduleInput  sched a
  type ScheduleOutput sched a

  rnfSchedule :: IsKernel kernel => sched kernel env t -> ()

  convertScheduleFun
    :: IsKernel kernel
    => PartitionedAfun (KernelOperation kernel) () t -> sched kernel () (Scheduled sched t)

  callScheduledFun :: GFunctionR t -> IOFun (Scheduled sched t) -> FullIOFun t

convertSchedule
  :: forall sched kernel t.
     (IsSchedule sched, IsKernel kernel)
  => PartitionedAcc (KernelOperation kernel) () t -> sched kernel () (ScheduleOutput sched t -> ())
convertSchedule acc
  | Refl <- reprIsBody @sched $ groundsR acc = convertScheduleFun (Abody acc)

type family Scheduled sched a where
  Scheduled sched (a -> b) = ScheduleInput  sched a -> Scheduled sched b
  Scheduled sched a        = ScheduleOutput sched a -> ()

reprIsBody :: forall sched t. GroundsR t -> (Scheduled sched t, IOFun t, FullIOFun t) :~: (ScheduleOutput sched t -> (), IO t, IO t)
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

type family IOFun f where
  IOFun (a -> b) = a -> IOFun b
  IOFun t        = IO t

type FullIOFun f = IO (FullIOFun' f)

type family FullIOFun' f where
  FullIOFun' (a -> b) = a -> FullIOFun b
  FullIOFun' t        = t

flattenIOFun :: GFunctionR f -> FullIOFun f -> IOFun f
flattenIOFun (GFunctionRlam _ funR) fun = \a -> flattenIOFun funR (join $ fun <*> pure a)
flattenIOFun (GFunctionRbody tp)    fun
  | Refl <- reprIsBody tp = fun

unsafePerformIOFun :: GFunctionR f -> IOFun f -> f
unsafePerformIOFun (GFunctionRlam _ funR) fun = unsafePerformIOFun funR . fun
unsafePerformIOFun (GFunctionRbody tp)    body
  | Refl <- reprIsBody tp = unsafePerformIO body

generateKernelNameAndDescription
  -- Function that gives the priority, singular name and plural name of an
  -- operation. The operations with highest priority are used in the name.
  :: (forall s. op s -> (Int, String, String))
  -> Clustered op t
  -- Returns a function name, a detailed description and a brief description
  -> (String, String, String)
generateKernelNameAndDescription f cluster =
  ( formatList False "_" "_" (take 2 sorted) ++ (if length sorted > 2 then "_etc" else "")
  , if trivial then "" else "Cluster with " ++
      formatList True ", then " (if length grouped == 2 then " and then " else " and finally ") (groupAndCount ops)
  , if trivial then "" else "Cluster with " ++
      formatList True ", " " and " sorted
  )
  where
    trivial 
      | [_] <- ops = True
      | otherwise  = False

    ops = map (\(Exists op) -> f op) $ flattenClustered cluster
    grouped = groupAndCount ops
    sorted = groupAndCount $ sortOn Down $ ops

    groupAndCount :: Eq a => [a] -> [(a, Int)]
    groupAndCount = map g . group
      where
        g [] = error "impossible"
        g as@(a:_) = (a, length as)
    
    formatList :: Bool -> String -> String -> [((Int, String, String), Int)] -> String
    formatList includeNumber separator finalSeparator list = case list of
      [] -> ""
      [a] -> formatItem includeNumber a
      [a, b] -> formatItem includeNumber a ++ finalSeparator ++ formatItem includeNumber b
      (a:as) -> formatItem includeNumber a ++ separator ++ formatList includeNumber separator finalSeparator as

    formatItem :: Bool -> ((Int, String, String), Int) -> String
    formatItem includeNumber ((_, singular, plural), count)
      | includeNumber = show count ++ " " ++ name
      | otherwise = name
      where
        name
          | count == 1 = singular
          | otherwise  = plural
