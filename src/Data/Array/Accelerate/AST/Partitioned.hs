{-# LANGUAGE BangPatterns          #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}

-- |
-- Module      : Data.Array.Accelerate.AST.Partitioned
-- Copyright   : [2008..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--
module Data.Array.Accelerate.AST.Partitioned
  ( module Data.Array.Accelerate.AST.Operation
  , Cluster(..), Combine(..)
  , PartitionedAcc, PartitionedAfun
  , SwapArgs(..), Take(..)
  ) where

import Data.Array.Accelerate.AST.Operation

import Control.Category ( Category(..) )
import Prelude hiding (id, (.))

type PartitionedAcc  op = PreOpenAcc  (Cluster op)
type PartitionedAfun op = PreOpenAfun (Cluster op)

-- data Cluster op args where
--   Leaf :: op args -> Cluster op args
--   ConsCluster :: op a'
--               -> SwapArgs a' a
--               -> Combine     a b c
--               -> Cluster op    b
--               -> Cluster op      c

-- | These definitions are far from guaranteeing a unique representation;
-- there are many equivalent ways to represent a clustering, even ignoring
-- the ambiguity in SwapArgs (where you can make many convoluted versions
-- of `id`). I don't think this is a big deal, but since it seems to always
-- be possible to construct a Cluster by appending a single element at a time,
-- it might be better to refactor this into a pseudo list (instead of binary tree).
-- Even then, every topologically sorted order will be a valid sequence.
data Cluster op args where
  -- Currently, we only swap the order of the arguments at the leaves. 
  -- This is needed to be able to horizontally fuse (x -> y -> a) with (y -> x -> a).
  -- I think it is also sufficient to do it only at leaves, and not in every node.
  -- Maybe putting it in the nodes will turn out to be easier though!
  Leaf :: op args'
       -> SwapArgs args args'
       -> Cluster op args

  -- Fuse two clusters.
  Branch :: Cluster op a
         -> Cluster op   b
         -> Combine    a b c
         -> Cluster op     c

-- Note that, in general, these combination descriptors can definitely represent
-- undesirable states: It's probably not doable to encode all fusability rules
-- in the types (especially while abstracting over backends), instead we will need
-- to call `error "impossible fusion"` in the backends at some points (particularly codegen).

-- | All these options will, in general, require the underlying Clusters to be weakened
-- by adding superfluous Args. The constructors below are the only way to "remove Args".
data Combine left right result where
  Combine :: Combine () () ()
  -- An array is produced and consumed, fusing it away.
  -- NOTE: this means that the array does not appear in the environment, and
  -- it does not have an accompanying `Arg` constructor: Its scope is now
  -- bound by this `Node` constructor in `Cluster`.
  Vertical  :: Combine              a              b               c
            -> Combine (Out sh e -> a) (In sh e -> b)              c

  -- Like vertical, but the arg is stored for later use
  Diagonal  :: Combine              a              b               c
            -> Combine (Out sh e -> a) (In sh e -> b) (Out sh e -> c)

  -- Both computations use the argument in the same fashion.
  -- Note that you can't recreate this type using WeakLeft and WeakRight,
  -- as that would duplicate the argument in the resulting type.
  -- Note also that it doesn't make too much sense to horizontally fuse output arguments.
  Horizontal :: Combine       a        b        c
             -> Combine (In sh e -> a) (In sh e -> b) (In sh e -> c)

  -- Only the right computation uses x, so this 'weakens' the left computation
  WeakLeftI  :: Combine              a              b               c
             -> Combine              a (In sh e  -> b) (In sh e  -> c)
  -- Mirror of WeakLeft
  WeakRightI :: Combine              a              b               c
             -> Combine (In sh e  -> a)             b  (In sh e  -> c)

  WeakLeftO  :: Combine              a              b               c
             -> Combine              a (Out sh e -> b) (Out sh e -> c)

  WeakRightO :: Combine              a              b               c
             -> Combine (Out sh e -> a)             b  (Out sh e -> c)

-- Re-order the type level arguments, to align them for the fusion constructors.
data SwapArgs a b where
  -- no swapping, base case
  Start :: SwapArgs a a
  -- put x on top of a recursive swap
  Swap  :: SwapArgs a xb
        -> Take x xb b
        -> SwapArgs a (x -> b)

-- neat, but is it actually useful?
instance Category SwapArgs where 
  id  = Start
  (.) = flip composeSwap

data Take x xa a where
  -- base case
  Here  :: Take x (x -> a) a
  -- recursive case
  There :: Take x       xa        a
        -> Take x (y -> xa) (y -> a)

composeSwap :: forall a b c. SwapArgs a b -> SwapArgs b c -> SwapArgs a c
composeSwap x = go
  where go :: SwapArgs b x -> SwapArgs a x
        -- If the second SwapArgs is identity, return x
        go Start = x
        -- Otherwise, the second SwapArgs puts something in front.
        -- Recurse, then wrap that in a Swap which puts the same thing in front!
        go (Swap a b) = Swap (go a) b

-- Alternative SwapArgs constructors:

  -- Start' :: SwapArgs () ()
  
  -- Dig   :: SwapArgs       a        b 
  --       -> SwapArgs (x -> a) (x -> b)
  
  -- SSwap :: SwapArgs a b 
  --       -> SwapArgs   b c 
  --       -> SwapArgs a   c
  
  -- Swap  :: SwapArgs a (x -> y -> z)
  --       -> SwapArgs a (y -> x -> z)
  
  -- Swap' :: Take x xa a
  --       -> SwapArgs xa (x -> a)

