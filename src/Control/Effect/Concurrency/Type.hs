{-|
Module      : Control.Effect.Concurrency.Types
Description : Common definitions for modules around the concurrency effect
License     : BSD-3-Clause
Maintainer  : Zhixuan Yang
Stability   : experimental

This module provides some shared definitions around the effect of concurrency.
-}

module Control.Effect.Concurrency.Type where

import Data.Functor.Unary
import Control.Effect.Family.Algebraic
import Control.Effect.Family.Scoped
import Control.Effect.Family.Distributive
import Control.Effect

-- * Types of actions

-- | A typeclass for types that can serve as actions in the style
-- of _algebra of communicating processes_ (ACP). 
class Eq a => Action a where
  -- `merge a b = Nothing` means the two actions `a` and `b` don't interact
  merge :: a -> a -> Maybe a

-- | Asymmetric actions in the style of Calculus for Communicating Systems (CCS)
-- The silent action stores the name of completed internal action for debugging purposes.  
data CCSAction a = Silent a | Action a | CoAction a deriving (Show, Eq, Ord)

instance Eq a => Action (CCSAction a) where
  merge (Action a) (CoAction b)
    | a == b    = Just (Silent a)
    | otherwise = Nothing
  merge (CoAction a) (Action b)
    | a == b    = Just (Silent a)
    | otherwise = Nothing
  merge _ _ = Nothing

-- | The dual of a ccs action.
dualAction :: CCSAction a -> CCSAction a
dualAction (Action a)   = CoAction a
dualAction (CoAction a) = Action a 
dualAction (Silent a)   = Silent a

-- | Getting the name of a ccs action.
getActionName :: CCSAction a -> a
getActionName (Silent a)   = a
getActionName (Action a)   = a
getActionName (CoAction a) = a

-- * Effect signatures

-- | The signature for the operation of performaing an action (of type @a@).
type Act a = Alg (Act_ a)

-- | The underlying first-order signature for the operation of performaing an action (of type @a@).
data Act_ a x = Act a x deriving Functor 

-- | Perform an action of type @a@.
{-# INLINE act #-}
act :: Member (Act a) sig => a -> Prog sig ()
act a = call' (Alg (Act a ()))


-- | The signature for parallel composition.
type Par = Scp Par_

-- | The underlying first-order signature for parallel composition.
data Par_ x = Par x x deriving Functor

-- | Run two processes @l@ and @r@ in parallel.
{-# INLINE par #-}
par :: Member Par sig => Prog sig x -> Prog sig x -> Prog sig x
par l r = call' (Scp (Par l r))

-- | The signature for joined parallel composition.
type JPar = Distr JPar_
-- | The underlying first-order signature for joined parallel composition.
data JPar_ x = JPar x x deriving (Functor, Foldable, Traversable)

-- | Run two processes @l@ and @r@ in parallel and join them, returning the results from 
-- both of them.
-- Note that `jpar` is not a scoped operation but a distributive operation, so it
-- is harder to forward along monad transformers compared to `par`. It is recommended
-- to use `par` if possible.
{-# INLINE jpar #-}
jpar :: Member JPar sig => Prog sig x -> Prog sig x -> Prog sig (x, x)
jpar l r = call' (Distr (JPar l r) (\(JPar x y) -> (x , y)))

-- | The signature for action restriction.
type Res a = Scp (Res_ a)
-- | The underlying first-order signature for restriction.
data Res_ a x = Res a x deriving Functor

-- | The process @res a p@ acts like @p@ except that @p@ cannot communicate with the 
-- external environment via action @a@ (@p@ can still use @a@ internally), so @res a@ is like  
-- a firewall blocking action @a@.
{-# INLINE res #-}
res :: Member (Res a) sig => a -> Prog sig x -> Prog sig x
res a p = call' (Scp (Res a p))

instance Unary (Res_ a) where
  get (Res a x) = x