{-|
Module      : Control.Effect.Concurrency.Types
Description : Common definitions for modules around the concurrency effect
License     : BSD-3-Clause
Maintainer  : Zhixuan Yang
Stability   : experimental

This module provides some shared definitions around the effect of concurrency.
-}

{-# LANGUAGE TemplateHaskell #-}

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

$(makeGen [e| act :: forall a. a -> () |])
-- Generated smart constructor has type:
-- @
-- act :: Member (Act a) sig => a -> Prog sig ()
-- @

$(makeScp [e| par :: 2 |])

-- | The signature for joined parallel composition.
type JPar = Distr JPar_
-- | The underlying first-order signature for joined parallel composition.
data JPar_ x = JPar_ x x deriving (Functor, Foldable, Traversable)

-- | Run two processes @l@ and @r@ in parallel and join them, returning the results from
-- both of them.
-- Note that `jpar` is not a scoped operation but a distributive operation, so it
-- is harder to forward along monad transformers compared to `par`. It is recommended
-- to use `par` if possible.
{-# INLINE jpar #-}
jpar :: Member JPar sig => Prog sig x -> Prog sig x -> Prog sig (x, x)
jpar l r = call (Distr (JPar_ l r) (\(JPar_ x y) -> (x , y)))

pattern JPar x y k <- (prj -> Just (Distr (JPar_ x y) k)) where
  JPar x y k = inj (Distr (JPar_ x y) k)

-- | The process @res a p@ acts like @p@ except that @p@ cannot communicate with the
-- external environment via action @a@ (@p@ can still use @a@ internally), so @res a@ is like
-- a firewall blocking action @a@.
$(makeScp [e| res :: forall a. a -> 1 |])

instance Unary (Res_ a) where
  get (Res_ a x) = x