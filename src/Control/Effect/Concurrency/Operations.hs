{-|
Module      : Control.Effect.Concurrency.Operations
Description : The operations for the concurrency effect
License     : BSD-3-Clause
Maintainer  : Zhixuan Yang
Stability   : experimental

This module contains the operations for the effect of concurrency (in the style
of process calculi). We have the following operations:

  1. an algebraic operation @`act` :: a ~> ()@ for performing an operation
  2. a binary scoped operation @`par`@ for running two processes in parallel
  3. a unary scoped operation @`res` a@ with a parameter @a@ for restricting
     the action @a@ in the scope.

Any type @a@ satisfying the constraint `Action a` can be used as the type of
action.  This typeclass has exactly one member @`merge` :: a -> a -> Maybe a@,
which returns @Nothing@ if the two actions cannot synchronise and returns @Just
a'@ if the two arguments can synchronise and produce the action @a'@ together.

A canonical choice of the type of actions is `CCSAction`, in which an action can
only synchronise with its dual action, producing a silent action together.
This is exactly how /calculus of communication systems/ works.

Currently this module doesn't have an operation for passing values between
processes. This may change in the future, but for now you can use an @IORef@ for
sending/receiving values between processes and use the operations of this module
to structure their synchronisation.
-}

{-# LANGUAGE TemplateHaskell #-}

module Control.Effect.Concurrency.Operations where

import Data.Functor.Unary
import Control.Effect.Family.Distributive
import Control.Effect

-- * Types of actions

-- | A typeclass for types that can serve as actions in the style
-- of _algebra of communicating processes_ (ACP).
class Eq a => Action a where
  -- `merge a b = Nothing` means the two actions `a` and `b` don't interact
  merge :: a -> a -> Maybe a

-- | Asymmetric actions in the style of Calculus for Communicating Systems (CCS)
-- The silent action stores the name of a completed internal action for debugging purposes.
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

$(makeGen [e| act :: forall a. a ~> () |])
-- Generated smart constructor has type:
-- @
-- act :: Member (Act a) effs => a -> Prog effs ()
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
jpar :: Member JPar effs => Prog effs x -> Prog effs x -> Prog effs (x, x)
jpar l r = call (Distr (JPar_ l r) (\(JPar_ x y) -> (x , y)))

{-# INLINE jparM #-}
jparM :: Member JPar effs => Algebra effs m -> m x -> m x -> m (x, x)
jparM alg l r = callM alg (Distr (JPar_ l r) (\(JPar_ x y) -> (x , y)))

{-# INLINE jparP #-}
jparP :: Member (n :@ JPar) effs => Proxy n -> Prog effs x -> Prog effs x -> Prog effs (x, x)
jparP p l r = callP p (Distr (JPar_ l r) (\(JPar_ x y) -> (x , y)))

#if MIN_VERSION_GLASGOW_HASKELL(9,10,1,0)
{-# INLINE jparN #-}
jparN :: forall n -> Member (n :@ JPar) effs => Prog effs x -> Prog effs x -> Prog effs (x, x)
jparN n l r = callN n (Distr (JPar_ l r) (\(JPar_ x y) -> (x , y)))
#endif

pattern JPar x y k = Distr (JPar_ x y) k

-- | The process @res a p@ acts like @p@ except that @p@ cannot communicate with the
-- external environment via action @a@ (@p@ can still use @a@ internally), so @res a@ is like
-- a firewall blocking action @a@.
$(makeScp [e| res :: forall a. a ~> 1 |])

instance Unary (Res_ a) where
  get (Res_ a x) = x
