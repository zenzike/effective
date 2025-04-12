module Control.Effect.Concurrency.Types where

import Data.Functor.Unary
import Control.Effect.Algebraic
import Control.Effect.Scoped
import Control.Effect.Distributive
import Control.Effect

-- | A typeclass for types that can serve as actions in the style
-- of _algebra of communicating processes_ (ACP). 
class Eq a => Action a where
  -- `merge a b = Nothing` means the two actions `a` and `b` don't interact
  merge :: a -> a -> Maybe a

-- | Asymmetric actions in the style of Calculus for Communicating Systems (CCS)
data CCSAction a = Silent a | Action a | CoAction a deriving (Show, Eq, Ord)

instance Eq a => Action (CCSAction a) where
  merge (Action a) (CoAction b)
    | a == b    = Just (Silent a)
    | otherwise = Nothing
  merge (CoAction a) (Action b)
    | a == b    = Just (Silent a)
    | otherwise = Nothing
  merge _ _ = Nothing

dualAction :: CCSAction a -> CCSAction a
dualAction (Action a)   = CoAction a
dualAction (CoAction a) = Action a 
dualAction (Silent a)   = Silent a

getActionName :: CCSAction a -> a
getActionName (Silent a)   = a
getActionName (Action a)   = a
getActionName (CoAction a) = a

type Act a = Alg (Act_ a)
data Act_ a x = Act a x deriving Functor 

{-# INLINE act #-}
act :: Member (Act a) sig => a -> Prog sig ()
act a = call' (Alg (Act a ()))

type Par = Scp Par_
data Par_ x = Par x x deriving Functor

{-# INLINE par #-}
par :: Member Par sig => Prog sig x -> Prog sig x -> Prog sig x
par l r = call' (Scp (Par l r))

type JPar = Distr JPar_
data JPar_ x = JPar x x deriving (Functor, Foldable, Traversable)

-- | @jpar l r@ executes the two programs @l@ and @r@ in parallel and join them,
-- returning the results from both of them.
-- Note that `jpar` is not a scoped operation but a distributive operation, so it
-- is harder to forward along monad transformers compared to `par`. It is recommended
-- to use `par` if possible.
{-# INLINE jpar #-}
jpar :: Member JPar sig => Prog sig x -> Prog sig x -> Prog sig (x, x)
jpar l r = call' (Distr (JPar l r) (\(JPar x y) -> (x , y)))

type Res a = Scp (Res_ a)
data Res_ a x = Res a x deriving Functor

{-# INLINE res #-}
res :: Member (Res a) sig => a -> Prog sig x -> Prog sig x
res a p = call' (Scp (Res a p))

instance Unary (Res_ a) where
  get (Res a x) = x