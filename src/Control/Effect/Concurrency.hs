{-# LANGUAGE DataKinds #-}
module Control.Effect.Concurrency (
  module Control.Effect.Concurrency.Action,
  Control.Monad.Trans.CRes.ListActs (..),
  Control.Monad.Trans.CRes.ActsMb (..),
  Control.Monad.Trans.CRes.CResT (..),
  -- * Syntax
  -- ** Operations
  Control.Effect.Concurrency.par,
  Control.Effect.Concurrency.act,
  Control.Effect.Concurrency.res,

  -- ** Signatures
  Act, Act_(..),
  Par, Par_(..),
  Res, Res_(..),

  -- * Semantics
  -- ** Handlers
  resump,
  resumpWith
  ) where

import Control.Effect
import Control.Effect.Algebraic
import Control.Effect.Scoped
import Control.Effect.Concurrency.Action
import qualified Control.Monad.Trans.CRes as C
import Control.Monad.Trans.CRes 
import Data.Functor.Unary

type Act a = Alg (Act_ a)
data Act_ a x = Act a x deriving Functor 

{-# INLINE act #-}
act :: Member (Act a) sig => a -> Prog sig ()
act a = call (Alg (Act a (return ())))

type Par = Scp Par_
data Par_ x = Par x x deriving Functor

{-# INLINE par #-}
par :: Member Par sig => Prog sig x -> Prog sig x -> Prog sig x
par l r = call (Scp (Par (fmap return l) (fmap return r)))

type Res a = Scp (Res_ a)
data Res_ a x = Res a x deriving Functor

{-# INLINE res #-}
res :: Member (Res a) sig => a -> Prog sig x -> Prog sig x
res a p = call (Scp (Res a (fmap return p)))

instance Unary (Res_ a) where
  get (Res a x) = x



alg :: (Action a, Monad m) => Algebra '[] m -> Algebra '[Act a, Par, Res a] (C.CResT a m)
alg _ eff
  | Just (Alg (Act a p)) <- prj eff = prefix a (return p)
  | Just (Scp (Par l r)) <- prj eff = C.par l r
  | Just (Scp (Res a p)) <- prj eff = C.res a p

resump :: forall a. Action a => Handler '[Act a, Par, Res a] '[] (C.CResT a) (C.ListActs a) 
resump = handler runAll alg where
  alg :: Monad m => Algebra '[] m -> Algebra '[Act a, Par, Res a] (C.CResT a m)
  alg _ eff
    | Just (Alg (Act a p)) <- prj eff = prefix a (return p)
    | Just (Scp (Par l r)) <- prj eff = C.par l r
    | Just (Scp (Res a p)) <- prj eff = C.res a p

resumpWith :: forall a. Action a => [Bool] -> Handler '[Act a, Par, Res a] '[] (C.CResT a) (ActsMb a)
resumpWith choices = handler (runWith choices) alg

