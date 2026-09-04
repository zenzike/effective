{-|
Module      : Control.Effect.Yield
Description : Simple bipartite coroutines
License     : BSD-3-Clause
Maintainer  : Zhixuan Yang
Stability   : experimental

This module provides a simple interface for coroutines. There is an algebraic
operation @Yield a b@ for producing an @a@-value and waiting for a @b@-value to
resume. The handler `pingpongWith` handles @Yield a b@ by running the program
against another program of effects @Yield b a@. There is also a scoped operation
@mapYield f g@ which applies the functions @f :: a -> a@ and @g :: b -> b@
to transform the values exchanged between the coroutines.

If the communication pattern of @Yield@ is too restrictive, you may need the
concurrency effects from the module "Control.Effect.Concurrency", which implements
an interface of concurrency in the style of /calculus of communicating systems/.
-}
{-# LANGUAGE DataKinds, MonoLocalBinds, CPP #-}

module Control.Effect.Yield where

import Control.Effect
import Control.Monad.Trans.YRes
import Data.Functor.Unary
import Data.List.Kind
import qualified Control.Monad.Trans.YRes as Y

$(makeGen [e| yield :: forall a b. a ~> b |])

$(makeScp [e| mapYield :: forall a b. (a -> a) -> (b -> b) ~> 1 |])

instance Unary (MapYield_ a b) where
  get (MapYield_ a b x) = x

yieldAlg :: Monad m => Algebra '[Yield a b, MapYield a b] (YResT a b m)
yieldAlg =
  (\(Yield a k) -> Y.yield a (fmap return k)) :#.
  (\(MapYield f g k) -> Y.mapYield f g k)

yieldAT :: AlgTrans '[Yield a b, MapYield a b] '[] '[YResT a b] Monad
yieldAT = AlgTrans (\_ -> yieldAlg)

-- | Handling @Yield a b@ and @MapYield a b@ by running the program against
-- a \'dual coroutine\' that produces effects @Yield b a@ and @MapYield b a@.
-- If the dual coroutine finishes first, the final return value is @Left _ :: Either y c@.
-- Conversely, if the handled program finishes first, the final return value is @Right _ :: Either y c@.
pingpongWith
  :: forall oeffs a b c y.
     (ForwardsM oeffs '[YResT b a])
  => (a -> Prog ('[Yield b a, MapYield b a] :++ oeffs) y)    -- ^ the dual coroutine
  -> Handler '[Yield a b, MapYield a b] oeffs '[YResT a b] c (Either y c)
pingpongWith q = handler run (\_ -> yieldAlg) where
  run :: forall m.  Monad m => Algebra oeffs m -> (YResT a b m c -> m (Either y c))
  run oalg p = pingpong p (eval (yieldAlg # getAT (fwds @oeffs @'[YResT b a]) oalg) . q)