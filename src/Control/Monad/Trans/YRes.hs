module Control.Monad.Trans.YRes (
  module Control.Monad.Trans.YRes,
  module Control.Monad.Trans.Resump
  ) where

import Control.Monad.Trans.Resump

-- | Step functor for yielding
data YStep a b x = YieldS a (b -> x) deriving Functor

-- | The monad @CResT m@ is the coproduct of the monad @m@ and the 
-- free monad over YStep. In other words, the algebraic theory
-- corresponding to @YResT m@ is the sum of the theory of @m@
-- plus an operation that takes in an @a@ value and produces a 
-- @b@-value.
type YResT a b = ResT (YStep a b)

yield :: Monad m => a -> (b -> YResT a b m x) -> YResT a b m x
yield a k = resOp (YieldS a k)

mapYield :: Monad m => (a -> a) -> (b -> b) -> YResT a b m x -> YResT a b m x
mapYield f g p = ResT $ 
  do xs <- unResT p
     case xs of
       Left x -> return (Left x)
       Right (YieldS a k) -> return (Right (YieldS (f a) (mapYield f g .  k . g))) 

-- | @pingpong p q@ runs the two coroutines @p@ and @q@ in the call and
-- response way until one of them finishes. The coroutine @p@ runs first.
pingpong :: Monad m => YResT a b m x -> (a -> YResT b a m y) -> m (Either y x)
pingpong p q =
  do xs <- unResT p
     case xs of 
      Left x -> return (Right x)
      Right (YieldS a k) -> pongping k (q a)

-- | @pongping p q@ runs the two coroutines @p@ and @q@ in the call and
-- response way until one of them finishes. The coroutine @q@ runs first.
pongping :: Monad m => (b -> YResT a b m x) -> YResT b a m y -> m (Either y x)
pongping p q = fmap swap $ pingpong q p where 
    swap :: Either x y -> Either y x
    swap (Left x) = Right x
    swap (Right y) = Left y