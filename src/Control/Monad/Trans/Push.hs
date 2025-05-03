{-# LANGUAGE TemplateHaskell #-}
module Control.Monad.Trans.Push where

import Control.Effect.CodeGen.Type ( Up )
import Control.Applicative ( Alternative(empty, (<|>)) )
import Control.Monad ( ap, liftM )
import Control.Monad.Trans.Class

newtype PushT n a = PushT { 
  runPushT :: forall t. (a -> n (Up t) -> n (Up t)) 
           -> n (Up t) -> n (Up t) }

instance Functor (PushT m) where
  fmap = liftM

instance Applicative (PushT m) where
  pure x = PushT $ \c n -> c x n
  (<*>) = ap

instance Monad (PushT m) where
  p >>= k = PushT $ \c n -> runPushT p (\a as -> runPushT (k a) c as) n

observeAll :: Applicative m => PushT m (Up a) -> m (Up [a])
observeAll p = runPushT p (\a -> fmap (\bs -> [|| $$a : $$bs ||])) (pure [|| [] ||])

instance Alternative (PushT m) where
  empty = PushT $ \_ n -> n

  p1 <|> p2 = PushT $ \c n -> runPushT p1 c (runPushT p2 c n)

instance MonadTrans PushT where
  lift ma = PushT $ \c n -> ma >>= (\a -> c a n)

once :: PushT m a -> PushT m a
once p = PushT $ \c n -> runPushT p (\a _ -> c a n) n
