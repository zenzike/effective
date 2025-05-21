{-# LANGUAGE TemplateHaskell #-}
module Control.Monad.Trans.ResUp where

import Control.Effect.CodeGen.Type ( Up )
import Control.Monad ( ap, liftM, MonadPlus (..) )
import Control.Monad.Trans.Class
import Control.Monad.Trans.YRes 
import Control.Monad.Trans.CRes 
import Control.Applicative

newtype ResUpT l n a = ResUpT 
  { runResUpT :: forall t. (a -> n (Up t)) -> (l (n (Up t)) -> n (Up t)) -> n (Up t) }

instance Functor (ResUpT l n) where
  fmap = liftM

instance Applicative (ResUpT l n) where
  pure x = ResUpT $ \k1 k2 -> k1 x
  (<*>)  = ap

instance Monad (ResUpT l n) where
  p >>= k = ResUpT $ \k1 k2 -> 
    runResUpT p (\a -> runResUpT (k a) k1 k2) k2 

resUpOp :: Functor l => l (ResUpT l n a) -> ResUpT l n a
resUpOp l = ResUpT $ \k1 k2 -> k2 (fmap (\p -> runResUpT p k1 k2) l)

instance MonadTrans (ResUpT l) where
  lift m = ResUpT $ \k1 k2 -> m >>= k1

type YResUpT a b = ResUpT (YStep a b) 

yieldUp :: a -> (b -> YResUpT a b n x) -> YResUpT a b n x
yieldUp a k = resUpOp (YieldS a k)

mapYieldUp :: (a -> a) -> (b -> b) -> YResUpT a b n x -> YResUpT a b n x
mapYieldUp f g p = ResUpT $ \k1 k2 ->
  runResUpT p k1 (\(YieldS a k) -> k2 (YieldS (f a) (k . g)))

-- * Concurrency

type CResUpT a = ResUpT (CStep a) 

instance Monad m => Alternative (CResUpT a m) where
  {-# INLINE empty #-}
  empty = resUpOp FailS

  {-# INLINE (<|>) #-}
  mxs <|> mys = resUpOp (ChoiceS mxs mys)

instance Monad m => MonadPlus (CResUpT a m) where
  {-# INLINE mzero #-}
  mzero = empty

  {-# INLINE mplus #-}
  mplus = (<|>)

prefix :: a -> ResUpT (CStep a) n x -> ResUpT (CStep a) n x
prefix a p = resUpOp (ActS a p)