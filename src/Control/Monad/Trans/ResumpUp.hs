{-|
Module      : Control.Monad.Trans.ResumpUp
Description : Resumption monad transformer
License     : BSD-3-Clause
Maintainer  : Zhixuan Yang
Stability   : experimental

This module contains the monad transformer to be used at the meta level to 
the resumption monad transformers.  
-}

{-# LANGUAGE TemplateHaskell #-}
module Control.Monad.Trans.ResumpUp where

import Control.Effect.CodeGen.Type ( Up )
import Control.Monad ( ap, liftM, MonadPlus (..) )
import Control.Monad.Trans.Class
import Control.Monad.Trans.YRes 
import Control.Monad.Trans.CRes 
import Control.Applicative

-- | @ResUpT@ is a Church-encoded version of the resumption monad transformer `ResT`
-- from "Control.Monad.Trans.Resump" with the restriction that the final answer
-- type must be code. This monad transformer is used for staging resumption
-- monads with the code-generation effect in "Control.Effect.CodeGen". 
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

-- | Perform an @l@-action and resumes as the @ResUpT l n a@ wrapped in the functor @l@.
resUpOp :: Functor l => l (ResUpT l n a) -> ResUpT l n a
resUpOp l = ResUpT $ \k1 k2 -> k2 (fmap (\p -> runResUpT p k1 k2) l)

instance MonadTrans (ResUpT l) where
  lift m = ResUpT $ \k1 k2 -> m >>= k1

-- | The resumption monad for yield-based coroutine.
type YResUpT a b = ResUpT (YStep a b) 

-- | Yield an @a@-value and wait for an @b@-value.
yield :: a -> (b -> YResUpT a b n x) -> YResUpT a b n x
yield a k = resUpOp (YieldS a k)

-- | @mapYieldUp f g p@ is a coroutine that behaves like @p@ except that the values
-- sent and received are processed by @f@ and @g@ respectively.
mapYield :: (a -> a') -> (b' -> b) -> YResUpT a b n x -> YResUpT a' b' n x
mapYield f g p = ResUpT $ \k1 k2 ->
  runResUpT p k1 (\(YieldS a k) -> k2 (YieldS (f a) (k . g)))

-- | The resumption monad for nondeterminism-based concurrency.
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

-- Perform an @a@-action and continue as the given process.
prefix :: a -> ResUpT (CStep a) n x -> ResUpT (CStep a) n x
prefix a p = resUpOp (ActS a p)