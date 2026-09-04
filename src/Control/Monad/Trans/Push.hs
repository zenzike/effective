{-|
Module      : Control.Monad.Trans.Push
Description : Monad Transformer for staging nondeterminism
License     : BSD-3-Clause
Maintainer  : Zhixuan Yang
Stability   : experimental
-}

{-# LANGUAGE TemplateHaskell #-}
module Control.Monad.Trans.Push where

import Control.Applicative ( Alternative(empty, (<|>)) )
import Control.Monad ( ap, liftM )
import Control.Monad.Trans.Class ( MonadTrans(..) )
import Language.Haskell.TH ( CodeQ )

-- | @PushT@ is a Church-encoded version of @ListT@ with the restriction that the final
-- answer type must be code. This monad transformer is used for staging nondeterminism
-- with the code-generation effect in "Control.Effect.CodeGen".
-- The monad @PushT n a@ supports the operations of nondeterminism just like @ListT@,
-- and it additionally supports the following two operations (defined in "Control.Effect.CodeGen.CodeQ"
-- and "Control.Effect.CodeGen.Down"):
--
-- > down :: PushT n (CodeQ a) -> CodeQ (ListT m a)
-- > up   :: CodeQ (ListT m a) -> PushT n (CodeQ a)
--
-- for converting between meta-level and object-level nondeterministic programs.
newtype PushT n a = PushT
  { runPushT :: forall t.
                (a -> n (CodeQ t) -> n (CodeQ t))  -- ^ The continuation for cons
             -> n (CodeQ t)                        -- ^ The continuation for nil
             -> n (CodeQ t) }

instance Functor (PushT m) where
  fmap = liftM

instance Applicative (PushT m) where
  pure x = PushT $ \c n -> c x n
  (<*>) = ap

instance Monad (PushT m) where
  p >>= k = PushT $ \c n -> runPushT p (\a as -> runPushT (k a) c as) n

instance Alternative (PushT m) where
  empty = PushT $ \_ n -> n

  p1 <|> p2 = PushT $ \c n -> runPushT p1 c (runPushT p2 c n)

instance MonadTrans PushT where
  lift ma = PushT $ \c n -> ma >>= (\a -> c a n)

-- | Keep only the first outcome.
once :: PushT m a -> PushT m a
once p = PushT $ \c n -> runPushT p (\a _ -> c a n) n