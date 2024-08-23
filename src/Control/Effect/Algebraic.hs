{-|
Module      : Control.Effect.Algebraic
Description : The algebraic effect family
License     : BSD-3-Clause
Maintainer  : Nicolas Wu
Stability   : experimental
-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MonoLocalBinds #-}

module Control.Effect.Algebraic where

import Control.Effect

import Data.Kind ( Type )
import Data.HFunctor
import Control.Monad.Trans.Class

-- | The family of algebraic operations. These satisfy the algebraicity property,
-- which says that:
--
-- > call (Alg op) >>= k  ==  call (Alg (op >>= k))
--
-- Operations of this form are automatically lifted through any monad transformer.
-- This is witnessed by the @Forward@ instance.
--
-- The @sig@ parameter is the signature type, @f@ corresponds to the semantics
-- carrier, and @k@ is the continuation parameter.
-- newtype Alg (sig :: Type -> Type)
--             (f :: Type -> Type)
--             k
--             = Alg (sig k)
--
newtype Alg (sig :: Type -> Type)
         (f :: Type -> Type)
         k
         = Alg (sig k)

instance Functor sig => Functor (Alg sig f) where
  {-# INLINE fmap #-}
  fmap f (Alg op) = Alg (fmap f op)

instance Functor sig => HFunctor (Alg sig) where
  {-# INLINE hmap #-}
  hmap f (Alg op) = Alg op

instance (MonadTrans t) => Forward (Alg f) t where
  {-# INLINE fwd #-}
  fwd alg (Alg op) = lift (alg (Alg op))
