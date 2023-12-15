{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
module Control.Family.FusedSig where

import Control.Family.Base
import Control.Effects

data Lan g h a where
  Lan :: (g b -> a) -> h b -> Lan g h a

data FusedSig sig m a where
  FusedSig :: (forall x . ctx (n x) -> m (ctx x))
           -> ctx ()
           -> sig n a
           -> FusedSig sig m a
-- FusedSig sig m a -> m a
--  is in bijection with
-- alg :: forall ctx n . (forall x . ctx (n x) -> m (ctx x)) -> ctx () -> sig n a -> m (ctx a)

class Fused sig where
  type JFus sig :: Effect
  fproject :: sig f a -> FusedSig (JFus sig) f a

