{-|
Module      : Control.Effect.Internal.Handler.Forward
Description : Forwarding algebras
License     : BSD-3-Clause
Maintainer  : Nicolas Wu
Stability   : experimental
-}

{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE GADTs #-}
{-# OPTIONS_HADDOCK ignore-exports #-}

module Control.Effect.Internal.Handler.Forward 
  ( Forward (..)
  , Forwards (..)
  ) where

import Control.Effect.Internal.Handler.Type
import Control.Effect.Internal.Effs

import Data.Kind ( Type )
import Data.HFunctor
import Data.List.Kind
import GHC.TypeNats
import Control.Monad.Trans.Identity
import Control.Monad.Trans.Compose

-- | The class demonstrating that an effect @eff@ can be forwarded through a transformer @t@.
class Forward cs (eff :: Effect) (t :: Effect) where
  -- | @fwd alg@ is a higher-order @eff@ algebra with carrier @m@ satisfying @cs@ that will
  -- create an @eff@ algebra with carrier @t m@.
  fwd :: forall m . cs m
      => (forall x . eff m x  -> m x)
      -> (forall x . eff (t m) x -> t m x)

-- | This class builds a forwarder for an t`Effs` by recursion over @effs@,
-- by ensuring that each effect can be forwarded through a given @t@.
class ForwardEffs cs effs (t :: (Type -> Type) -> (Type -> Type))  where
  fwdEffs :: AlgTrans effs effs t cs

instance ForwardEffs cs '[] t where
  {-# INLINE fwdEffs #-}
  fwdEffs :: AlgTrans '[] '[] t cs 
  fwdEffs = AlgTrans $ \_ -> absurdEffs

instance ( HFunctor eff, Forward cs eff t, ForwardEffs cs effs t
         , KnownNat (Length effs), KnownNat (1 + Length effs)) 
         => ForwardEffs cs (eff ': effs) t where
  {-# INLINE fwdEffs #-}
  fwdEffs :: AlgTrans (eff ': effs) (eff ': effs) t cs
  fwdEffs = AlgTrans $ \alg -> \case
    (Eff op)   -> fwd @cs (alg . Eff) op
    (Effs ops) -> getAT (fwdEffs @cs)  (alg . Effs) ops


-- | `Forwards` is a synonym of `ForwardEffs` and it is created solely for guiding the instance 
-- resolution of Haskell. Users of the library should always use @Forwards@.
-- 
-- In more detail, if the instances for @IdentityT@ and @ComposeT@ below were written as instances 
-- of `ForwardEffs`, they would overlap with the instance of @ForwardEffs cs (eff ': effs) t@
-- for @ForwardEffs cs (eff ': effs) IdentityT@. By creating a new typeclass, we essentially instruct
-- GHC to first recur on the transformer argument and then the effect argument.
class Forwards cs effs t where
  fwds :: AlgTrans effs effs t cs 

instance ForwardEffs cs effs t => Forwards cs effs t where
  {-# INLINE fwds #-}
  fwds :: AlgTrans effs effs t cs 
  fwds = fwdEffs @cs

instance {-# OVERLAPS #-} 
  ( HFunctor (Effs effs)
  , forall m . cs m => Functor m
  , forall m . cs m => cs (IdentityT m)
  ) 
  => Forwards cs effs IdentityT where
  {-# INLINE fwds #-}
  fwds :: AlgTrans effs effs IdentityT cs
  fwds = AlgTrans $ \alg -> IdentityT . alg . hmap runIdentityT

instance {-# OVERLAPS #-} 
  ( forall m. cs m => cs (t1 m)
  , forall m. cs m => cs (t2 m)
  , forall m. cs m => Functor m
  , forall m. cs (t1 (t2 m)) => cs (ComposeT t1 t2 m)
  , ForwardEffs cs effs t1
  , Forwards cs effs t2
  , HFunctor (Effs effs)
  )
  => Forwards cs effs (ComposeT t1 t2) where
  {-# INLINE fwds #-}
  fwds :: AlgTrans effs effs (ComposeT t1 t2) cs
  fwds = AlgTrans $ \alg x -> ComposeT . getAT (fwdEffs @cs) (getAT (fwds @cs) alg) . hmap getComposeT $ x