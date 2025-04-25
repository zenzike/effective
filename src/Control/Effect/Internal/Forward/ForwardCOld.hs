{-|
Module      : Control.Effect.Internal.Forward.ForwardC
Description : Forwarding algebras
License     : BSD-3-Clause
Maintainer  : Nicolas Wu, Zhixuan Yang
Stability   : experimental
-}

{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE GADTs #-}
{-# OPTIONS_HADDOCK ignore-exports #-}

module Control.Effect.Internal.Forward.ForwardC
  ( ForwardC (..)
  , ForwardsC (..)
  ) where

import Control.Effect.Internal.Handler.Type
import Control.Effect.Internal.Effs

import Data.Kind ( Type )
import Data.HFunctor
#ifdef INDEXED
import Data.List.Kind
import GHC.TypeNats
#endif
import Control.Monad.Trans.Identity
import Control.Monad.Trans.Compose
import Unsafe.Coerce

-- | The class demonstrating that an effect @eff@ on every type constructor satisfying @cs@
-- can be forwarded through a transformer @t@.
class ForwardC cs (eff :: Effect) (t :: (Type -> Type) -> (Type -> Type)) where
  -- | @fwdC alg@ is a higher-order @eff@ algebra with carrier @m@ satisfying @cs@ that will
  -- create an @eff@ algebra with carrier @t m@.
  fwdC :: forall m . cs m
       => (forall x . eff m x  -> m x)
       -> (forall x . eff (t m) x -> t m x)

-- | This class builds a forwarder for an t`Effs` by recursion over @effs@,
-- by ensuring that each effect can be forwarded through a given @t@.
class ForwardEffsC cs effs (t :: (Type -> Type) -> (Type -> Type))  where
  fwdEffsC :: AlgTrans effs effs t cs

instance ForwardEffsC cs '[] t where
  {-# INLINE fwdEffsC #-}
  fwdEffsC :: AlgTrans '[] '[] t cs 
  fwdEffsC = AlgTrans $ \_ -> absurdEffs

instance ( HFunctor eff, ForwardC cs eff t, ForwardEffsC cs effs t 
#ifdef INDEXED
         , KnownNat (Length effs), KnownNat (1 + Length effs)
#endif
  ) 
         => ForwardEffsC cs (eff ': effs) t where

  {-# INLINE fwdEffsC #-}
  fwdEffsC :: AlgTrans (eff ': effs) (eff ': effs) t cs
  fwdEffsC = AlgTrans $ \alg -> \case
    (Eff op)   -> fwdC @cs (alg . Eff) op
    (Effs ops) -> getAT (fwdEffsC @cs)  (alg . Effs) ops


-- | `ForwardsC` is a synonym of `ForwardEffsC` and it is created solely for guiding the instance 
-- resolution of Haskell. Users of the library should always use @Forwards@.
-- 
-- In more detail, if the instances for @IdentityT@ and @ComposeT@ below were written as instances 
-- of `ForwardEffsC`, they would overlap with the instance of @ForwardEffs cs (eff ': effs) t@
-- for @ForwardEffsC cs (eff ': effs) IdentityT@. By creating a new typeclass, we essentially instruct
-- GHC to first recur on the transformer argument and then the effect argument.
class ForwardsC cs effs t where
  fwdsC :: AlgTrans effs effs t cs 

instance ForwardEffsC cs effs t => ForwardsC cs effs t where
  {-# INLINE fwdsC #-}
  fwdsC :: AlgTrans effs effs t cs 
  fwdsC = fwdEffsC @cs

instance {-# OVERLAPS #-} 
  ForwardsC cs effs IdentityT where
  {-# INLINE fwdsC #-}
  fwdsC :: AlgTrans effs effs IdentityT cs
  fwdsC = AlgTrans $ \(alg :: Algebra effs m) -> 
    IdentityT . alg . unsafeCoerce @(Effs effs (IdentityT m) _) @(Effs effs m _)

instance {-# OVERLAPS #-} 
  ( forall m. cs m => cs (t1 m)
  , forall m. cs m => cs (t2 m)
  , forall m. cs (t1 (t2 m)) => cs (ComposeT t1 t2 m)
  , ForwardEffsC cs effs t1
  , ForwardsC cs effs t2
  , HFunctor (Effs effs)
  )
  => ForwardsC cs effs (ComposeT t1 t2) where
  {-# INLINE fwdsC #-}
  fwdsC :: AlgTrans effs effs (ComposeT t1 t2) cs
  fwdsC = AlgTrans $ \(alg :: Algebra effs m) x -> 
       ComposeT
     . getAT (fwdEffsC @cs) (getAT (fwdsC @cs) alg) 
     . unsafeCoerce @(Effs effs (ComposeT t1 t2 m) _) @(Effs effs (t1 (t2 m)) _)
     $ x