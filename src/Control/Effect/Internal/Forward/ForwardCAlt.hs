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

module Control.Effect.Internal.Forward.ForwardCAlt
  ( ForwardC (..)
  , ForwardsC (..)
  ) where

import Control.Effect.Internal.Handler.TypeAlt
import Control.Effect.Internal.Effs

import Data.Kind ( Type )
import Data.HFunctor
#ifdef INDEXED
import Data.List.Kind
import GHC.TypeNats
#endif

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
  fwdEffsC :: AlgTrans effs effs '[t] cs

instance ForwardEffsC cs '[] t where
  {-# INLINE fwdEffsC #-}
  fwdEffsC :: AlgTrans '[] '[] '[t] cs 
  fwdEffsC = AlgTrans $ \_ -> absurdEffs

instance ( HFunctor eff, ForwardC cs eff t, ForwardEffsC cs effs t 
#ifdef INDEXED
         , KnownNat (Length effs), KnownNat (1 + Length effs)
#endif
  ) 
         => ForwardEffsC cs (eff ': effs) t where

  {-# INLINE fwdEffsC #-}
  fwdEffsC :: AlgTrans (eff ': effs) (eff ': effs) '[t] cs
  fwdEffsC = AlgTrans $ \alg -> \case
    (Eff op)   -> fwdC @cs @_ @t (alg . Eff) op
    (Effs ops) -> getAT (fwdEffsC @cs @_ @t)  (alg . Effs) ops


-- | `ForwardsC` forwards effects @effs@ along a list of carrier transformers.
class ForwardsC cs effs ts where
  fwdsC :: AlgTrans effs effs ts cs 

instance ForwardEffsC cs effs ts => ForwardsC cs effs '[ts] where
  {-# INLINE fwdsC #-}
  fwdsC :: AlgTrans effs effs '[ts] cs 
  fwdsC = fwdEffsC @cs

instance {-# OVERLAPS #-} ForwardsC cs effs '[] where
  {-# INLINE fwdsC #-}
  fwdsC :: AlgTrans effs effs '[] cs
  fwdsC = AlgTrans $ \alg  -> alg 

instance {-# OVERLAPS #-} 
  ( forall m. cs m => cs (Apply ts m)     
    -- ZY : In all other places I can't use non-injective type family @Apply@ in a quanfified
    -- constraint. I don't know why it works here.
  , ForwardEffsC cs effs t
  , ForwardsC cs effs ts )
  => ForwardsC cs effs (t ': ts) where
    {-# INLINE fwdsC #-}
    fwdsC :: AlgTrans effs effs (t ': ts) cs
    fwdsC = AlgTrans $ \(alg :: Algebra effs m) -> 
      getAT (fwdEffsC @cs @_ @t) (getAT (fwdsC @cs @_ @ts) alg)