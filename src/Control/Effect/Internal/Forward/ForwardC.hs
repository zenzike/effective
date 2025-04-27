{-|
Module      : Control.Effect.Internal.Forward.ForwardC
Description : Default forwarding algebras
License     : BSD-3-Clause
Maintainer  : Nicolas Wu, Zhixuan Yang
Stability   : experimental

This module provides a class @ForwardsC cs effs ts@ that associates the transformer
stack @ts@ with an algebra transformer @`fwdsC` :: AlgTrans effs effs ts cs@ that is
expected to be 'the canonical way' to forward the effect @effs@ along @ts@.
-}

{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# OPTIONS_HADDOCK ignore-exports #-}

module Control.Effect.Internal.Forward.ForwardC
  ( ForwardC (..)
  , ForwardsC (..)
  , Forwards
  , fwds
  ) where

import Control.Effect.Internal.AlgTrans.Type
import Control.Effect.Internal.Effs

import Data.Kind 
import Data.HFunctor
#ifdef INDEXED
import GHC.TypeNats
#endif

-- | The class demonstrating that an effect @eff@ on every type constructor satisfying @cs@
-- can be forwarded through a transformer @t@.
-- This is a typeclass that is expected to be instantiated by the user of @effective@ for 
-- user-defined transformers @t@, but the user should /use/ the typeclass `ForwardsC`
-- that automatically deal with forwarding a list of effects along a list of transformers.
class ForwardC (eff :: Effect) (t :: (Type -> Type) -> (Type -> Type)) where
  type FwdConstraint eff t :: (Type -> Type) -> Constraint 

  -- | @fwdC alg@ is a higher-order @eff@ algebra with carrier @m@ satisfying @cs@ that will
  -- create an @eff@ algebra with carrier @t m@.
  fwdC :: forall m . FwdConstraint eff t m
       => (forall x . eff m x     -> m x)
       -> (forall x . eff (t m) x -> t m x)

-- | This class builds a forwarder for an t`Effs` by recursion over @effs@,
-- by ensuring that each effect can be forwarded through a given @t@.
-- This is an internal typeclass that the user of @effective@ don't need
-- to use explicitly.
class ForwardEffsC effs (t :: (Type -> Type) -> (Type -> Type))  where
  type FwdEffsConstraint effs t :: (Type -> Type) -> Constraint
  fwdEffsC :: AlgTrans effs effs '[t] (FwdEffsConstraint effs t)

instance ForwardEffsC '[] t where
  type FwdEffsConstraint '[] t = TruthC

  {-# INLINE fwdEffsC #-}
  fwdEffsC :: AlgTrans '[] '[] '[t] TruthC
  fwdEffsC = AlgTrans $ \_ -> absurdEffs

instance ( HFunctor eff
         , ForwardC eff t
         , ForwardEffsC effs t 
#ifdef INDEXED
         , KnownNat (Length effs), KnownNat (1 + Length effs)
#endif
         ) 
         => ForwardEffsC (eff ': effs) t where

  type FwdEffsConstraint (eff ': effs) t = AndC (FwdConstraint eff t) (FwdEffsConstraint effs t)

  {-# INLINE fwdEffsC #-}
  fwdEffsC :: AlgTrans (eff ': effs) (eff ': effs) '[t] (FwdEffsConstraint (eff ': effs) t)
  fwdEffsC = AlgTrans $ \alg -> \case
    (Eff op)   -> fwdC @_ @t (alg . Eff) op
    (Effs ops) -> getAT (fwdEffsC @_ @t)  (alg . Effs) ops


-- | This class builds a forwarder for an t`Effs` along a list @ts@ of transformers 
-- by ensuring that each transformer in @ts@ can forward @effs@.
-- This class is expected to be used by the user of @effective@ whenever they need 
-- to assert that some transformers can forward some effects, but this class is not
-- expected to be instantiated by the user because the following instances reduce
-- @ForwardsC cs effs ts@ to @`ForwardC` cs eff t@ for every @t@ in @ts@ and every
-- @eff@ in @effs@.
class ForwardsC effs ts where
  type FwdsConstraint effs ts :: (Type -> Type) -> Constraint
  fwdsC :: AlgTrans effs effs ts (FwdsConstraint effs ts)

instance ForwardsC effs '[] where
  type FwdsConstraint effs '[] = TruthC

  {-# INLINE fwdsC #-}
  fwdsC :: AlgTrans effs effs '[] (FwdsConstraint effs '[])
  fwdsC = AlgTrans $ \alg -> alg 

instance (ForwardEffsC effs t, ForwardsC effs ts) => ForwardsC effs (t ': ts) where
  type FwdsConstraint effs (t ': ts) = 
    CompC ts (FwdEffsConstraint effs t) (FwdsConstraint effs ts)

  {-# INLINE fwdsC #-}
  fwdsC :: AlgTrans effs effs (t ': ts) (FwdsConstraint effs (t ': ts))
  fwdsC = AlgTrans $ \(alg :: Algebra effs m) -> 
    getAT (fwdEffsC @_ @t) (getAT (fwdsC @_ @ts) alg)

type Forwards cs effs ts = (ForwardsC effs ts, ImpliesC cs (FwdsConstraint effs ts)) 

fwds :: forall cs effs ts. Forwards cs effs ts => AlgTrans effs effs ts cs
fwds = AlgTrans (getAT (fwdsC @effs @ts))
