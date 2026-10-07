{-|
Module      : Control.Effect.Do
Description : Exception throwing with a value
License     : BSD-3-Clause
Maintainer  : Nicolas Wu
Stability   : experimental

This adds |do| notation to handlers by making use of the
@QualifiedDo@ extension.

@
{-# LANGUAGE QualifiedDo #-}
import qualified Control.Effect.Do as H

handle (H.do getLineState \\\\ state ["World"]
             teletypeIO
             constIO) hello
@
This merely desugars @H.do { h1; h2; h3 }@ to become @h1 |> h2 |> h3@.
-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE ImpredicativeTypes #-}

module Control.Effect.Do ((>>)) where

import Prelude hiding ((>>))

import Control.Effect.Internal.Handler (Handler, (|>))
import Control.Effect.Internal.AlgTrans (FuseAT#)
import Control.Effect.Internal.AlgTrans.Type (MonadApply)
import Control.Effect.Internal.Runner (FuseR#)
import Control.Effect.Internal.Forward (ForwardsM)
import Data.List.Kind (Union, type (:\\), type (:++))

(>>)
  :: forall effs1 effs2 oeffs1 oeffs2 ts1 ts2 a1 a2 a3.
     ( forall m. Monad m => MonadApply ts2 m
     , ForwardsM effs2 ts1
     , ForwardsM (oeffs1 :\\ effs2) ts2
     , FuseAT# effs1 effs2 oeffs1 oeffs2 ts1 ts2
     , FuseR# effs2 oeffs1 oeffs2 ts1 ts2 )
  => Handler effs1 oeffs1 ts1 a1 a2   -- ^ @h1@
  -> Handler effs2 oeffs2 ts2 a2 a3   -- ^ @h2@
  -> Handler (effs1 `Union` effs2)
             ((oeffs1 :\\ effs2) `Union` oeffs2)
             (ts1 :++ ts2)
             a1 a3
(>>) = (|>)





