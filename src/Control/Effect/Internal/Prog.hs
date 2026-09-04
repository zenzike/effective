{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE MagicHash #-}
{-|
Module      : Control.Effect.Internal.Prog
Description : The datatype for effectful programs
License     : BSD-3-Clause
Maintainer  : Nicolas Wu
Stability   : experimental

This module exports the type of effectful programs. We may have more than one
underlying representations (that provide the same interface) and which one used
is controlled by some CPP flags. Currently the default is the impredicative
encoding in "Control.Effect.Internal.Prog.Imp".
-}

module Control.Effect.Internal.Prog
  (
    -- * Program datatypes
    Prog,
    type (!),

    -- * Program constructors
    call,
    callJ,
    callK,
    progAlg, ProgAlg#,
    weakenProg,

    -- * Program eliminator
    eval, eval'
  )
  where


import Control.Effect.Internal.Prog.Imp
import Control.Effect.Internal.Algebra

-- | @a ! effs@ is the type of programs with a polymorphic effect set that contains at least @effs@.
-- The return type of programs is @a@.
type a ! effs = forall effs' . Members effs effs' => Prog effs' a