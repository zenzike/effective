{-|
Module      : Control.Effect.Internal.Prog
Description : The datatype for effectful programs
License     : BSD-3-Clause
Maintainer  : Nicolas Wu
Stability   : experimental

This module exports the type of effectful programs. The library ships with more than one underlying
representations (that provide the same interface) and are controlled by some CPP flags. 
Currently the default is the impredicative encoding in "Control.Effect.Internal.Prog.ProgImp".
-}

{-# LANGUAGE CPP #-}

module Control.Effect.Internal.Prog
  ( 
    -- * Program datatypes
    Prog, 
    Progs, 

    -- * Program constructors
    call, 
    call', 
    callK,
    progAlg, 
    weakenProg, 

    -- * Program eliminator
    eval,
  )
  where


#ifdef PROGDIRECT
import Control.Effect.Internal.Prog.ProgDirect
#else
import Control.Effect.Internal.Prog.ProgImp
#endif

import Control.Effect.Internal.Effs

-- | A family of programs that may contain at least the effects in @effs@ in any
-- order.
type Progs effs -- ^ A list of effects the program may use
           a    -- ^ The return value of the program
  = forall effs' . Members effs effs' => Prog effs' a