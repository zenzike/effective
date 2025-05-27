{-|
Module      : Control.Effect.CodeGen
Description : Staged effectful programming
License     : BSD-3-Clause
Maintainer  : Zhixuan Yang
Stability   : experimental

This module contains everything related to the code-generation effect for
staged monadic programming. This effect is useful for writing highly optimised
effectful programs without any abstract cost incurred by algebraic effects and
handlers. Programming with the code-generation effect slightly changes the way
of using the @effective@ library, so it deserves its own dedicated tutorial
(to be written). The rough idea is that instead of handling effectful programs
of type @Prog eff a@ at runtime, we only use @effective@ at compile time to
generate (optimised) monadic programs (e.g. of type @StateT (ListT Identity) a@) 
to be executed at runtime. There are some random small examples in @test/Staged.hs@
and @test/StagedGen.hs@ of how this is done.

The technique here is heavily inspired by András Kovács's work on staged programming
with two-level type theory described in
  1. ICFP 2024: [Closure-Free Functional Programming in a Two-Level Type Theory](https://dl.acm.org/doi/10.1145/3674648)
  2. ICFP 2022: [Staged Compilation With Two-Level Type Theory](https://dl.acm.org/doi/10.1145/3547641)
-}
module Control.Effect.CodeGen (
    module Control.Effect.CodeGen.Up
  , module Control.Effect.CodeGen.Split
  , module Control.Effect.CodeGen.Down
  , module Control.Effect.CodeGen.Type
  , module Control.Effect.CodeGen.Gen
  , module Control.Effect.CodeGen.Eval
  , module Control.Effect.CodeGen.JoinFlow
  , module Control.Effect.CodeGen.Nondet
  , module Control.Effect.CodeGen.Concurrency
  ) where

import Control.Effect.CodeGen.Up
import Control.Effect.CodeGen.Split
import Control.Effect.CodeGen.Down
import Control.Effect.CodeGen.Type
import Control.Effect.CodeGen.Gen
import Control.Effect.CodeGen.Eval
import Control.Effect.CodeGen.JoinFlow
import Control.Effect.CodeGen.Nondet
import Control.Effect.CodeGen.Concurrency