[![Build Status](https://github.com/zenzike/effective/actions/workflows/ci.yml/badge.svg)](https://github.com/zenzike/effective/actions)

Effective
==========

The `effective` library is an effect handlers library for Haskell that is
designed to allow users to define and interpret their own languages and
effects. This library incorporates support for:

* Algebraic, scoped, and other higher-order effects.
* Combinators for defining and composing deep effect handlers.
* Staged effectful programming using Typed Template Haskell.

Getting Started
---------------

The README is a checked literate Haskell file. To run it locally:
```console
cabal test readme
cabal repl readme
```
The longer documentation examples are also compiled and tested:
```console
cabal test docs
```
This compiles this readme and other examples. Each `.md` file has a matching
`.lhs` symlink so the documentation can be compiled.

[`Control.Effect`](src/Control/Effect.hs) is the public entry point which
re-exports the core program type, handler type, handler combinators, evaluation
functions, and Template Haskell helpers for defining operations.


Operations
----------

A core idea of effect handlers is to produce a program with an
*effect signature* that describes the kinds of operations that the
program makes use of.

For example, creating a `Teletype` program is a rite of passage for monadic IO
[^Gordon1992] where the challenge is to show how IO of reading from and writing
to the terminal can be achieved. The example uses two user-defined operations,
`getLine` and `putStrLn`, which are generated from their operation signatures:
```haskell
$(makeGen [e| getLine  :: String |])
$(makeGen [e| putStrLn :: String ~> () |])
```
This generates operations with the following types:
```haskell ignore
getLine  :: Member GetLine effs  => Prog effs String
putStrLn :: Member PutStrLn effs => String -> Prog effs ()
```
These are programs whose effects `effs` contains `GetLine` and `PutStrLn`,
respectively.

Using these operations, the `echo` program will continue to echo the input
obtained by `getLine` using `putStrLn` until a blank line is received:
```haskell
echo :: (Members '[GetLine, PutStrLn] effs) => Prog effs ()
echo = do str <- getLine
          case str of
            [] -> return ()
            _  -> do putStrLn str
                     echo
```
The type signature stipulates that `echo` is a family of programs whose effect
signature contains `[GetLine, PutStrLn]`, and returns a result of type `()`.
Although a list is used, the order of effects in the signature is irrelevant.
The effect signature says that this is a program that may use the corresponding
`getLine` and `putStrLn` operations.

Handlers
--------

The most direct interpretation of this program is to use the corresponding
operations from `Prelude` for `getLine` and `putStrLn` to interpret
the syntax for these operations. In `effective`, `IO`
actions enter a program through the built-in `Alg IO` effect:
```haskell ignore
io :: Members '[Alg IO] effs => IO a -> Prog effs a
```
The call to `io` records the action as syntax to be handled later on.

An interpretation is given by a *handler*, which processes each of the
operations.
For instance, the `teletypeIO` handler is defined as follows.
The main type parameters of this handler of interest indicate the
*input* effects that are consumed (`GetLine` and `PutStrLn`), and the
*output* effects that are produced (`Alg IO`):
```haskell
--                     +------------------------------------- input effects
--                     |                    +---------------- output effects
--                     |                    |         +------ carrier transformers
--                     |                    |         |  +--- program result
--                     |                    |         |  | +- handler result
--                     |                    |         |  | |
teletypeIO :: Handler '[GetLine, PutStrLn] '[Alg IO] '[] a a
teletypeIO = interpret $
  (\(GetLine k)     -> do x <- io (Prelude.getLine); return (k x)) :%
  (\(PutStrLn xs k) -> do x <- io (Prelude.putStrLn xs); return k) :% emptyCase
```
Looking at the body of this handler, we can see that it functions by
interpreting the syntax of `GetLine` and `PutStrLn` in terms of calls to `io`
which schedules the appropriate actions. The clauses for the operations are put
together using the binary operator `(:%)`, finished with `emptyCase`.

Composing Handlers
------------------

The output effects of `teletypeIO` is `Alg IO`, which must be fully consumed
before the program can be handled. This is achieved by composing
`teletypeIO` with another handler, `constIO`:
```haskell ignore
constIO :: Handler '[Alg IO] '[] '[ConstIO] a (IO a)
```
The signature of `constIO` promises to consume `Alg IO` and produce no
additional effects. It does so by using `ConstIO` internally, and takes the
program result `a` into a handler result `IO a`.

Using the pipe operator `\\`, we combine `teletypeIO` with `constIO` into
a single handler that can interpret the `echo` program:
<!--
```haskell
exampleIO :: IO ()
exampleIO = handle (teletypeIO \\ constIO) echo
```
-->
```console
ghci> handle (teletypeIO \\ constIO) echo :: IO ()
Hello world!
Hello world!
```
This executes the `echo` program where input provided on the
terminal by the user is immediately echoed back out to the terminal.

Reinterpreting Operations
-------------------------

A different interpretation changes only the handler. Instead of running
the terminal version, the same `echo` program can be given a pure input
buffer and a pure output log by applying a different handler:
```haskell
teletypeStateWriter :: Handler
  '[GetLine, PutStrLn] '[Put [String], Get [String], Tell [String]] '[] a a
teletypeStateWriter = interpret $
  (\(GetLine k)     ->  do xs <- get; case xs of
                                        []    -> return (k "")
                                        x:xs' -> do put xs'
                                                    return (k x)) :%
  (\(PutStrLn xs k) -> do tell [xs]; return k)                    :% emptyCase
```
This translation replaces `getLine` and `putStrLn` with different operations.
This can be done in terms of `get`, `put`, and `tell`, and these can
in turn be interpreted by `state_` and `writer` handlers. These handlers are
then composed to form `teletypePure`:
```haskell
teletypePure :: [String]
             -> Handler '[GetLine, PutStrLn] '[]
                        '[StateT [String], WriterT [String]]
                        a ([String], a)
teletypePure input =
  (teletypeStateWriter \\ state_ input) \\ writer
```
The handler consumes strings from its input list; when the list is exhausted it
returns the blank line that makes `echo` stop, and it returns the strings that
would have been printed.
<!--
```haskell
examplePure :: ([String], ())
examplePure = handle (teletypePure ["Hello world!"]) echo
```
-->
```console
ghci> handle (teletypePure ["Hello world!"]) echo
(["Hello world!"],())
```
Effect handlers have allowed us to interpret the `echo` program in two different
ways: as a terminal version that interacts with `IO`, and as a pure
version that works with lists of input and output.

Scoped Operations
-----------------

Operations like `getLine` and `putStrLn` are *algebraic*: they take values as
parameters and return values to the program. The `effective` library also
supports *scoped* operations, which take entire subprograms as arguments. For
example, the `censor` operation marks a region of a program whose output
should be transformed by a cipher:
```haskell
hoppy :: () ! [Tell [String], Censor [String]]
hoppy = do tell ["Hello Alfie!"]
           censor backwards $
             do tell ["tortoise"]
                censor shout $
                  do tell ["get bigger!"]
           tell ["Goodbye!"]

backwards, shout :: [String] -> [String]
backwards = map reverse
shout     = map (map toUpper)
```
The `censors` handler applies ciphers to the `tell` operations in the regions
they delimit, and nested ciphers accumulate:
```console
ghci> handle (censors @[String] id |> writer) hoppy :: ([String], ())
(["Hello Alfie!","esiotrot","!REGGIB TEG","Goodbye!"],())
```
Since `censor` is ordinary operation syntax, a different handler can give it a
different meaning, such as removing the censorship altogether.


Documentation
-------------

### Tutorial

A tutorial can be found in
[docs/Tutorial.md](docs/Tutorial.md). Another resource is the paper
[Composing and Staging Effect Handlers](https://yangzhixuan.github.io/pdf/effective-paper.pdf),
which is a self-contained explanation of the design of this library.

### Built-in Effects

The library is exposed through
[`Control.Effect`](https://github.com/zenzike/effective/blob/master/src/Control/Effect.hs),
and a number of built-in effects are provided in this library
that have their own documentation. Each of these modules defines the operations
of one effect and one or more handlers that give them a meaning:

| Module | Description | Operations | Handlers |
| --- | --- | --- | --- |
| [`Control.Effect.Reader`](https://github.com/zenzike/effective/blob/master/src/Control/Effect/Reader.hs) | A read-only environment. | `ask`, `asks`, `local` | `reader`, `asker` |
| [`Control.Effect.Writer`](https://github.com/zenzike/effective/blob/master/src/Control/Effect/Writer.hs) | Output accumulated in a monoid. | `tell`, `censor` | `writer`, `writer_`, `censors`, `uncensors` |
| [`Control.Effect.State`](https://github.com/zenzike/effective/blob/master/src/Control/Effect/State.hs) | A single mutable value. | `get`, `put` | `state`, `state_` |
| [`Control.Effect.Except`](https://github.com/zenzike/effective/blob/master/src/Control/Effect/Except.hs) | Exceptions that carry a value. | `throw`, `catch` | `except`, `retry` |
| [`Control.Effect.Maybe`](https://github.com/zenzike/effective/blob/master/src/Control/Effect/Maybe.hs) | Failure without a value. | `throw`, `catch` | `except`, `retry` |
| [`Control.Effect.IO`](https://github.com/zenzike/effective/blob/master/src/Control/Effect/IO.hs) | Real input and output. | `io` | `constIO`, `handleIO` |
| [`Control.Effect.Nondet`](https://github.com/zenzike/effective/blob/master/src/Control/Effect/Nondet.hs) | Choice and failure. | `empty`, `<\|>`, `select`, `once`, `cut` | `list`, `logic`, `nondet`, `backtrack` |
| [`Control.Effect.Concurrency`](https://github.com/zenzike/effective/blob/master/src/Control/Effect/Concurrency.hs) | Processes that synchronise on actions. | `par`, `act`, `res` | `resump`, `resumpWith`, `ccsByQSem` |
| [`Control.Effect.Yield`](https://github.com/zenzike/effective/blob/master/src/Control/Effect/Yield.hs) | Coroutines that exchange values. | `yield`, `mapYield` | `pingpongWith` |
| [`Control.Effect.HStore`](https://github.com/zenzike/effective/tree/master/src/Control/Effect/HStore) | Mutable cells holding values of any type. | `new`, `get`, `put` | `handleHS`, `runHS` |
| [`Control.Effect.WithName`](https://github.com/zenzike/effective/blob/master/src/Control/Effect/WithName.hs) | Named copies of an existing effect. | `:@`, `callP` | `renameEffs`, `renameOEffs` |

### Internal Implementation

The modules under [`Control.Effect.Internal`](https://github.com/zenzike/effective/tree/master/src/Control/Effect/Internal)
contain implementation details that are always subject to change. For the
curious, a logical order in which to read them is as follows:

| Module | Contents |
| --- | --- |
| [`Control.Effect.Internal.Algebra`](https://github.com/zenzike/effective/blob/master/src/Control/Effect/Internal/Algebra.hs) | The data structure for storing effect operations |
| [`Control.Effect.Internal.Prog.Imp`](https://github.com/zenzike/effective/blob/master/src/Control/Effect/Internal/Prog/Imp.hs) | Programs in impredicative encoding |
| [`Control.Effect.Internal.AlgTrans`](https://github.com/zenzike/effective/blob/master/src/Control/Effect/Internal/AlgTrans.hs) | Transforming effectful operations along carrier transformers |
| [`Control.Effect.Internal.Forward`](https://github.com/zenzike/effective/blob/master/src/Control/Effect/Internal/Forward.hs) | Default forwarding algebras |
| [`Control.Effect.Internal.Runner`](https://github.com/zenzike/effective/blob/master/src/Control/Effect/Internal/Runner.hs) | Runners do initialisation and finalisation work around handling operations |
| [`Control.Effect.Internal.Handler`](https://github.com/zenzike/effective/blob/master/src/Control/Effect/Internal/Handler.hs) | Handlers and handler combinators |

<!--
Language Extensions
--------------------

The `effective` library requires the `DataKinds` extension since
this is used to keep track of effect signatures.

```haskell top
{-# LANGUAGE DataKinds       #-}
{-# LANGUAGE GADTs           #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns    #-}
{-# LANGUAGE LambdaCase      #-}
{-# LANGUAGE TemplateHaskell #-}
```
The following pragma is only needed for the testing framework.
```haskell top
{-# LANGUAGE OverloadedStrings #-}
```

Imports
-------

This file has a number of imports:

```haskell top
import Control.Effect
import Control.Effect.IO
import Control.Effect.State
import Control.Effect.Writer

import Data.Char (toUpper)
import Prelude hiding (putStrLn, getLine)
import qualified Prelude
import Hedgehog (Group(..), property, checkParallel, (===))
import Hedgehog.Main (defaultMain)
```

```haskell
props :: Group
-- props = $$(discover)
props = Group "README properties"
  [ ("examplePure", property $
      examplePure === (["Hello world!"], ()))
  , ("exampleCensor", property $
      (handle (censors @[String] id |> writer) hoppy :: ([String], ()))
        === (["Hello Alfie!","esiotrot","!REGGIB TEG","Goodbye!"], ()))
  ]

main :: IO ()
main = defaultMain $ fmap checkParallel [props]
```
-->

References
----------

* [Effect Handlers in Scope. N. Wu, T. Schrijvers, R. Hinze. Haskell Symposium. 2014](https://dl.acm.org/doi/10.1145/2633357.2633358)

* [Modular Models of Monoids with Operations. Z. Yang, N. Wu. ICFP. 2023](https://dl.acm.org/doi/10.1145/3607850)

* [A Framework for Higher-Order Effects & Handlers. B. v.d. Berg, T. Schrijvers. SCP 2024](https://doi.org/10.1016/j.scico.2024.103086)

* [Freer Monads, More Extensible Effects. O. Kiselyov, H. Ishii. Haskell 2015](https://doi.org/10.1145/2804302.2804319)

* [Handling Higher-Order Effectful Operations with Judgemental Monadic Laws. Z. Yang, N. Wu. POPL. 2026](https://dl.acm.org/doi/10.1145/3776678)

* [Composing and Staging Effect Handlers. Z. Yang, N. Wu](https://yangzhixuan.github.io/pdf/effective-paper.pdf)

[^Gordon1992]: [Functional Programming and Input/Output. A. Gordon. PhD Thesis, King's College London. 1992](https://www.microsoft.com/en-us/research/uploads/prod/2016/11/fpio.pdf)
