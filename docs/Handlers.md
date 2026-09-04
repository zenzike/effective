<!--
```haskell
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}

module Handlers where

import Prelude hiding (getLine, putStrLn)
import qualified Prelude

import Control.Effect
import Control.Effect.Family.Algebraic
import Control.Effect.IO
import Control.Effect.State

import Hedgehog

$(makeGen [e| getLine  :: String |])
$(makeGen [e| putStrLn :: String ~> () |])

echo :: (Members '[GetLine, PutStrLn] effs) => Prog effs ()
echo = do str <- getLine
          case str of
            [] -> return ()
            _  -> do putStrLn str
                     echo

teletypeIO :: Handler '[GetLine, PutStrLn] '[Alg IO] '[] a a
teletypeIO = interpret $
  (\(GetLine k)     -> do x <- io Prelude.getLine; return (k x)) :%
  (\(PutStrLn xs k) -> do io (Prelude.putStrLn xs); return k)    :% emptyCase
```
-->

Interpreting Operations
-----------------------

Now suppose that the task is to count the number of times `getLine` is called
when the `echo` program is executed. One approach is to change the `echo`
program, and write something like `echoTick`, where a `tick` has been added
after each `getLine`:
```haskell
echoTick :: () ! '[GetLine, PutStrLn, Tick]
echoTick =
  do str <- getLine ; tick
     case str of
       [] -> return ()
       _  -> do putStrLn str
                echoTick
```
The idea is to execute this program using a specialised handler that counts the
number of ticks, before handling the teletype operations and collecting the
remaining `Alg IO` operations with `constIO`:
```haskell
exampleEchoTick :: IO ((), Int)
exampleEchoTick = handle (ticker |> teletypeIO |> constIO) echoTick
```
When this is executed, it counts the number of lines received:
```console
ghci> exampleEchoTick
Hello
Hello
world!
world!

((),3)
```
This demonstrates how unhandled effects that are recognized by I/O can be
forwarded and dealt with after the execution of the handler.

We can also emulate the behaviour of `echo` by ignoring all the ticks by using
the `unticker` handler:
```haskell
exampleEchoNoTick :: IO ()
exampleEchoNoTick = handle (unticker |> teletypeIO |> constIO) echoTick
```
Note that this is different to discarding the tick count by applying `fst`
to the result of a program that counts ticks: the count is not even generated
in the first place.


Programs and Handlers
---------------------

The type of the `echoTick` program is `() ! '[GetLine, PutStrLn, Tick]`, which is in
fact a synonym roughly equivalent to:
```haskell ignore
echoTick :: forall effs. (Member GetLine effs, Member PutStrLn effs, Member Tick effs)
         => Prog effs ()
```
The `a ! effs` datatype thus describes a *family* of programs which contains
all the operations given in `effs`. No order of the members is
implied (because the constraints are not ordered), and nor is the list necessarily exhaustive (because `effs` could contain other operations).

The `ticker` and `unticker` handlers have the following types:
```haskell ignore
ticker   :: Handler '[Tick] '[] '[StateT Int] a (a, Int)
unticker :: Handler '[Tick] '[] '[]           a a
```
Here is what the different parameters mean for the `ticker` handler:
```haskell ignore
ticker   :: Handler '[Tick]         -- input effects
                    '[]             -- output effects
                    '[StateT Int]   -- transformers
                    a               -- input type
                    (a, Int)        -- output type
```

The signature of the handler tells us how it behaves:
* **Input effects**: The input effects will be processed and removed by this handler.
  In `ticker` the input effect is `Tick`.
* **Output effects**: The output effects will be produced by this handler.
  In `ticker` the output effects are empty.
* **Transformers**: The transformer are used to provide semantics to the input effects.
  In `ticker` there is only one transformer `StateT Int`. The transformer
  list is applied to a monad `m` using `Apply`, so that
  `'Apply [t3, t2, t1] m a = t3 (t2 (t1 m a))`.
* **Input/output types**: The input/output types are the types of the return values
  of an effectful program before/after applying the handler. When `ticker` is used
  to handle a program of type `Prog effs a`, the output will be the type `(a, Int)`.

A handler is applied to a program using the `handle` function or its variants.
In `exampleEchoTick`, the pipeline is complete because `ticker` consumes `Tick`,
`teletypeIO` translates `GetLine` and `PutStrLn` into `Alg IO`, and `constIO`
consumes the remaining `Alg IO` operations at the end.
```haskell ignore
handle
  :: (...)
  => Handler effs '[] ts a b
  -> Prog effs a -> Apply ts Identity b
```
So far, we have been working with examples of _impure_ effects that ultimately
rely on `IO`. Another important class of effects is the class of _pure_ effects,
which we will look at next.


Working with Pure Handlers
--------------------------

A pure handler can be applied when all the effects in a program are
processed, and when none are produced:
```haskell ignore
handle :: forall effs ts fs a .
  (Monad (Apply ts Identity), HFunctor (Effs effs))
  => Handler effs '[] ts fs
  -> Prog effs a
  -> Apply fs a
```

For example, a pure state effect is provided in `Effect.Control.State`, which
supports `get` and `put` as operations that are indicated by `Get s` and `Put s`
in a signature.

Here is a program that increments the number in a state
and returns it:
```haskell
incr :: () ! [Put Int, Get Int]
incr = do x <- get
          put @Int (x + 1)
```

This program can be executed by using a `state s` handler, where the
state is initialised to `s`:
```haskell ignore
state :: s -> Handler '[Put s, Get s]   -- input effects
                      '[]               -- output effects
                      '[StateT s]       -- transformer
                      a                 -- input type
                      (a, s)            -- output type
```

Executing the `incr` program with this handler can be achieved as follows:
```console
ghci> handle (state (41 :: Int)) incr
((),42)
```
Since the program has type `() ! [Put Int, Get Int]`, with a pure value of `()`,
the result of applying the handler is a value of type `((), Int)`.

The type of the `state` handler promises to handle both `Put s` and `Get s`
operations, and so it is able to work with programs that use both, or
either one of these. Here is a program that only uses `Get String`:
```haskell
getStringLength :: Int ! '[Get String]
getStringLength = do xs <- get @String
                     return (length xs)
```
It can be handled using `state`:
```console
ghci> handle (state "Hello!") getStringLength
(6,"Hello!")
```
Notice that the `state` handler returns the final return value of the program
as well as the final state.

A variation of the `state` handler is `state_`,
which does not return the final state:
```haskell ignore
state_ :: s -> Handler [Put s, Get s] '[] '[StateT s] '[]
```
Here the final wrapper is `'[]`, and so applying this to a program
of type `Prog effs a` will simply return a value of type `a`.
```console
ghci> handle (state_ "Hello!") getStringLength
6
```

The effect of `handle h p` is to use the handler `h` to remove _all_ the
effects in interpreting the program `p`. This relates to both the effects
of the program and effects output by a handler.
Trying to apply a handler that does not fully evaluate the effects in `p` will
result in a type error.
For example, the `echo` program cannot be handled with a state handler:
```console
ghci> handle (state "Hello") echo

<interactive>:2:24: error: [GHC-39999]
    • No instance for ‘Member' GetLine '[] (ElemIndex GetLine '[])’
        arising from a use of ‘echo’
    • In the second argument of ‘handle’, namely ‘echo’
      In the expression: handle (state "Hello") echo
      In an equation for ‘it’: it = handle (state "Hello") echo
```
This is essentially saying that `GetLine` is not supported by the state handler.


Defining  Operations
--------------------

One of the key features of an effect system is to allow an effect engineer
to create new effects and interpret them in different ways. Although
`getLine` and `putStrLn` are special, in that they are processed by `evalIO`
and provided by the `effective` library, the `tick` operation is a
custom operation with a semantics given as we desire.

The goal is to provide an operation written `tick` that can be used when constructing programs, and a corresponding datatype `Tick` that is used
for pattern matching.

Creating custom operations typically requires the following to be defined:

1. **Operation Signature:** A datatype for the underlying operation
2. **Pattern Synonym:** A pattern synonym facilitate algebra definitions
3. **Smart Constructor:** A smart constructor to enable programs to use the operation

This is boilerplate that will hopefully be avoided Template Haskell
in a future iteration of this library.

### Operation Signature

For now, the `tick` operation is defined by providing a datastructure to hold
the syntax as data with the following:
```haskell
type Tick = Alg Tick_
data Tick_ k = Tick_ k
  deriving Functor
```
The `Tick` type is an algebraic operation, denoted with `Alg` using the
underlying signature `Tick_`. The convention is to add an *underscore* for the *underlying* signature functor.

### Pattern Synonym

A pattern synonym `Tick` is defined:
```haskell
pattern Tick p = Alg (Tick_ p)
```

### Smart Constructor

A smart constructor `tick` is defined that allows programs to be written
that uses this operation:
```haskell
tick :: () ! '[Tick]
tick = call (Tick ())
```
The signature of `tick` uses a `Member` constraint to describe how `tick` can be
used in any program where `Tick` is in its signature, and this is the same as
writing `tick :: () ! '[Tick]`. The `Alg` constructor indicates that `Tick` is
an algebraic operation.

Defining Handlers
-----------------

The `unticker` and `ticker` handlers are examples of interpreters that
will interpret `Tick` in different ways. The simplest one is `unticker`,
which removes all instances of `Tick`:
```haskell
unticker :: Handler '[Tick] '[] '[] a a
unticker = interpret1 (\(Tick x) -> return x)
```
The `interpret1` function builds a handler from a function
that describes how to rephrase an operation. Here, `Tick x`
is translated into `return x`.

The `ticker` handler is a bit more complex: it works by interpreting
the `tick` operation into `get` and `put` operations, which interact
with an `Int` to keep track of how many ticks have been produced.
Notice that the `gen` function generates these operations from the given `tick`:
```haskell
tickState :: Handler '[Tick] '[Put Int, Get Int] '[] a a
tickState = interpret1 rephrase where
  rephrase :: Tick m x -> Prog [Put Int, Get Int] x
  rephrase (Tick x) = do n <- get
                         put @Int (n + 1)
                         return x
```
The `ticker` is produced by combining `tickState` with the `state` handler using
the _pipe_ combinator, written `h1 \\ h2` to pipe the handler `h1` into the
handler `h2`.

```haskell
ticker :: Handler '[Tick] '[] '[StateT Int] a (a, Int)
ticker = tickState \\ state (0 :: Int)
```
Given `h1 :: Handler effs1 oeffs1 t1 f1` and `h2 :: Handler effs2 oeffs2 t2 f2`, the
result of `h1 \\ h2` is a handler that recognises all of `effs1`, the input
effects of `h1`, and passes any effects `oeffs1` produced by `h1` to be processed
by `h2`. Here are the types involved:
```haskell ignore
(\\) :: ...
  => Handler effs1 oeffs1 ts1 fs1    -- h1
  -> Handler effs2 oeffs2 ts2 fs2    -- h2
  -> Handler effs1
             ((oeffs1 :\\ effs2) `Union` oeffs2)
             (ts1 :++ ts2)
             (fs2 :++ fs1)
```
More specifically, the output effects of the resulting handler include all the output
effects of `h1` that are not processed by `h2`, together with any effects
produced by `h2`.

The transformers and wrappers of the resulting handler are the concatenation of those
given by `h1` and `h2`. Note, however, transformers and wrappers are
concatenated in opposite orders.


Intercepting Operations
-----------------------

Forwarding effects to I/O works in many situations, but sometimes it is rather
crude: the power of effects is in their ability to intercept and translate
operations.

Suppose the task is now to count all instances of `getLine` in the
entire program. Adding `incr` after every `getLine` may require a large
refactor, and remembering to add `incr` in all future calls of `getLine` is a
burden. An alternative would be to define a variation of `getLine` that
incorporates `incr`, but that is not necessarily better.

Better would be to allow a different interpretation of `getLine` that
automatically increments a variable: then the `echo` program could
remain exactly the same. To do this, the `getLine` operation must
be intercepted.

Here is how to write a handler that intercepts a `getLine` operation, only to
emit it again while also incrementing a counter in the state:
```haskell
getLineIncr
  :: Handler '[GetLine]                       -- input effects
             '[GetLine, Get Int, Put Int]     -- output effects
             '[]                              -- no transformers
             a
             a
getLineIncr = interpret1 $ \(GetLine k) ->
  do xs <- getLine
     incr
     return (k xs)
```
The handler says that it will deal with `[GetLine]` as an input effect,
and will output the effects `[GetLine, Get Int, Put Int]`.

Now the task is to connect this handler with `state`. This can
be achieved with a `pipe`, which we write as `||>`:
```haskell
getLineIncrState :: Handler '[GetLine]   -- input effects
                            '[GetLine]   -- output effects
                            '[StateT Int]
                            a
                            (a, Int)
getLineIncrState = getLineIncr \\ (state (0 :: Int))
```
This can then be executed using `handleIO`, which will deal with
the residual `GetLine` effect:
```console
ghci> handleIO getLineIncrState echo
Hello
Hello
world!
world!

((),3)
```
The `getLineIncrState` has intercepted the `getLine` operation and
incremented the state counter on each execution.

<!--
```haskell
examples :: Group
examples = Group "Handlers" []
```
-->
