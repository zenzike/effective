<!--
```haskell
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}

module IO where

import Prelude hiding (getLine, putStrLn)
import qualified Prelude

import Control.Effect
import Control.Effect.Family.Algebraic
import Control.Effect.IO
import Control.Effect.Maybe (MaybeT(..))
import Control.Effect.State
import qualified Control.Effect.Maybe as Maybe
import qualified Control.Effect.State as State
import Control.Exception (SomeException, try)
import Data.IORef
import Hedgehog hiding (evalIO)
import qualified Hedgehog as H
```
-->

Working with IO
===============

A value of type `Prog effs a` is a syntax tree of a program that uses
operations in the effects `effs`, and with variables of type `a`. It
describes the order in which the operations are performed, but leaves
the semantics of those operations for the handler to interpret.

This matters for `IO` because real input and output cannot be performed while a
program is still just syntax. In this document, the main route is:

1. write the program using operations;
2. translate those operations into the built-in `Alg IO` effect;
3. collect those `Alg IO` operations into a final `IO` action with `ConstIO`;
4. evaluate the syntax with `handle`, producing that `IO` action.

The later sections compare this with `handleIO`, and explain the narrower limit:
`IO` works well as the final collected result, but not as a reusable carrier
layer in the middle of an arbitrary stack.


Pure vs Mutable State
----------------------

The `get` and `set` operations are used to work with a single state
value of type `s`:
```haskell ignore
put :: Member (Put s) effs => s -> Prog effs ()
get :: Member (Get s) effs => Prog effs s
```
They can be used to define a simple increment function that
bumps the value in the state by 1:
```haskell
incr :: () ! [Put Int, Get Int]
incr = do x <- get
          put @Int (x + 1)
```
The standard `state` handler interprets these operations purely,
and internally uses the strict `StateT` transformer by default.
```haskell ignore
state :: s -> Handler [Put s, Get s] '[] '[Strict.StateT s] a (a, s)
```
So, to test this is a simple as applying the handler with a starting state:
```haskell
example1 :: ((), Int)
example1 = handle (state 41) incr :: ((), Int)

-- >>> example1
-- ((), 42)
```
Internally this uses the `State` monad, and so the resulting computation is pure.

A different way to do this is to work with an `IORef` that holds
the state and is interacted with using `writeIORef` and `readIORef`:
```haskell
stateIORef :: IORef s -> Handler '[State.Put s, State.Get s] '[Alg IO] '[] a a
stateIORef ref =
  interpret
    (\case (State.Put s k) -> do io (writeIORef ref s); return k
           (State.Get k)   -> do s <- io (readIORef ref); return (k s))
```
This program does not execute `IO` immediately: it creates `io` operations
that are to be consumed by the `constIO` handler from `Control.Effect.IO`:

```haskell
example2 :: IO Int
example2 = do ref <- newIORef (41 :: Int)
              handle (stateIORef ref |> constIO) incr
              readIORef ref
```





Recording IO Actions
--------------------
```haskell
helloIO :: Members '[Alg IO] effs => Prog effs ()
helloIO = io (Prelude.putStrLn "hello")
```
`helloIO` prints only when the program is evaluated with an algebra that runs
`Alg IO`.


Translating Teletype to Alg IO
------------------------------

The `teletypeIO` handler uses `io` operations when it translates `GetLine` and
`PutStrLn`:
```haskell
teletypeIO :: Handler '[GetLine, PutStrLn] '[Alg IO] '[] a a
teletypeIO = interpret
  (\case GetLine k ->
           do x <- io Prelude.getLine
              return (k x)
         PutStrLn xs k ->
           do io (Prelude.putStrLn xs)
              return k)
```
This handler has a type that can be read as follows:
```haskell ignore
--      +-------------------------------------- input effects
--      |                     +---------------- output effects
--      |                     |         +------ carrier transformers
--      |                     |         |  +--- program result
--      |                     |         |  | +- handler result
--      |                     |         |  | |
Handler '[GetLine, PutStrLn] '[Alg IO] '[] a a
```
The handler consumes the teletype operations. It may produce `Alg IO`
operations. It uses no carrier transformers, because the stack is `'[]`. It
leaves the result type unchanged: a program that returns an `a` is still
interpreted as a computation returning an `a`.

The important point is that `teletypeIO` still does not run `IO`. It rewrites one
language into another: `GetLine` and `PutStrLn` are replaced by `Alg IO`
operations built with `io`.


Collecting IO with ConstIO
--------------------------

Plain `handle` can evaluate a handler only when no output effects remain. Since
`teletypeIO` leaves `Alg IO` operations behind, we need a second handler that
consumes `Alg IO` and returns a final `IO` action. The carrier for that handler
is `ConstIO`, provided by `Control.Effect.IO`:
```haskell ignore
constIO :: Handler '[Alg IO] '[] '[ConstIO] a (IO a)
```
The name is literal: for every lower monad `m`, `ConstIO m` stores an `IO`
action and ignores `m`. That is enough to consume `Alg IO`: each operation
contains an `IO x`, and `constIO` stores that action in the carrier. When
evaluation finishes, the handler unwraps the stored action and returns it as the
final result of `handle`:
```haskell
runHelloWithHandle :: IO ()
runHelloWithHandle = handle constIO helloIO
```
This is still syntax-directed evaluation. `handle` evaluates the program with
`Identity` as its base monad; `ConstIO` is the bottom carrier that turns the
result into `IO`.


Running the Example
-------------------

Since `teletypeIO` translates `GetLine` and `PutStrLn` into `Alg IO`, composing it
with `constIO` gives a complete handler:
```haskell
runEchoIO :: IO ()
runEchoIO = handle (teletypeIO |> constIO) echo
```
The call to `handle` returns an `IO` action. It does not choose `IO` as the base
monad; it uses `ConstIO` as the bottom carrier and unwraps the collected action at
the end.


Choosing IO as the Base
-----------------------

There is also a direct-base route. The general evaluation function that chooses a
non-pure base monad is `handleM`. It runs the handler in a caller-chosen monad and
supplies an algebra for the effects that remain in that monad:
```haskell ignore
handleM
  :: Algebra xeffs m
  -> Handler effs oeffs ts a b
  -> Prog (effs `Union` xeffs) a
  -> m b
```
For ordinary terminal `IO`, the external algebra is `ioAlg`:
```haskell ignore
ioAlg :: Algebra '[Alg IO] IO
```
Using it with `teletypeIO` gives the missing meaning for the `Alg IO` operations
that the handler produces:
```haskell ignore
handleM ioAlg teletypeIO echo :: IO ()
```
The convenience function `handleIO` packages exactly this common case:
```haskell ignore
handleIO = handleM ioAlg
```
This is a different route to the same kind of result:
```haskell
runEchoHandleIO :: IO ()
runEchoHandleIO = handleIO teletypeIO echo
```
`handleIO` chooses `IO` as the base monad and uses `ioAlg` to run `Alg IO`
operations there. `handle (teletypeIO |> constIO)` keeps `Identity` as the base
and collects the `IO` action in the bottom carrier. This document does not claim
which route is faster; that would need measurement.


Using an Algebra Transformer Directly
-------------------------------------

A `Handler` contains both an algebra transformer and a runner. Sometimes the
runner is not needed. If all we want is to evaluate syntax into its carrier, we
can work directly with an `AlgTrans` and use `evalAT'`.

Here is a simplified type:
```haskell ignore
evalAT'
  :: AlgTrans effs '[] ts cs
  -> Prog effs a
  -> Apply ts m a
```

The output row is empty, so `evalAT'` needs no external output algebra. It also
does not take a runner. The result is the carrier computation itself,
`Apply ts m a`.

The ordinary `IO` algebra can be viewed as an algebra transformer with no
transformer stack:
```haskell
ioAT :: AlgTrans '[Alg IO] '[] '[] ((~) IO)
ioAT = asAT ioAlg
```

The `((~) IO)` constraint says that `ioAT` only works when the base monad is
exactly `IO`. It consumes `Alg IO`, produces no remaining effects, and leaves
the carrier unchanged.

For a program that already only uses `Alg IO`, this is enough:
```haskell
runHelloIO :: IO ()
runHelloIO = evalAT' ioAT helloIO
```

The same idea applies to `echo`. The `halg` component of `teletypeIO` is the
algebra transformer that translates `GetLine` and `PutStrLn` into `Alg IO`.
Composing it with `ioAT` gives a complete interpretation with no remaining
effects:
```haskell
runEchoAT :: IO ()
runEchoAT = evalAT' (halg teletypeIO `compAT` ioAT) echo
```

This is not `handle` running `IO` from `Identity`. It is a different evaluation
basis: choose `IO` through the algebra transformer constraint, evaluate with
`evalAT'`, and do not use a handler runner.

Use this style when the carrier computation is already the result you want. Use
a `Handler` and one of the `handle` functions when the runner matters, for
example when it must run `StateT`, `ExceptT`, or another carrier transformer
down to a final result type.


Why ConstIO Stays at the Bottom
-------------------------------

`ConstIO` is a real carrier, but it is not a general-purpose transformer layer.
It works by ignoring the lower monad `m`. That is exactly why it can collect
`Alg IO` operations into an `IO` action, and exactly why it cannot preserve
useful carrier behaviour underneath it.

To see where the requirements come from, look at the two parts of a handler.
Ignoring some internal wrappers, a handler has the following shape:
```haskell ignore
halg :: forall m. Monad m => Algebra oeffs m -> Algebra effs (Apply ts m)
hrun :: forall m. Monad m => Algebra oeffs m -> Apply ts m a -> m b
```
The algebra transformer `halg` explains how to interpret the input operations in
the carrier `Apply ts m`. The runner `hrun` explains how to run the final carrier
computation back down to the lower monad.

When a program is actually evaluated, the carrier computation must be a monad.
For example, `handle` has a constraint of this shape:
```haskell ignore
handle
  :: Monad (Apply ts Identity)
  => Handler effs '[] ts a b
  -> Prog effs a
  -> b
```
Handler composition needs the stronger reusable version: if `m` is a monad, then
`Apply ts m` must also be a monad. For a single carrier layer `t`, that is the
object-level requirement:
```haskell ignore
Monad m => Monad (t m)
```
This is weaker than being a `MonadTrans`. A `MonadTrans` also provides a way to
lift lower-monad actions through the layer:
```haskell ignore
lift :: Monad m => m a -> t m a
```
`ConstIO` satisfies the monad requirement: `ConstIO m` is a monad for every
`m`. It does not satisfy the transformer requirement:
```haskell ignore
lift :: Monad m => m a -> ConstIO m a
```
There is nowhere to put the `m a`, because `ConstIO m a` contains only an
`IO a`.

It helps to keep the names separate. A monad morphism is a
structure-preserving map between two particular monads:
```haskell ignore
type m ~> n = forall x. m x -> n x
```
For each lower monad `m`, the constructor and runner for `ConstIO` are monad
morphisms between `IO` and `ConstIO m`:
```haskell ignore
ConstIO    :: IO ~> ConstIO m
runConstIO :: ConstIO m ~> IO
```
Indeed, `ConstIO m` is just `IO` with a wrapper.

A monad transformer is different. It is a construction that takes any monad `m`
to a monad `t m`, together with a monad morphism from the base monad into the
transformed monad:
```haskell ignore
lift :: Monad m => m ~> t m
```
This is the morphism `ConstIO` does not have. It gives monad morphisms between
`IO` and `ConstIO m`, but not from an arbitrary lower monad `m` into
`ConstIO m`. So `ConstIO` is a constant monad-valued carrier, not a monad
transformer.

The concrete missing operation is lifting lower-carrier behaviour through the
layer. The standard `MonadTrans` class calls this operation `lift`; here is the
same shape in a small local class:
```haskell
class LiftBase t where
  liftBase :: Monad m => m a -> t m a
```
For comparison, `MaybeT` can implement this operation, and over the base monad
`Maybe` it keeps both `Just` and `Nothing` visible:
```haskell
instance LiftBase MaybeT where
  liftBase ma = MaybeT (fmap Just ma)

maybeTLiftJust :: Maybe (Maybe String)
maybeTLiftJust =
  runMaybeT (liftBase (Just "kept") :: MaybeT Maybe String)

maybeTLiftNothing :: Maybe (Maybe String)
maybeTLiftNothing =
  runMaybeT (liftBase (Nothing :: Maybe String) :: MaybeT Maybe String)
```
Evaluating these gives `Just (Just "kept")` and `Nothing`.

Now try to make `ConstIO` provide the same interface. The honest answer is to
omit the instance, because `liftBase` would need to turn an arbitrary `m a` into
an `IO a`. To make the failure executable, here is a deliberately broken
instance:
```haskell
instance LiftBase ConstIO where
  liftBase _ =
    ConstIO (ioError (userError "ConstIO cannot lift the base monad"))

constIOLiftJust :: IO String
constIOLiftJust =
  runConstIO (liftBase (Just "kept") :: ConstIO Maybe String)

constIOLiftNothing :: IO String
constIOLiftNothing =
  runConstIO (liftBase (Nothing :: Maybe String) :: ConstIO Maybe String)
```
Running `constIOLiftJust` is the surprising case: even `Just "kept"` fails.
The implementation has no way to inspect an arbitrary `m a` and extract the
`a`. Replacing the exception with a default value would be just as bad: it would
invent an `a` and discard the base monad's behaviour.

It is tempting to look for a different IO-shaped carrier that does preserve the
lower monad. The two most direct shapes put `IO` on one side of `m` or the other:
```haskell ignore
newtype InsideIO  m a = InsideIO  (m (IO a))
newtype OutsideIO m a = OutsideIO (IO (m a))
```
These are not monad transformers in the sense that matters for handlers: they
do not even turn every monad `m` into a monad `t m`. They have lift-shaped maps:
```haskell ignore
liftInsideIO :: Functor m => m a -> InsideIO m a
liftInsideIO ma = InsideIO (fmap pure ma)

liftOutsideIO :: m a -> OutsideIO m a
liftOutsideIO ma = OutsideIO (pure ma)
```
but lifting alone is not enough. A carrier transformer must also make `t m` a
monad for arbitrary monads `m`.

For `InsideIO`, bind would have to produce `m (IO b)`. After taking apart the
outer `m`, it can get an `IO a`, but the continuation has type:
```haskell ignore
a -> InsideIO m b
a -> m (IO b)
```
The only way to obtain the `a` is inside the `IO` action, but the result needed
from the continuation is in the outer `m`. That would require moving an
arbitrary `m` out from inside `IO`, which is not available in general.

For `OutsideIO`, bind has the dual obstruction. Running the outer `IO` gives an
`m a`, but the continuation needs an actual `a`:
```haskell ignore
a -> OutsideIO m b
a -> IO (m b)
```
For an arbitrary monad `m`, there may be no `a` to extract, or there may be many.
There is no general way to choose one and run the resulting `IO` action while
remaining inside `m`.

So the three simple shapes fail for different reasons. `ConstIO` is monadic and
therefore usable as a final carrier, but it is not a transformer because it
cannot lift the lower monad. `InsideIO` and `OutsideIO` can lift the lower monad
in an obvious way, but they do not provide the general monadic carrier that a
handler stack needs.

So `ConstIO` works as the collector at the bottom of the stack. Stacks such as
`'[MaybeT, ConstIO]` are fine: `MaybeT` is above `ConstIO`, and the final result
can be an `IO (Maybe a)`. But `ConstIO` cannot be the IO-running layer in the
middle of a stack. Once evaluation reaches `ConstIO`, the lower monad has been
ignored.

That boundary is the important one. You can either collect `IO` at the bottom
with `constIO`, or choose `IO` as the base monad with `handleIO` or
`handleM ioAlg`. What this construction does not provide is an IO carrier that
sits between other useful carrier layers.


The Danger of Putting ConstIO Too Early
---------------------------------------

The safe way to read `constIO` is: it should be the final handler in the
pipeline, after every handler whose carrier behaviour must be observed. These
shapes are the intended ones:
```haskell ignore
handle (teletypeIO |> constIO) echo
handle (Maybe.except |> constIO) program
handle (stateIORef ref |> constIO) program
```
In each case, the useful carrier layer is above `ConstIO`. `MaybeT` can decide
whether the result is `Nothing` or `Just`; `stateIORef` can emit `Alg IO`; only
then does `constIO` collect the remaining `Alg IO` operations into a final `IO`
action.

The dangerous mental model is to think of `ConstIO` as a neutral layer that
later handlers can still interact with. It is not neutral. Morally, it has this
shape:
```haskell ignore
ConstIO m a  ~=  IO a
```
There is no `m` inside the representation. Once evaluation has entered
`ConstIO`, the lower carrier is not part of the stored computation. A later
runner may still be type-correct in trivial cases, but it receives only a pure
lower-carrier value containing the collected `IO` action. It cannot observe
state updates, failures, logs, or other carrier behaviour from inside that
action, because those behaviours were never stored there.

If a later handler has actual input effects, the type system usually stops the
composition: those effects would have to be forwarded through `ConstIO`, and
`ConstIO` is not a transformer with a general lifting operation. The more subtle
problem is not unhandled operation syntax. It is that a lower carrier can be
present in the type without contributing meaningfully to the `IO` action that
`ConstIO` stores.

This is allowed because `Handler` does not promise that every carrier layer is
observationally relevant. It tracks which effects are consumed and which effects
remain. It also asks for forwarding evidence when operations must pass through a
carrier. It does not impose a noninterference law saying that a carrier must
preserve, run, or expose all carrier behaviour below it. The runner for
`constIO` has the essential shape:
```haskell ignore
forall m. Monad m => ConstIO m a -> m (IO a)
```
Since `ConstIO m a` contains only an `IO a`, the implementation can simply put
that `IO` action into the lower monad with `pure`. That is type-correct, but it
also explains the limitation: `m` is used only as the place where the final
`IO` action is returned, not as part of the computation being collected.

So the practical rule is stricter than the type alone: put `constIO` last in the
handler pipeline. If you need `IO` to coexist with carrier layers below it, use
`handleIO` or `handleM ioAlg` instead, so `IO` is the base monad rather than a
carrier that ignores its base.


Executable Checks
-----------------

These examples are part of the documentation test suite. They are not a proof
that `ConstIO` is a general-purpose `IO` transformer, but they check the useful
behaviour claimed above.

The contrast with `MaybeT` above is executable. `MaybeT` preserves base-monad
failure when lifted over `Maybe`:
```haskell
example_maybeT_lifts_base :: Property
example_maybeT_lifts_base = property $ do
  maybeTLiftJust === Just (Just "kept")
  maybeTLiftNothing === Nothing
```
The deliberately broken `ConstIO` instance cannot do the corresponding job.
Even lifting `Just "kept"` fails, because `ConstIO` cannot recover the value
from an arbitrary base monad:
```haskell
example_constIO_cannot_lift_base :: Property
example_constIO_cannot_lift_base = property $ do
  result <- H.evalIO (try constIOLiftJust :: IO (Either SomeException String))
  case result of
    Left _ -> return ()
    Right value -> do
      H.annotate ("unexpected lifted value: " ++ show value)
      H.failure
```

First, `handle constIO` constructs an `IO` action. The effects have not happened
until that returned action is run:
```haskell
recordIO :: Members '[Alg IO] effs => IORef [String] -> Prog effs [String]
recordIO ref = do
  io (modifyIORef ref (++ ["first"]))
  io (modifyIORef ref (++ ["second"]))
  io (readIORef ref)

example_constIO_returnsAction :: Property
example_constIO_returnsAction = property $ do
  ref <- H.evalIO (newIORef [])
  let action = handle constIO (recordIO ref)

  before <- H.evalIO (readIORef ref)
  before === []

  result <- H.evalIO action
  result === ["first", "second"]

  after <- H.evalIO (readIORef ref)
  after === ["first", "second"]
```

Second, `ConstIO` can sit at the bottom of a stack. Here `MaybeT` is above it,
so the final result is an `IO (Maybe a)`:
```haskell
runRecordIOMaybe :: IORef [String] -> IO (Maybe [String])
runRecordIOMaybe ref =
  handle (Maybe.except `fuse` constIO) (recordIO ref)

example_constIO_underMaybeT_success :: Property
example_constIO_underMaybeT_success = property $ do
  ref <- H.evalIO (newIORef [])
  result <- H.evalIO (runRecordIOMaybe ref)
  result === Just ["first", "second"]

  after <- H.evalIO (readIORef ref)
  after === ["first", "second"]
```

It also cooperates with failure in the layer above it. The first `IO` action has
already been sequenced before the failure; the second one is never reached:
```haskell
recordThenAbort :: Members '[Alg IO, Maybe.Throw] effs => IORef [String] -> Prog effs ()
recordThenAbort ref = do
  io (modifyIORef ref (++ ["before"]))
  Maybe.throw
  io (modifyIORef ref (++ ["after"]))

runRecordThenAbort :: IORef [String] -> IO (Maybe ())
runRecordThenAbort ref =
  handle (Maybe.except `fuse` constIO) (recordThenAbort ref)

example_constIO_underMaybeT_abort :: Property
example_constIO_underMaybeT_abort = property $ do
  ref <- H.evalIO (newIORef [])
  result <- H.evalIO (runRecordThenAbort ref)
  result === Nothing

  after <- H.evalIO (readIORef ref)
  after === ["before"]
```

Finally, state operations can be interpreted through `IORef` rather than through
the usual `StateT` carrier. This handler consumes `Get` and `Put`, and emits
`Alg IO` actions that read and write the reference:
```haskell

bumpTwice :: Members '[State.Get Int, State.Put Int] effs => Prog effs Int
bumpTwice = do
  n <- State.get @Int
  State.put @Int (n + 1)
  m <- State.get @Int
  State.put @Int (m + 1)
  State.get @Int
```
Using the standard `StateT` handler, `bumpTwice` returns the final value and
final state:
```haskell
example_ioRefState_matchesStateT :: Property
example_ioRefState_matchesStateT = property $
  (handle (State.state (10 :: Int)) bumpTwice :: (Int, Int)) === (12, 12)
```
Using `stateIORef`, the same state transitions happen in `IO` by mutating the
reference:
```haskell
runBumpTwiceIORef :: IORef Int -> IO Int
runBumpTwiceIORef ref =
  handleIO (stateIORef ref) bumpTwice

example_ioRefState_handleIO :: Property
example_ioRefState_handleIO = property $ do
  ref <- H.evalIO (newIORef 10)
  result <- H.evalIO (runBumpTwiceIORef ref)
  result === 12

  final <- H.evalIO (readIORef ref)
  final === 12
```
The same IORef-backed handler can also be composed with `constIO`, so the whole
program is evaluated by `handle`:
```haskell
runBumpTwiceIORefWithHandle :: IORef Int -> IO Int
runBumpTwiceIORefWithHandle ref =
  handle (stateIORef ref |> constIO) bumpTwice

example_ioRefState_handleConstIO :: Property
example_ioRefState_handleConstIO = property $ do
  ref <- H.evalIO (newIORef 10)
  result <- H.evalIO (runBumpTwiceIORefWithHandle ref)
  result === 12

  final <- H.evalIO (readIORef ref)
  final === 12
```


Summary
-------

The rule from the start can now be read precisely:

* Use `handle (h |> constIO)` when `h` translates the remaining operations into
  `Alg IO` and `ConstIO` can sit at the bottom of the stack.
* Use `handleIO h` when you want to choose `IO` as the base monad directly.
  This is the same idea as `handleM ioAlg h`.
* Use `evalAT'` when an algebra transformer alone is enough and no handler
  runner is needed.
* Put `constIO` last in the handler pipeline. It ignores the lower monad, so it
  cannot preserve useful carrier behaviour underneath it.

```haskell
examples :: Group
examples = $$(discoverPrefix "example_")
```
