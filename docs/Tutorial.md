<!--
```haskell
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}

module Tutorial where

import Prelude hiding (getLine, putStrLn)
import qualified Prelude

import Control.Effect
import Control.Effect.IO
import Control.Effect.Writer
import Control.Effect.State

import Data.IORef
import Data.Int (Int64)
import Data.Word (Word64)

import System.CPUTime (getCPUTime)
import System.Mem (getAllocationCounter)

import Hedgehog hiding (eval)
```
-->

Programs and Handlers
=====================

A value of type `Prog effs a` is a *syntax tree* that consists of operations
drawn from `effs`, which is known as the *effect signature*. The syntax
tree returns values of `a`. The tree is entirely syntactic: it describes the shape
of a program but not how that should be interpreted. The interpretation
is decided later by a handler.

Operations
----------

The `effective` library provides operations for many of the standard effects
provided by monads.
The state effect, from `Control.Effect.State`, offers two operations: one
that gets a stored value of type `s` from the state, and another that puts
such a value into the state.

Here are their signatures:
```haskell ignore
get :: Member (Get s) effs => Prog effs s
put :: Member (Put s) effs => s -> Prog effs ()
```
The `Member` constraints say that these are programs whose effect signature
`effs` contains the effect types `Get s` or `Put s`, but is otherwise
unconstrained.

Looking at these types, an operation is characterised by two things:

* its *parameters*, the data that the operation may make use of; and
* its *arity*, the type of value that the operation returns to the program.

So `put` has a single parameter of type `s`, the new state, and its arity is
`()`; `get` has no parameters, and its arity is `s`, the current state.

Operations are combined into programs using `do` notation. Here is a program
that increments the state by a given `n`:
```haskell
incr :: Members '[Put Int, Get Int] effs => Int -> Prog effs ()
incr n = do x <- get
            put (x + n)
```
The `Members` constraint collects the `Member` constraints of the operations
used. This shape of type is common enough that the library provides a
synonym, so the type of `incr` can equivalently be written as:
```haskell ignore
incr :: Int -> () ! '[Put Int, Get Int]
```
The `incr` program does not directly modify any state: it builds the syntax tree of a
program in which a `Get` operation is followed by a `Put` operation carrying
the incremented value. Giving the syntax meaning is the job of a *handler*.

Executing the `incr` program with the `state s` handler can be achieved as follows:
```console
ghci> handle (state (40 :: Int)) (incr 2)
((),42)
```
This starts with a state of `40` and runs the `incr 2` program.
Since the program has type `() ! '[Put Int, Get Int]`, with a pure value of `()`,
the result of applying the handler is a value of type `((), Int)`,
where the first component is the pure result and the second is the
resulting state.
<!--
```haskell
example_incr :: Property
example_incr = property $
  handle (state (40 :: Int)) (incr 2) === ((), 42)
```
-->

The `state s` handler has a signature that describes the effects it interacts
with:
```haskell ignore
state :: s -> Handler '[Put s, Get s]   -- input effects
                      '[]               -- output effects
                      '[StateT s]       -- transformers
                      a                 -- input type
                      (a, s)            -- output type
```
The signature of the handler indicates some of its behaviour:
* **Input effects**: The input effects will be processed and removed by this handler.
  In `state s` the input effects are `Put s` and `Get s`.
* **Output effects**: The output effects will be produced by this handler.
  In `state s` the output effects are empty.
* **Transformers**: The transformers are used to provide semantics to the input effects.
  In `state s` there is only one transformer `StateT s`.
* **Input/output types**: The input/output types are the types of the return values
  of an effectful program before/after applying the handler. When `state s` is used
  to handle a program of type `Prog effs a`, the output will be the type `(a, s)`.

A handler can be applied when it can process all the effects in a program,
which is indicated by having empty output effects. The `handle` function
ensures that this is the case:
```haskell ignore
handle :: Monad (Apply ts Identity)
       => Handler effs '[] ts a b
       -> Prog effs a -> b
```
The key aspect of `handle` is that it takes a `Prog effs a` program
and processes it into some type `b`, as determined by the handler.

The `Apply ts Identity` constraint applies each of the transformers
in the list `ts` to the `Identity` monad. More precisely,
if a transformer list `ts = [t3, t2, t1]` is applied to a monad `m` 
we have `Apply [t3, t2, t1] m a = t3 (t2 (t1 m)) a`.
This is not typically information that users of effects need to worry about,
but ensures that handlers are able to forward effects appropriately.

Working with IO
---------------

The `effective` library also allows users to work with `IO` by using
`io :: IO a -> a ! '[Alg IO]` to embed IO into a program:
```haskell
helloIO :: String ! '[Alg IO]
helloIO = do name <- io (do Prelude.putStrLn "What is your name?"
                            Prelude.getLine)
             io (Prelude.putStrLn ("Hello " ++ name ++ "!"))
             return name
```
The `io` operation will embed subprograms of type `IO a` into the program,
and these are then executed using the `constIO` handler:
```haskell ignore
constIO :: Handler '[Alg IO] '[] '[ConstIO] a (IO a)
```
This handler interprets all the `Alg IO` nodes in the tree by simply
performing the IO action:
```haskell
exampleHello :: IO String
exampleHello = handle constIO helloIO
```
Executing this program asks for a name as input and sends an appropriate
greeting message before returning the name that was typed.

```console
ghci> exampleHello
What is your name?
World
Hello World!
"World"
```

Fusing Handlers
----------------

Programs can be constructed that include a combination of operations that
need to be handled by different handlers.
For instance, we can simply combine the previous two programs to make one
that increments the state as well as greets the user:
```haskell
helloIncr :: () ! '[Get Int, Alg IO, Put Int]
helloIncr = do name <- helloIO
               incr (length name)
```
Notice that the signature now reflects that the program now has a combination
of effects. Also notice that the order of effects in the signature does not matter:
they can be thought of as a set.

One way to combine two handlers is to *fuse* them together using `|>` (a synonym for `fuse`). 
```haskell
exampleHelloIncr :: IO ((), Int)
exampleHelloIncr = handle (state (40 :: Int) |> constIO) helloIncr
```
This combines the `state 40` handler and the `constIO` handler
into one that can deal with all the effects that they can.
It does so by processing all the effects that `state 40` recognises,
and then processes all the effects that `constIO` recognises.

Executing this in the terminal produces:
```console
ghci> exampleHelloIncr
What is your name?
World
Hello World!
((),45)
```
The type of the fused handlers shows that the operations
for `Put Int`, `Get Int` and also `Alg IO` are handled:
```haskell ignore
state (40 :: Int) |> constIO
  :: Handler '[Put Int, Get Int, Alg IO]
             '[]
             [StateT Int, ConstIO]
             a
             (IO (a, Int))
```
More generally, the type of `|>` is somewhat difficult to read,
because it has sophisticated constraints, but here is a
simplified version:
```haskell ignore
(|>) :: ... 
        o1 ~ i2
     => Handler effs1 oeffs1 ts1 i1 o1
     -> Handler effs2 oeffs2 ts2 i2 o2
     -> Handler (Union effs1 effs2)
                (Union (oeffs1 :\\ effs2) oeffs2)
                (ts1 :++ ts2)
                i1
                o2
```
The input effects of the combination are the union of `effs1` and `effs2`.
The output effects are not quite the union of `oeffs1` and `oeffs2` because
any effects in `oeffs1` that are recognised by `h2` will be interpreted.
Notice also that the output type of `h1` must be the input type of `h2`.

A natural question is whether it is possible to change the handler order.
This can sometimes be done, but in the case above it results in a type
error:
```console
ghci> handle (constIO |> state (40 :: Int)) helloIncr
<interactive>:36:17: error: [GHC-39999]
    • No instance for ‘transformers-0.6.1.2:Control.Monad.Trans.Class.MonadTrans
                         ConstIO’
        arising from a use of ‘|>’
    • In the first argument of ‘handle’, namely
        ‘(constIO |> state (40 :: Int))’
      In the expression: handle (constIO |> state (40 :: Int)) helloIncr
      In an equation for ‘it’:
          it = handle (constIO |> state (40 :: Int)) helloIncr
```
The error message tells us that `ConstIO` is not a monad transformer,
and this is a requirement for the effects to be forwarded through `|>` appropriately.
In other words, `constIO` must be the final handler that is applied because
it does not support effect forwarding.


Interpreting Operations
-----------------------

One fundamental operation that can be done with effect handlers is to
*interpret* some operation in terms of another.
For instance, the `Get s` and `Put s` effects could be interpreted
in terms of `Alg IO` by making use of a mutable variable for the state `s`.

To do this, we can use `ref :: IORef s` which is a reference to the state and is interacted 
with using `writeIORef` and `readIORef`.
The definition of the handler uses `interpret`, which takes a number
of clauses that deal with the effect constructors `Put s k` and `Get k`:
```haskell
stateIORef :: IORef s -> Handler '[Put s, Get s] '[Alg IO] '[] a a
stateIORef ref = interpret $
  (\(Put s k) -> do io (writeIORef ref s); return k) :%
  (\(Get k)   -> do s <- io (readIORef ref); return (k s)) :% emptyCase
```
The parameter `k` is known as the *continuation* parameter, and represents
the point at which the program that follows this operation belongs.

This can be composed with the `constIO` handler to have a program
that counts using mutable state:
```haskell
exampleIORef :: IO Int
exampleIORef = do ref <- newIORef (40 :: Int)
                  handle (stateIORef ref |> constIO) (incr 2)
                  readIORef ref
```


Generic Operations
------------------

An important feature of `effective` is that it allows users to define their own operations.
To do so, the following must be defined:

1. **Operation Signature:** A datatype for the underlying operation
2. **Pattern Synonym:** A pattern synonym to facilitate matching on syntax 
3. **Smart Constructor:** A smart constructor to enable programs to use the operation

In practice, this is most easily done by using a *generator*.

A *generic operation* is described by exactly its name, its (optional) parameters,
and its arity. The splice `makeGen` is a *generic generator* that takes an
operation signature and produces the necessary boilerplate:
```haskell
$(makeGen [e| getLine  :: String |])
$(makeGen [e| putStrLn :: String ~> () |])
```
This is an *algebraic signature* of the operation: the parameters, if any, are written
before a `~>`, and the final type is the arity. Thus `getLine :: String` says
that `getLine` has no parameters and returns a `String`, while
`putStrLn :: String ~> ()` says that `putStrLn` carries a `String` and
returns `()`.

Using `makeGen` generates an effect type named after the operation,
`GetLine` and `PutStrLn` respectively, together with a smart constructor
whose type follows the same shape as the built-in operations:
```haskell ignore
getLine  :: Member GetLine effs  => Prog effs String
putStrLn :: Member PutStrLn effs => String -> Prog effs ()
```
The new operations are used just as before to construct a program that
greets the user.
```haskell
hello :: Members '[GetLine, PutStrLn] effs => Prog effs String
hello = do putStrLn "What is your name?"
           name <- getLine
           putStrLn ("Hello " ++ name ++ "!")
           return name
```
This is essentially the same as before, but with an important
difference: we can intercept `putStrLn` and `getLine` and interpret
them differently, since they are not the standard IO operations.

Alongside the smart constructor, each splice generates a pattern synonym,
`GetLine` and `PutStrLn`, which is how a handler takes the syntax apart.
The most direct understanding of this program is to use the corresponding
operations from `Prelude` for `getLine` and `putStrLn`.
As before we can use `io` to achieve this:
```haskell
teletypeIO :: Handler '[GetLine, PutStrLn] '[Alg IO] '[] a a
teletypeIO = interpret $
  (\(GetLine k)     -> do x <- io (Prelude.getLine); return (k x)) :%
  (\(PutStrLn xs k) -> do io (Prelude.putStrLn xs); return k) :% emptyCase
```

Piping Effects
--------------

An alternative way to deal with `GetLine` is to provide it with input from
a list of strings, rather than expect it from user input. We will
achieve this by interpreting `getLine` in terms of `get` and `put`
operations with some internal state that holds a list of input strings.

Since we are focusing on interpreting only one effect, we can use `interpret1`:
```haskell
getLineState :: Handler '[GetLine] '[Get [String], Put [String]] '[] a a
getLineState = interpret1 rephrase where
  rephrase :: GetLine m x -> Prog [Get [String], Put [String]] x
  rephrase (GetLine k) = do xss <- get
                            case xss of
                              []        -> return (k "")
                              (xs:xss') -> do put xss'
                                              return (k xs)
```
The definition of `rephrase` provides the system with the
information on how to proceed when a `getLine` is matched.
This is done by matching on the syntax `GetLine k`, where
`k` is a continuation that corresponds to the program that follows this
operation. Since the arity of `getLine` is `String`, the continuation
`k` requires a string to continue.

Although it would be possible to handle these effects by using the fuse operator
as before, this produces a handler that does more than we want. To understand
why, consider the type of fusing them together:
```haskell ignore
getLineState |> state ["World"]
  :: Handler '[GetLine, Put [String], Get [String]]  -- This exposes too much!
             '[]
             '[StateT [String]]
             a
             (a, [String])
```
The issue is that this handler will interpret any `put` and `get`
operations that exist in the original program. This handler has
leaked the fact that we are reinterpreting `GetLine` with those operations.

The *pipe* combinator, written `\\`, deals with this case by making the second handler
intercept only what comes out of the first handler. In particular:
```haskell ignore
(getLineState \\ state ["World"])
  :: Handler '[GetLine] 
             '[] 
             '[StateT [String]]
             a 
             (a, [String])
```
Here we see that `get` and `put` have been interpreted, but that the
composition does not intercept those in the input effects.

The (simplified) type of `pipe` is:
```haskell ignore
(\\) ::...
        o1 ~ i2
     => Handler effs1 oeffs1 ts1 i1 o1
     -> Handler effs2 oeffs2 ts2 i2 o2
     -> Handler effs1
                (Union (oeffs1 :\\ effs2) oeffs2)
                (ts1 :++ ts2)
                i1
                o2
```
In contrast to `fuse`, this only intercepts `effs1`,
but otherwise the signature is the same.

Now we are able, for instance, to test our `hello` program
with the following:
```console
ghci> handle ((getLineState \\ state ["World"]) |> teletypeIO |> constIO) hello
What is your name?
Hello World!
("World",[])
```
This still interacts with the terminal in that values are
printed, but it takes input from the supplied state.


Hiding Effects
--------------

A related operation is the `hide` combinator, which allows us to *hide* the
`Get [String]` and `Put [String]` effects in the resulting handler:
```haskell ignore
hide (Proxy @'[Get [String], Put [String]]) (getLineState |> state ["World"])
  :: Handler '[GetLine]    -- `Get [String]` and `Put [String]` are no longer exposed
             '[] 
             '[StateT [String]] 
             a 
             (a, [String])
```
This handler will not intercept `Get [String]` and `Put [String]` effects.

However, there is a catch: if the first handler in this composition itself wants
to handle those effects, then that would no longer be possible because `hide`
will remove the effects entirely.

The law that relates `fuse`, `pipe`, and `hide` is:
```haskell ignore
h1 \\ h2 === hide (Proxy @(effs2 :\\ effs1)) (h1 |> h2)
```
The (simplified) type of `hide` is:
```haskell ignore
hide :: Proxy heffs
     -> Handler effs oeffs ts a b
     -> Handler (effs :\\ heffs) oeffs ts a b
```


Manual Definition
-----------------

An operation described by `makeGen` defines a corresponding signature,
smart constructor, and pattern synonym.
For instance, generating `$(makeGen [e| getLine  :: String |])` produces:

```haskell ignore
type GetLine = Alg GetLine_

data GetLine_ k = GetLine_ (String -> k)
  deriving Functor

pattern GetLine k = Alg (GetLine_ k)

getLine :: Member GetLine effs => Prog effs String
getLine = call (GetLine id)
```

The code that corresponds to `$(makeGen [e| putStrLn :: String ~> () |])`
produces a datatype that has a `String` as a parameter, and has an
arity of `()`, which corresponds to one continuation:
```haskell ignore
type PutStrLn = Alg PutStrLn_

data PutStrLn_ k = PutStrLn_ String k
  deriving Functor

pattern PutStrLn str k = Alg (PutStrLn_ str k)

putStrLn :: Member PutStrLn effs => String -> Prog effs ()
putStrLn str = call (PutStrLn str ())
```
It would have been possible, and indeed more consistent, to define this where the continuation
is explicitly of type `() -> k`. However, this clutters the operation needlessly, so
by convention when the arity is `()` our library makes the continuation take no argument.


Algebraic Operations
--------------------

A different way of defining operations is to use an *algebraic generator*.
Here, an operation `op` has an arity which is a natural number `n`, and
produces an operation that takes `n` subprograms as parameters, each
corresponding to a continuation.

Here is an example of using an algebraic operation `confirm`,
where the program `confirm message p q` will display 
`message` and proceed with `p` if the user confirms they
want to continue and with `q` otherwise.
```haskell
$(makeAlg [e| confirm :: String ~> 2 |])
```
The confirmation is implemented as a handler that
translates `confirm` into `putStrLn` and `getLine` effects,
and decides how to render the question and receive the response:
```haskell
confirmYN :: Handler '[Confirm] '[PutStrLn, GetLine] '[] a a
confirmYN = interpret1 $ \(Confirm question yes no) ->
  do putStrLn (question ++ " [y/N]")
     line <- getLine
     return (if line `elem` ["y", "Y"] then yes else no)
```
Now the operation can be used to execute `hello` multiple times:
```haskell
hellos :: Members '[PutStrLn, GetLine, Confirm] effs => Prog effs [String]
hellos = do name <- hello
            confirm "Greet someone else?"
              (do names <- hellos
                  return (name : names))
              (do putStrLn "Goodbye!"
                  return [name])

exampleHellos :: IO [String]
exampleHellos = 
  handle (confirmYN |> teletypeIO |> constIO) hellos
```
The program can be executed to collect the names of
people that were greeted:
```console
ghci> exampleHellos
What is your name?
Alice
Hello Alice!
Greet someone else? [y/N]
y
What is your name?
Bob
Hello Bob!
Greet someone else? [y/N]

Goodbye!
["Alice","Bob"]
```

<!--
```haskell
putStrLnState :: Handler '[PutStrLn] '[Get [String], Put [String]] '[] a a
putStrLnState = interpret1 $ \(PutStrLn s k) ->
  do out <- get
     put (out ++ [s])
     return k

example_hellos :: Property
example_hellos = property $
  handle (confirmYN |> (getLineState \\ state_ ["Alice", "y", "Bob", ""])
                    |> (putStrLnState \\ state [])) hellos
    === ( ["Alice", "Bob"]
        , [ "What is your name?"
          , "Hello Alice!"
          , "Greet someone else? [y/N]"
          , "What is your name?"
          , "Hello Bob!"
          , "Greet someone else? [y/N]"
          , "Goodbye!"
          ] )
```
-->

Scoped Operations
-----------------

Algebraic and generic operations are not the only kinds of operations that
are supported. Another family are *scoped* operations, which allow the
operation to have code as a parameter. We will demonstrate this with logging
and timestamps.

For the purposes of this example, we will use the `tell` operation to log information.
This operation is then interpreted using the `writer` handler which allows
anything that was told to be inspected.
```haskell
helloTell :: String ! '[Tell [String], Alg IO, GetLine, PutStrLn]
helloTell = do tell ["Entering hello"]
               name <- hello
               tell ["Exiting hello"]
               return name
```
This will log the message before and after `hello` is executed:
```console
ghci> handle (writer @[String] |> teletypeIO |> constIO) helloTell
What is your name?
World
Hello World!
(["Entering hello","Exiting hello"],"World")
```

Timestamps are often used in conjunction with logging so that the time a message
is logged can be recorded. This can be done by
automatically augmenting `tell` with the appropriate timestamp:
```haskell
tellTime :: forall w a . Handler '[Tell w] '[Tell [(Integer, w)], Alg IO] '[] a a
tellTime = interpret1 $ \(Tell (w :: w) k) ->
  do time <- io getCPUTime
     tell [(time, w)]
     return k
```
This way, we have the option to log the time by adding the `tellTime` handler if desired.
Now a timestamp is added to the start of messages emitted by `tell`:
```console
ghci> handle (tellTime @[String] |> writer @[(Integer, [String])] |> teletypeIO |> constIO) helloTell
What is your name?
World
Hello World!
([(623190000000,["Entering hello"]),(623252000000,["Exiting hello"])],"World")
```
<!--
```haskell
example_tellTime :: Property
example_tellTime = property $ do
  (msgs, name) <- Hedgehog.evalIO $
    handle (tellTime @[String] |> writer @[(Integer, [String])]
                               |> (getLineState \\ state_ ["World"])
                               |> (putStrLnState \\ state_ ([] :: [String]))
                               |> constIO) helloTell
  (map snd msgs, name) === ([["Entering hello"], ["Exiting hello"]], "World")
```
-->

A different interface is to use a *scoped operation* that marks
part of the program as of interest for profiling.
```haskell
$(makeScp [e|profile :: String ~> 1|])
```

For example, to profile some code `p`, we need to mark it as code of interest
by writing `profile name p`, where `name` is some identifier that we wish to see
in the log. Then, we must decide which instrument we want to use to measure
what happens to `p`. An instrument measures some quantity of interest, such as
time, memory, energy, or bandwidth.

For example, the `timer` handler can be invoked to measure time. This injects
`getCPUTime` operations to measure the time `t` before and `t'` after `p`
is executed. Then `tell` emits a pair consisting of `(name, t' - t)`,
thus showing how much time was spent in `p`.

```haskell
timer :: Handler '[Profile] '[Tell [(String, Integer)], Alg IO] '[] a a
timer = interpretM1 $ \oalg (Profile name p) ->
  do t  <- eval oalg (io getCPUTime)
     k  <- p
     eval oalg (do t' <- io getCPUTime
                   tell [(name, t' - t)])
     return k
```
How exactly `getCPUTime` is measured, and what is done with the `tell` is left
to another handler. This easily allows, for instance, different ways of measuring time
to be implemented, or for logs to be enabled and disabled.

More generally, there may be other instruments that could be used, and indeed
the `timer` handler can alternatively be defined by using `profiler`:
```haskell
timer' :: Handler '[Profile] '[Tell [(String, Integer)], Alg IO] '[] a a
timer' = profiler (flip (-)) (io getCPUTime)
```
A new `profiler f instrument` will inject the `instrument` before and after
a program marked `profile "name" p` and collect two measurements: one before
`p` and another after `p` is executed. These are then combined by the given
function `f` and emitted using `tell`.
```haskell
profiler :: Member (Tell [(String, b)]) oeffs
         => (a -> a -> b) -> Prog oeffs a -> Handler '[Profile] oeffs '[] c c
profiler f instrument = interpretM1 $ \oalg (Profile name p) ->
  do t  <- eval oalg instrument
     k  <- p
     eval oalg (do t' <- instrument
                   tell [(name, f t t')])
     return k
```

An alternative use of profiling would be to count memory allocation,
or perhaps even both time and allocation together:
```haskell
allocs :: Handler '[Profile] '[Tell [(String, Int64)], Alg IO] '[] a a
allocs = profiler (-) (io getAllocationCounter)

timeAllocs :: Handler '[Profile] '[Tell [(String, (Integer, Int64))], Alg IO] '[] a a
timeAllocs = profiler (\(t, m) (t', m') -> (t' - t, m - m'))
                      (do t <- io getCPUTime
                          m <- io getAllocationCounter
                          return (t, m))
```

For our teletype example, we can instrument all of the `getLine` operations
with a profiler as follows:
```haskell
getLineProfile :: Handler '[GetLine] '[Profile, GetLine] '[] a a
getLineProfile = interpret1 $ \(GetLine k) ->
  profile "getLine" (getLine >>= return . k)
```
```console
ghci> handle (getLineProfile |> timeAllocs |> writer @[(String, (Integer, Int64))] |> teletypeIO |> constIO) hello
What is your name?
World
Hello World!
([("getLine",(4154000000,22720))],"World")
```
So, this takes approximately 4.154 milliseconds of CPU time, since `getCPUTime`
reports picoseconds, and allocates about 22.72 kilobytes of memory.
<!--
```haskell
example_timeAllocs :: Property
example_timeAllocs = property $ do
  (msgs, name) <- Hedgehog.evalIO $
    handle (getLineProfile |> timeAllocs |> writer @[(String, (Integer, Int64))]
                           |> (getLineState \\ state_ ["World"])
                           |> (putStrLnState \\ state_ ([] :: [String]))
                           |> constIO) hello
  (map fst msgs, name) === (["getLine"], "World")
```
-->

<!--
```haskell
examples :: Group
examples = $$(discoverPrefix "example_")
```
-->
