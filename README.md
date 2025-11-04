[![Build Status](https://github.com/zenzike/effective/actions/workflows/ci.yml/badge.svg)](https://github.com/zenzike/effective/actions)

Effective
==========

The `effective` library is an effect handlers library for Haskell that is
designed to allow users to define and interpret their own languages and
effects. This library incorporates support for:

* Algebraic, scoped, and other higher-order effects.
* Modular effect handlers.
* Staged effectful programming using Typed Template Haskell.


README
------

This README is a literate Haskell file and therefore can be executed:
```console
git clone effective
cd effective
cabal test readme
cabal repl readme
```
This should test some properties and then bring you into `ghci` where you can follow the examples.[^Imports]


A Tiny Calculator
-----------------

Effect handlers are used to annotate a program with the operations it uses,
and to allow those operations to be interpreted using different effects.

For example, suppose we are trying to implement a calculator that
evaluates a tiny expression language:
```haskell
data Expr = Lit Int | Var String | Add Expr Expr
  deriving Show
```
The calculator program takes these expressions and, using an operation
`lookup` that finds the value of a literal, will output the result:
```haskell
calc :: Expr -> Progs '[Lookup String Int] Int
calc (Lit n)   = return n
calc (Var x)   = lookup x
calc (Add a b) = do x <- calc a ; y <- calc b ; return (x + y)
```
This `calc` program relies on an implementation of `lookup` to
provide the values of the variables.

The `lookup` operation is created by the user simply by writing:
```haskell ignore
data Lookup_ key val k = Lookup_ key (val -> k)
  deriving Functor
$(makeAlg ''Lookup)
```
This has the effect of creating the following code:
```haskell
-- Underlying signature functor
data Lookup_ key val k = Lookup_ key (val -> k)
  deriving Functor

-- Effect synonym
type Lookup key val = Alg (Lookup_ key val)

-- Bidirectional pattern for matching/injecting Lookup operations
pattern Lookup :: Member (Lookup key val) eff
               => key -> (val -> k) -> Effs eff m k
pattern Lookup k f <- (prj -> Just (Alg (Lookup_ k f)))
  where
    Lookup k f = inj (Alg (Lookup_ k f))

-- Smart constructor: request the value of a key
lookup :: Member (Lookup key val) sig => key -> Prog sig val
lookup k = call (Alg (Lookup_ k id))
```
We can give a pure interpretation of `lookup` directly, by passing
in an environment association list:
```haskell
lookupEnv :: [(String, Int)] -> Handler '[Lookup String Int] '[] '[] a a
lookupEnv env = interpret $ \(Lookup var k) ->
  return (k (maybe 0 id (Prelude.lookup var env)))
```
Then, executing this code means using `handle`:
```haskell
runEval :: [(String, Int)] -> Expr -> Int
runEval env e = handle (lookupEnv env) (calc e)
```

Although this code works, it is not ideal because when a value is not
found in the environment, we simply return `0`. A better
alternative would be to perform another lookup, so that a different handler
can ask for the information:
```
lookupEnv' :: [(String, Int)] -> Handler '[Lookup String Int] '[Lookup String Int] '[] a a
lookupEnv' env = interpret $ \(Lookup var k) ->
  case Prelude.lookup env of
    Nothing  -> lookup var >>= k
    Just val -> return (k val)
```

One way to deal with a lookup is simply to fail whenever we ask for information:










A different handler to interact with `Lookup` can use `State`:
```haskell
freeVars :: Handler '[Lookup String Int] '[Get [String], Put [String]] '[] a a
freeVars = interpret $ \(Lookup x k) -> do
  xs <- get @[String]
  put (if elem x xs then xs else (insert x xs))
  return (k (0 :: Int))
```
But this is not very satisfactory: we had to return 0 into each
continuation, and the output value is not the calculation we want.
```haskell
exampleVars :: ([String], Int)
exampleVars = handle (freeVars |> state [])
                     (calc (Add (Var "x") (Var "y")))

-- ghci> exampleVars
-- (["x","y"],0)
```
A better solution is to find an appropriate value for the continuation `k`,
and so another lookup can be performed:
```haskell
freeVars' :: Handler '[Lookup String Int] '[Get [String], Put [String], Lookup String Int] '[] a a
freeVars' = interpret $ \(Lookup x k) -> do
  n <- lookup x
  xs <- get @[String]
  put (if elem x xs then xs else (insert x xs))
  return (k (n :: Int))
```
This new `lookup` inside the code block is not the one that is handled by
`freeVars'`, but will instead be picked up by whatever handler follows.

For instance, we can feed in the environment we want as before:
```haskell
exampleVars' :: ([String], Int)
exampleVars' = handle (freeVars' |> state [] |> lookupEnv [("x", 18), ("y", 24)])
                      (calc (Add (Var "x") (Var "y")))

exampleVars'' :: ([String], Int)
exampleVars'' = handle (freeVars' |> lookupEnv [("x", 18), ("y", 24)] |> state [])
                       (calc (Add (Var "x") (Var "y")))

-- ghci> exampleVars'
-- (["x","y"],42)
```
Better still we, can now create a new handler that uses the result
of the free variables in the state to query the user for the values they want:
```haskell
queryVars :: Handler '[Lookup String Int] '[Get [(String, Int)], Put [(String, Int)], Alg IO] '[] a a
queryVars = interpret $ \(Lookup var k) -> do
  env <- get
  case Prelude.lookup var env of
    Nothing  -> do io (Prelude.putStrLn ("Enter a value for " ++ var))
                   (val :: Int) <- read <$> io (Prelude.getLine)
                   put (insert (var, val) env)
                   return (k val)
    Just val -> return (k val)

queryVarsIO :: Handler '[Lookup String Int] '[Alg IO] '[] a a
queryVarsIO = interpret $ \(Lookup var k) -> do
    io (Prelude.putStrLn ("Enter a value for " ++ var))
    (val :: Int) <- read <$> io (Prelude.getLine)
    return (k val)

-- queryVarsCached  :: Handler '[Lookup String Int] '[Lookup String Int, Get [(String, Int)], Put [(String, Int)]] '[] a a
-- quaryVarsCached = intepret $ \(Lookup var k) -> do
--   env <- get
--   case Prelude.lookup var env of
--     Nothing ->  do val <- lookup var
--                    put (insert (var, val) env)
--                    return (k val)
--     Just val -> undefined -- as with cachedFX'
```

```haskell
exampleVars''' :: IO ([(String, Int)], Int)
exampleVars''' = handleIO (queryVars |> state ([] :: [(String, Int)]))
                          (calc (Add (Var "x") (Var "y")))

-- ghci> exampleVars'''
-- Enter a value for x
-- 18
-- Enter a value for y
-- 24
-- ([("x",18),("y",24)],42)


-- exampleVars'''' :: IO ([(String, Int)], Int)
-- exampleVars'''' = handleIO (lookupEnv [("x", 18), ("y", 24)] |> queryVars)
--                            (calc (Add (Var "x") (Var "y")))
```

Working with IO
----------------

A core idea of effect handlers is to produce a program with an
*effect signature* that describes the kinds of operations that the
program makes use of.

For example, creating a `Teletype` program is a rite of passage for monadic IO
[^Gordon1992] where the challenge is to show how IO of reading from and writing
to the terminal can be achieved. A program that interacts with the terminal is
`echo`. This is a simple program that will continue to echo the input obtained
by `getLine` is output to the terminal using `putStrLn` until a blank line is
received by
`getLine`:
```haskell
echo :: Progs [GetLine, PutStrLn] ()
echo = do str <- getLine
          case str of
            [] -> return ()
            _  -> do putStrLn str
                     echo
```
The type signature stipulates that `echo` is a family of programs whose effect
signature contains `[GetLine, PutStrLn]`, and returns a result of type `()`.
The effect signature says that this is a program that may require
the corresponding `getLine` and `putStrLn` operations.

In this example, `getLine` and `putStrLn` are user-defined operations
with the following types:
```haskell ignore
getLine  :: Member GetLine sig  => Prog sig String
putStrLn :: Member PutStrLn sig => String -> Prog sig ()
```
This states that they are programs whose signature `sig` contain
`GetLine` and `PutStrLn`, respectively. Later, we will see
how these are defined.

In `effective`, a program is an entirely syntactic construction. To give
it a semantics, a *handler* must be invoked that provides the interpretation
of the syntax.

The most obvious interpretation of `getLine` and `putLine` is to invoke their
corresponding values from the prelude:
```haskell
getLineIO :: Handler '[GetLine] '[Alg IO] '[] a a
getLineIO = interpret (\(GetLine k) -> do x <- io (Prelude.getLine); return (k x))

putStrLnIO :: Handler '[PutStrLn] '[Alg IO] '[] a a
putStrLnIO = interpret (\(PutStrLn xs k) -> do x <- io (Prelude.putStrLn xs); return k)

teletypeIO :: Handler '[GetLine, PutStrLn] '[Alg IO] '[] a a
teletypeIO = interpret
  (\case (GetLine k)     -> do x <- io (Prelude.getLine); return (k x)
         (PutStrLn xs k) -> do x <- io (Prelude.putStrLn xs); return k)
```
Later we will look at all the parameters of a `Handler` more carefully,
but for the present purposes, the first parameter indicates the
*input* effects that are consumed (`GetLine` and `PutStrLn`),
and the second parameter indicates the *output* effects
that are produced (`Alg IO`).



```haskell
type GetLine = Alg GetLine_
data GetLine_ k  = GetLine_ (String -> k) deriving Functor
pattern GetLine :: Member GetLine eff => (String -> k) -> Effs eff m k
pattern GetLine k <- (prj -> Just (Alg (GetLine_ k)))
  where GetLine k = inj (Alg (GetLine_ k))
getLine :: Members '[GetLine] sig => Prog sig String
getLine = call (Alg (GetLine_ id))

type PutStrLn = Alg PutStrLn_
data PutStrLn_ k = PutStrLn_ String k     deriving Functor
pattern PutStrLn :: Member PutStrLn eff => String -> k -> Effs eff m k
pattern PutStrLn str k <- (prj -> Just (Alg (PutStrLn_ str k)))
  where PutStrLn str k = inj (Alg (PutStrLn_ str k))
putStrLn :: Members '[PutStrLn] sig => String -> Prog sig ()
putStrLn str = call (Alg (PutStrLn_ str ()))
```
Much of this is standard boilerplate code.


Now to execute the program all that remains is `handleIO`:
```haskell
exampleIO :: IO ()
exampleIO = handleIO teletypeIO echo
```
This will execute the `echo` program where input provided on the
terminal by the user is immediately echoed back out to the terminal.

```console
ghci> exampleIO
Hello world!
Hello world!
```


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
The idea is to execute this program using a specialised handler
that counts the number of ticks:
```haskell
exampleEchoTick :: IO (Int, ())
exampleEchoTick = handleIO (ticker |> teletypeIO) echoTick
```
When this is executed, it counts the number of lines received:
```console
ghci> exampleEchoTick
Hello
Hello
world!
world!

(3,())
```
This demonstrates how unhandled effects that are recognized by I/O can be
forwarded and dealt with after the execution of the handler.

We can also emulate the behaviour of `echo` by ignoring all the ticks by using
the `unticker` handler:
```haskell
exampleEchoNoTick :: IO ()
exampleEchoNoTick = handleIO (unticker |> teletypeIO) echoTick
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
The `a ! sig` datatype thus describes a *family* of programs which contains
all the operations given in `sig`. No order of the members is
implied (because the constraints are not ordered), and nor is the list necessarily exhaustive (because `sig` could contain other operations).

The `ticker` and `unticker` handlers have the following types:
```haskell ignore
ticker   :: Handler '[Tick] '[] '[StateT Int] a (Int, a)
unticker :: Handler '[Tick] '[] '[]           a a
```
Here is what the different parameters mean for the `ticker` handler:
```haskell ignore
ticker   :: Handler '[Tick]         -- input effects
                    '[]             -- output effects
                    '[StateT Int]   -- transformers
                    a               -- input type
                    (Int, a)        -- output type
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
* **Wrappers**: The wrappers are used to wrap the final computation when the handler
  is applied.
  When `ticker` is used to handle a program of type `Prog effs a`,
  the output will be the wrapper `((,) s)` applied to the value of the program
  `a`, which is simply `(s, a)`.
  The wrapper list is applied to a value of type `a` using `Apply`,
  so that the wrapper, so that
  `Apply [f3, f2, f1] a = f3 (f2 (f1 a))`.

A handler is applied to a program using a `handle` function. In `exampleEchoTick`,
the `handleIO` function is used because `GetLine` and `PutStrLn` are operations
that relate to `IO`.
```haskell ignore
handleIO
  :: ( Injects xeffs IOEffects , Injects oeffs IOEffects ...)
  => Proxy xeffs -> Handler effs oeffs ts fs
  -> Prog (effs `Union` xeffs) a -> IO (Apply fs a)
```
The @xeffs@ type argument is the operations on the `IO`-monad that the program
needs to use, which must be explicitly given using a proxy argument (it is never
inferable without the proxy argument because `Union` is a non-injective type
family).
The result is `IO (Apply fs a)`, where `fs` is the wrapper functors of the handler.
This becomes important for handlers like `unticker`, so that the result
of `handleIO unticker p` when `p :: Prog [Tick] a` is a value of type `IO a`.
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
                      '[(,) s]          -- wrapper
```

Executing the `incr` program with this handler can be achieved as follows:
```console
ghci> handle (state (41 :: Int)) incr
(42,())
```
Since the program has type `() ! [Put Int, Get Int]`, with a pure value of `()`,
the result of applying the handler is `((,) Int)` applied to `()`,
thus giving back a value of type `(Int, ())`.

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
("Hello!",6)
```
Notice that the `state` handler returns the final state as well as the final
return value of the program.

A variation of the `state` handler is `state_`,
which does not return the final state:
```haskell ignore
state_ :: s -> Handler [Put s, Get s] '[] '[StateT s] '[]
```
Here the final wrapper is `'[]`, and so applying this to a program
of type `Prog sig a` will simply return a value of type `a`.
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

A pattern synonym `Tick` is defined that projects `Alg Tick_` into
an `Effs` type, which is the type used to assemble multiple effects into one:
```haskell
pattern Tick :: Member Tick eff => k -> Effs eff m k
pattern Tick p <- (prj -> Just (Alg (Tick_ p)))
  where Tick p = inj (Alg (Tick_ p))
```

### Smart Constructor

A smart constructor `tick` is defined that allows programs to be written
that uses this operation:
```haskell
tick :: () ! '[Tick]
tick = call (Alg (Tick_ ()))
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
unticker = interpret (\(Tick x) -> return x)
```
The `interpret` function builds a handler from a function
that describes how to rephrase an operation. Here, `Tick x`
is translated into `return x`.

The `ticker` handler is a bit more complex: it works by interpreting
the `tick` operation into `get` and `put` operations, which interact
with an `Int` to keep track of how many ticks have been produced.
Notice that the `gen` function generates these operations from the given `tick`:
```haskell
tickState :: Handler '[Tick] '[Put Int, Get Int] '[] a a
tickState = interpret rephrase where
  rephrase :: Effs '[Tick] m x -> Prog [Put Int, Get Int] x
  rephrase (Tick x) = do n <- get
                         put @Int (n + 1)
                         return x
```
The `ticker` is produced by combining `tickState` with the `state` handler using
the _pipe_ combinator, written `h1 ||> h2` to pipe the handler `h1` into the
handler `h2`.

```haskell
ticker :: Handler '[Tick] '[] '[StateT Int] a (Int, a)
ticker = tickState ||> state (0 :: Int)
```
Given `h1 :: Handler eff1 oeff1 t1 f1` and `h2 :: Handler eff2 oeff2 t2 f2`, the
result of `h1 ||> h2` is a handler that recognises all of `eff1`, the input
effects of `h1`, and passes any effects `oeff1` produced by `h1` to be processed
by `h2`. Here are the types involved:
```haskell ignore
(||>) :: ...
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
getLineIncr = interpret $ \(GetLine k) ->
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
                            (Int, a)
getLineIncrState = getLineIncr ||> (state (0 :: Int))
```
This can then be executed using `handleIO`, which will deal with
the residual `GetLine` effect:
```console
ghci> handleIO getLineIncrState echo
Hello
Hello
world!
world!

(3,())
```
The `getLineIncrState` has intercepted the `getLine` operation and
incremented the state counter on each execution.


Redirecting Input
-----------------

Another issue is trying to test the behaviour of a program that demands input
from the terminal. For instance, suppose the task is to get a line and return
its length. This is achieved by the `getLineLength` program:
```haskell
getLineLength :: Int ! '[GetLine]
getLineLength = do xs <- getLine
                   return (length xs)
```
As before, this can be evaluated using `evalIO`:
```console
ghci> evalIO getLineLength
Hello
5
```
Better would be to provide those lines purely from a pure
list of strings. Here is how `getLine` can be interpreted in terms of the
operations `get` and `put` from a state containing a list of strings:
```haskell
getLineState
  :: Handler '[GetLine] '[Get [String], Put [String]] '[] a a
getLineState = interpret $ \(GetLine k) ->
  do xss <- get
     case xss of
       []        -> return (k "")
       (xs:xss') -> do put xss'
                       return (k xs)
```

The signature of `getLineState` says that it is a handler that recognizes
`GetLine` operations and interprets them in terms of some output effects in
`oeff`, which consist of `Get [String]` and `Put [String]`. Interpreting
effects in terms of other, more primitive, effects allows other handlers to
deal with those more primitive effects.

The `getLineState` handler will process the `GetLine` effect in the
echo program, and in so doing will output `Get [String]` and `Put [String]`
effects. These can be handled by a state handler. The output of the
`getLineState` handler can be piped into the `state` handler to produce
a new handler. Here are two variations:
```haskell
getLinePure :: [String] -> Handler '[GetLine] '[] '[StateT [String]] a ([String], a)
getLinePure str = getLineState ||> (state str)

getLinePure_ :: [String] -> Handler '[GetLine] '[] '[StateT [String]] a a
getLinePure_ str = getLineState ||> (state_ str)
```
Now we have a means of executing a program that contains only a `GetLine` effect,
and extracting the resulting string:
```haskell ignore
handle (getLinePure ["hello", "world!"]) :: Prog '[GetLine] a -> ([String], a)
```
Executing this will get the first line in the list of strings and return its length,
and the same program can be executed either processed with IO.
```console
ghci> handle (getLinePure ["Hello", "world!"]) getLineLength
(["world!"],5)
```
This consumes `"Hello"` as the result of `getLine`, and so the state retains
`"world!"`.


Redirecting Output
------------------

Although the input of `echo` can be redirected using `getLinePure`, using this
alone would not suffice, because the type of echo indicates that the program
also uses the `PutStrLn` effect, which must also be handled.
Trying to do so returns a type error:
```console
ghci> :t handle (getLinePure ["hello", "world"]) echo

<interactive>:8:42: error: [GHC-39999]
    • No instance for ‘Member' PutStrLn '[] (ElemIndex PutStrLn '[])’
        arising from a use of ‘echo’
    • In the second argument of ‘handle’, namely ‘echo’
      In the expression: handle (getLinePure ["Hello", "world!"]) echo
      In an equation for ‘it’:
          it = handle (getLinePure ["Hello", "world!"]) echo
```
This is saying that GHC has no way to handle the `PutStrLn` effect using this
handler.

One fix is to handle the program with `handleIO` to output to IO, while
redirecting the input to come from a pure list:
```console
ghci> handleIO (getLinePure_ ["Hello", "world!"]) echo
Hello
world
```
However, there is another solution: the `putStrLn` operation can also be
redirected to do something pure.

Outputting pure values is managed by the `writer` handler, in combination
with the `tell` operation:
```haskell ignore
writer :: Monoid w => Handler '[Tell w] '[] '[WriterT w] '[(,) w]
tell   :: Monoid w => w -> () ! '[Tell w]
```
The signatures tell us that `tell` introduces the `Tell` effect, and
`writer` handles this effect.

The following simple example returns a list of strings, since a list of
elements is a monoid:
```console
ghci> handle writer (tell ["Hello", "World!"]) :: ([String], ())
(["Hello","World!"],())
```
Using this, values can be written as the output of a program.

Now the task is to interpret all `putStrLn` operations in terms of the
`tell` operation:
```haskell
putStrLnTell :: Handler '[PutStrLn] '[Tell [String]] '[] a a
putStrLnTell = interpret $ \(PutStrLn str k) ->
  do tell [str]
     return k
```
This can in turn be piped into the `writer` handler to make
a pure version of `putStrLn`:
```haskell
putStrLnPure :: Handler '[PutStrLn] '[] '[WriterT [String]] a ([String], a)
putStrLnPure = putStrLnTell ||> writer
```
Now, a pure handler for both `putStrLn` and `getLine` can
be defined as the /fusion/ of `putStrLnPure` and `getLinePure`.
```haskell
teletype :: [String]
         -> Handler '[GetLine, PutStrLn]
                    '[]
                    '[(StateT [String]), (WriterT [String])]
                    a
                    ([String], a)
teletype str = getLinePure_ str |> putStrLnPure
```
The `fuse` combinator `|>` takes two handlers and creates one that accepts the union
of their signatures. The handlers are run in sequence so that the output of the
first handler is fed into the input of the second. Any remaining output
operations are combined and become the output of the fusion.

Now the `echo` program can be executed in an entirely pure context:
```console
ghci> handle (teletype ["Hello", "world!"]) echo
(["Hello","world!"],())
```
<!--
```haskell
prop_teletypePure :: Property
prop_teletypePure = property $ do
  xss <- forAll $ list (linear 0 1000) (string (linear 0 100) ascii)
  let xss' = takeWhile (/= "") xss
  handle (teletype xss) echo === (xss', ())
```
-->
The return value of `()` comes from the result of `echo` itself, and the list
of strings is the accumulated result of the `tell` commands.

One challenge is to count the number of times `getLine` is executed
while also processing it purely. No problem, the `getLineIncrState` can be used
to interpret `getLine` before passing the resulting `getLine` to `teletype`:
```haskell
teletypeTick
  :: [String]
  -> Handler '[GetLine, PutStrLn] '[]
             '[StateT Int, StateT [String], WriterT [String]]
             a
             ([String], (Int, a))
teletypeTick str = getLineIncrState |> teletype str
```
This can be executed using `handle`, passing in the
list of inputs to be fed to `getLine`:
```console
ghci> handle (teletypeTick ["Hello", "world!"]) echo
(["Hello","world!"],(3,()))
```
<!--
```haskell
prop_teletypeTick :: Property
prop_teletypeTick = property $ do
  xss <- forAll $ list (linear 0 1000) (string (linear 0 100) ascii)
  let xss' = takeWhile (/= "") xss
  handle (teletypeTick xss) echo === (xss', (length xss' + 1, ()))
```
-->


Scoped Operations
-----------------

Intercepting operations and changing their behaviour is typical when working
with handlers. An example of this is to apply a transformation to all the
`tell` operations, so that everything is in uppercase. To this, another
interpreting handler called `retell` can be defined, which takes in a function used
to modify output:
```haskell
retell :: forall w w' a . (Monoid w, Monoid w')
       => (w -> w')
       -> Handler '[Tell w] '[Tell w'] '[] a a
retell f = interpret $ \(Tell w k) ->
  do tell (f w)
     return k
```
Simply put, every `tell w` is intercepted, and retold as `tell (f w)`. Thus,
a simple message can be made louder at the flick of a switch:
```console
ghci> handle (retell (map toUpper) |> writer @String) (tell "get bigger!")
("GET BIGGER!",())
```
The `retell` handler modifies the `tell` operations, and they are then
turned into the final result with `writer`.

Suppose the task is to censor language that can only be described as [nasty and
frightful](https://en.wikipedia.org/wiki/Roald_Dahl_revision_controversy).
A program designed around this task may need a more nuanced approach to
retelling its input, with censoring only acceptable in certain regions of code.

A scoped operation takes a program as one of its parameters, and interacts with
operations in that program. For example, the `Censor` effect is
introduced by the accompanying `censor` operation, and is handled
using the `censors` handler:
```
censor  :: Member (Censor w) sig => (w -> w) -> Prog sig a -> Prog sig a
censors :: Monoid w => (w -> w) -> Handler '[Tell w, Censor w] '[Tell w] '[]
```
The result of the `censors cipher` handler is to first apply the `cipher`
to any `tell`, just like `retell` above. However, when a `censor cipher' p` operation
is encountered, the result is to additionally apply `cipher'` to any `tell`
in `p`. In this way, nested `censors` will have their ciphers accumulated.

For instance, here is a program that uses `censor` at
particular points of the program, to help
[Mr Hoppy](https://en.wikipedia.org/wiki/Esio_Trot) to tell a tortoise
called Alfie to get bigger:
```haskell
hoppy :: () ! [Tell [String], Censor [String]]
hoppy = do tell ["Hello Alfie!"]
           censor @[String] backwards $
             do tell ["tortoise"]
                censor @[String] shout $
                  do tell ["get bigger!"]
           tell ["Goodbye!"]

backwards, shout :: [String] -> [String]
backwards = map reverse
shout     = map (map toUpper)
```
To evaluate this program, the `censors` handler is created with an initial
cipher which is `id` so that the messages not under a `censor` are not affected:
```console
ghci> handle (censors @[String] id |> writer) hoppy :: ([String], ())
(["Hello Alfie!","esiotrot","!REGGIB TEG","Goodbye!"],())
```
Notice how `"get bigger!"` is both reversed and made uppercase because
the ciphers have been accumulated.
<!--
```haskell
prop_esiotrot :: Property
prop_esiotrot = property $ do
  (handle (censors @[String] id |> writer) hoppy :: ([String], ())) === (["Hello Alfie!","esiotrot","!REGGIB TEG","Goodbye!"],())
```
-->

Hiding Operations
-----------------

Since `censor` is an operation, it can be given different semantics by a
different handler. For instance, here is type of the `uncensor` handler:
```haskell ignore
uncensors :: forall w . Monoid w => Handler '[Censor w] '[] '[] '[]
```
This handler removes all censorship from the program. The type promises that no other
effects are generated, and that the result is pure.
```console
ghci> handle (uncensors @[String] |> writer @[String]) hoppy
(["Hello world!","tortoise","get bigger!","Goodbye!"],())
```
One way to define `uncensors` is to process all `censor` operations with
`censors id`, followed by the `writer_` handler (which discards its output) to
remove any generated `tell` operations. To prevent this handler from touching
any `tell` operations that were in the program before censor, the `hide`
combinator removes them from being seen:
```haskell
uncensors :: forall w a . Monoid w => Handler '[Censor w] '[] '[(ReaderT (w -> w)), (WriterT w)] a a
uncensors = hide (Proxy @'[Tell w]) (censors @w id |> writer_ @w)
```
The key combinator here is `hide`:
```haskell ignore
hide :: forall sigs effs oeffs f . (Injects (effs :\\ sigs) effs, Injects oeffs oeffs)
     => Proxy sigs
     -> Handler effs            oeffs f
     -> Handler (effs :\\ sigs) oeffs f
```
This takes in a handler, returns it where any effects provided by the type parameter `sigs`
are hidden. While this works, the version in `Control.Effect.Writer` processes
any `censor` by ignoring its argument, and does not accumulate any output, and
is therefore more efficient.
<!--
```haskell
prop_uncensors :: Property
prop_uncensors = property $ do
  (handle (uncensors @[String] |> writer) hoppy :: ([String], ())) === (["Hello Alfie!","tortoise","get bigger!","Goodbye!"],())
```
-->

Censoring `PutStrLn`
--------------------

The `censors` handler is designed to work with the interaction between `censor`
and `tell`. Suppose the task is now to censor the `echo` program.
It is easy enough to see how a variation of `retell` could be written,
by interpreting `PutStrLn` operations:
```haskell
rePutStrLn :: (String -> String) -> Handler '[PutStrLn] '[PutStrLn] '[] a a
rePutStrLn f = interpret $ \(PutStrLn str k) ->
  do putStrLn (f str)
     return k
```

```console
ghci> handle (rePutStrLn (map toUpper) |> teletype ["tortoise"]) echo
(["TORTOISE"],())
```
<!--
```haskell
prop_rePutStrLn :: Property
prop_rePutStrLn = property $ do
  xss <- forAll $ list (linear 0 1000) (string (linear 0 100) ascii)
  let xss' = takeWhile (/= "") xss
  handle (rePutStrLn (map toUpper) |> teletype xss) echo
    === (map (map toUpper) xss',())
```
-->

A more localized approach is to use the `censor` operation so
that a censored echo can be used:
```haskell
shoutEcho :: () ! [Censor [String], GetLine, PutStrLn]
shoutEcho = censor shout echo
```
The censoring in this program cannot be handled with the `censors` handler by
itself, since it simply has the wrong type: it works with `Tell` rather than
`PutStrLn` operations.

Rather than writing a custom handler from scratch, one attempt is to
first transform any `putStrLn` operation into a `tell` using
`putStrLnTell`, then apply the `censors` handler, and finally
turn any `tell` back into `putStrLn` with using `tellPutStrLn`:
```haskell
tellPutStrLn :: Handler '[Tell [String]] '[PutStrLn] '[] a a
tellPutStrLn = interpret $ \(Tell strs k) ->
  do putStrLn (unwords strs)
     return k
```
This chain of handlers might be called `censorsPutStrLn`:
```haskell
censorsPutStrLn :: ([String] -> [String])
                -> Handler [PutStrLn, Tell [String], Censor [String]] '[PutStrLn] '[ReaderT ([String] -> [String])] a a
censorsPutStrLn cipher = putStrLnTell |> censors cipher |> tellPutStrLn
```
The ensuing chain of handlers seems to do the job:
```console
ghci> handle (censorsPutStrLn id |> teletype ["Hello world!"])
             shoutEcho
(["HELLO WORLD!"],())
```
However, things can get muddled if the program contains a mixture
of `tell` and `putStrLn` operations.

For example, here is a program that uses `tell` to log the fact
that the shouty echo program is being entered before doing so:
```haskell
logShoutEcho :: () ! [PutStrLn, GetLine, Censor [String], Tell [String]]
logShoutEcho = do tell ["Entering shouty echo"]
                  shoutEcho
```
It is tempting to execute the program with the following:
```console
ghci> handle (censorsPutStrLn id |> teletype ["Hello world!"]) logShoutEcho
(["Entering shouty echo","HELLO WORLD!"],())
```
It seems to work, but the problem is that the logged messages are treated
in exactly the same way as the pure `putStrLn` values: everything is
accumulated into the same list of strings. The problem is exasperated
when `handleIO` is used: the logged messages are immediately output to the
terminal:
```console
ghci> handleIO (censorsPutStrLn id) logShoutEcho
Entering shouty echo:
Hang on, that's a log message!
HANG ON, THAT'S A LOG MESSAGE!
```
The reason is that the `censorsPutStrLn` handler is interpreting all the `tell`
operations into `putStrLn`: it cannot discriminate between those that came from
a `putStrLn` originally, and those that are part of the program.

The solution is simple: the `tell` operations to do with logging
should be handled _before_ the teletype effects are handled:
```console
ghci> handle (writer @[String] |> censorsPutStrLn id |> teletype ["Hello world!"]) logShoutEcho
(["HELLO WORLD!"],(["Entering shouty echo"],()))
```
This pure version separates the two kinds of logged messages; those
that come from `tell` are processed first (and so in the inner tuple),
and then the messages from `putStrLn` are on the outside.

This even works with `handleIO`:
```
ghci> handleIO (writer @[String] |> censorsPutStrLn id) logShoutEcho
Ah, that's better
AH, THAT'S BETTER

(["Entering shouty echo"],())
```
The `putStrLn` messages are correctly censored, and the log messages
are purely produced.


Timestamps
----------

Timestamps are often used in conjunction with logging so that the time a message
is logged can be recorded. The traditional way of doing this might be to make
a bespoke `logger` that ensures that there is a timestamp integrated into each
occurence of the log:
```haskell
logger :: String -> () ! [Tell [(Integer, String)], Alg IO]
logger str = do time <- io getCPUTime
                tell [(time, str)]
```
However, this is a case where a reinterpretation might be better where all
instances of `tell` are augmented with the appropriate timestamp.
```haskell
telltime :: forall w a . Monoid w => Handler '[Tell w] '[Tell [(Integer, w)], Alg IO ] '[] a a
telltime = interpret $ \(Tell (w :: w) k) ->
  do time <- io getCPUTime
     tell [(time, w)]
     return k
```
Now a timestamp is added to the start of messages emitted by `tell`:
```console
ghci> handleIO (telltime @[String] |> censors backwards |> writer @[(Integer, [String])] |> censorsPutStrLn id |> teletype ["Hello"]) logShoutEcho
(["Hello"],([(8073080000000,["Entering shouty echo"])],()))
```

A different interface is to use a scoped operation that marks
part of the program as of interest for profiling.
```haskell
type Profile = Scp Profile'
data Profile' k where
  Profile :: String -> k -> Profile' k
  deriving Functor

profile :: Member Profile sig => String -> Prog sig a -> Prog sig a
profile name p = call (Scp (Profile name p))
```

For example, to profile some code `p`, we need to mark it as a code of interest
by writing `profile name p`, where `name` is some identifier that we wish to see
in the log. Then, we must decide which instrument we want to use to measure
what happens to `p`. An instrument measures some quantity of interest, such as
time memory, energy, or bandwidth.

For example, the `timer` handler can be invoked to measure time. This injects
`getCPUTime` operations to measure the time `t` before and `t'` after `p`
is executed. Then `ask` emits a pair consisting of `(name, t' - t)`,
thus showing how much time was spent in `p`.

```haskell
timer :: Handler '[Profile] '[Tell [(String, Integer)], Alg IO] '[] a a
timer = interpretM $ \oalg (Eff (Scp (Profile name p))) ->
  do t  <- eval oalg (io getCPUTime)
     k  <- p
     eval oalg $ do
        t' <- io getCPUTime
        tell [(name, t' - t)]
     return k
```
How exactly `getCPUTime` is measured, and what is done with the `ask` is left
to another handler. This easily allows, for instance, different ways of measuring time
to be implemented, or for logs to be enabled and disabled.

More generally, there may be other instruments that could be used, and indeed
the `timer` handler can alternatively be defined by using `profiler`:
```haskell
timer' :: Handler '[Profile] '[Tell [(String, Integer)], Alg IO] '[] a a
timer' = profiler (flip (-)) (io getCPUTime)
```
A new `profiler f instrument p` will inject the `instrument` before and after
`p` and collect two measurements: one before `p` and another after `p` is
executed. These are then combined by the given function `f` and emitted using
`ask`.
```haskell
profiler :: (HFunctor (Effs oeffs), Injects oeffs (Tell [(String, b)] ': oeffs))
  => (a -> a -> b) -> Prog oeffs a -> Handler '[Profile] (Tell [(String, b)] ': oeffs) '[] c c
profiler f instrument = interpretM $ \oalg (Eff (Scp (Profile name p))) ->
  do t  <- eval oalg (weakenProg instrument)
     k  <- p
     eval oalg $ do
        t' <- weakenProg instrument
        tell [(name, f t t')]
     return k
```

For our teletype example, we can instrument all of the `getLine` operations
with a profiler as follows:
```haskell
getLineProfile :: Handler '[GetLine] '[Profile, GetLine] '[] a a
getLineProfile = interpret $ \(GetLine k) ->
  profile "getLine" (getLine >>= return . k)
```







Members
-------

There are three scenarios to consider when trying to engineer a fit between a
program (shaft) of type `Prog effs a` and a handler (hole) of type
`Handler ieffs oeffs ts fs`, depending on how their interfaces correspond:

1. *Transition* (`effs = ieffs`): The program and the handler have the same
   signatures. In the effective library, every effect is
   handled sequentially, from left to right in the order dictated by the
   handler. Programs are defined using `Members` so that reorderings
   are dealt with by the constraints solver.
2. *Clearance* (`effs < ieffs`): The handler can deal with more operations than
   required by the program. In these situations the handler or the program can
   be weakened. In the effective library, the program is weakened by
   the constraints solver due to the `Members` constraint.
3. *Interference* (`effs > ieffs`): The handler cannot deal with all the
   operations exposed by the program. Any residual effects will have to be
   handled later. In the effective library, a handler's interface can be
   extended using `fuse` and `pipe` with another handler, and residual
   effects can be dealt with using an algebra as a parameter to `handleM`.

When there is transition between program and handler, there may be a difference
in the orders of the effects presented in the signatures. The philosophy of
effect handlers is that a program can be handled in different ways to create
different semantics. Although it is reasonable for a program to insist on a
particular order in which certain effects should be handled, the `effective`
library leaves this choice entirely to the handler.




Language Extensions
--------------------

The `effective` library requires the `DataKinds` extension since
this is used to keep track of effect signatures.

```haskell top
{-# LANGUAGE DataKinds       #-}  -- Used for the list of effects
{-# LANGUAGE GADTs           #-}  -- Used for syntax
{-# LANGUAGE PatternSynonyms #-}  -- Used for syntax
{-# LANGUAGE ViewPatterns    #-}  -- Used for syntax
{-# LANGUAGE LambdaCase      #-}  -- Used for syntax
{-# LANGUAGE TemplateHaskell #-}  -- Used for syntax
```
<!--
The following pragma is only needed for the testing framework.
```haskell top
{-# LANGUAGE OverloadedStrings #-}
```
-->

Imports
-------

This file has a number of imports:

```haskell top
import Control.Effect hiding (Lookup)
import Control.Effect.Family.Algebraic
import Control.Effect.Family.Scoped
import Control.Effect.IO
import Control.Effect.State
import Control.Effect.Maybe
import Control.Effect.Writer hiding (uncensors)

import Control.Effect.Reader (ReaderT, asker, Ask, ask)

import Data.List (insert)
import Data.List.Kind hiding (Lookup)
import Data.Char (toUpper)
import Data.HFunctor

import System.CPUTime (getCPUTime)

import Prelude hiding (putStrLn, getLine, lookup)
import qualified Prelude
import Control.Effect.Internal.TH
```

<!--
We will hide the following from the README, because it is
only for testing the documentaton itself.
```haskell top
import Hedgehog (Property, Group(..), discover, property, forAll, checkParallel, (===))
import Hedgehog.Main (defaultMain)
import Hedgehog.Gen hiding (map, maybe)
import Hedgehog.Range

props :: Group
-- props = $$(discover)
props = Group "README properties"
  [ ("teletypePure", prop_teletypePure)
  , ("teletypeTick", prop_teletypeTick)
  , ("esiotrot",     prop_esiotrot)
  , ("uncensors",    prop_uncensors)
  , ("rePutStrLn",   prop_rePutStrLn)
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

[^Gordon1992]: [Functional Programming and Input/Output. A. Gordon. PhD Thesis, King's College London. 1992](https://www.microsoft.com/en-us/research/uploads/prod/2016/11/fpio.pdf)

[^Imports]: The language extensions and imports required are at the bottom of this file.

