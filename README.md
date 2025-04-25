Effective
==========

The `effective` library is an effect handlers library for Haskell that is
designed to allow users to define and interpret their own languages and
effects. This library incorporates support for:

* Algebraic, scoped, and other higher-order effects.
* Modular effect handlers.


README
------

This README is a literate Haskell file and therefore can be executed:
```console
git clone effective
cd effective
cabal repl readme
```
This should bring you into `ghci` where you can follow the examples.[^Imports]


Working with IO
----------------

The `Teletype` example is a rite of passage for monadic IO [^Gordon1992] where
the challenge is to show how IO of reading from and writing to the terminal can
be achieved. A program that interacts with the terminal is `echo`. This is a
simple program that will continue to echo the input obtained by `getLine` is
output to the terminal using `putStrLn` until a blank line is received by
`getLine`:
```haskell
echo :: Progs [GetLine, PutStrLn] ()
echo = do str <- getLine
          case str of
            [] -> return ()
            _  -> do putStrLn str
                     echo
```
The type signature says that this is a program that requires
both `GetLine` and `PutStrLn` operations.

The most obvious interpretation of `getLine` and `putLine` is to invoke their
corresponding values from the prelude. Indeed, when all the operations of a
program are standard Prelude IO operations, it is enough to simply evaluate the
program using `evalIO`:
```haskell ignore
exampleIO :: IO ()
exampleIO = evalIO echo
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
echoTick :: Progs '[GetLine, PutStrLn, Tick] ()
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
exampleEchoTick = handleIO @'[GetLine, PutStrLn] ticker echoTick
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
exampleEchoNoTick = handleIO @'[GetLine, PutStrLn] unticker echoTick
```
Note that this is different to discarding the tick count by applying `fst`
to the result of a program that counts ticks: the count is not even generated
in the first place.


Programs and Handlers
---------------------

The type of the `echoTick` program is `Progs '[GetLine, PutStrLn, Tick] ()`, which is in
fact a synonym roughly equivalent to:
```haskell ignore
echoTick :: (Member GetLine sig, Member PutStrLn sig, Member Tick sig)
         => Prog sig ()
```
The `Progs` datatype thus describes a *family* of programs which contains
all the operations in the given signature. No order of the members is
implied (because the constraints are not ordered), and nor is the list necessarily exhaustive (because `sig` could contain other operations).

The `ticker` and `unticker` handlers have the following types:
```haskell ignore
ticker   :: Handler '[Tick] '[] '[StateT Int] [(,) Int]
unticker :: Handler '[Tick] '[] '[] '[]
```
Here is what the different parameters mean for the `ticker` handler:
```haskell ignore
ticker   :: Handler '[Tick]         -- input effects
                    '[]             -- output effects
                    '[StateT Int]   -- transformer
                    '[(,) Int]      -- wrapper
```

The signature of the handler tells us how it behaves:
* **Input effects**: The input effects will be processed and removed by this handler.
  In `ticker` the input effect is `Tick`.
* **Output effects**: The output effects will be produced by this handler.
  In `ticker` the output effects are empty.
* **Transformer**: The transformer is used to provide semantics to the input effects.
  In `ticker` the transformer is `StateT Int`.
* **Wrapper**: The wrapper is used wrap the final computation when the handler
  is handled.
  When `ticker` is used to handle a program of type `Prog effs a`,
  the output will be the wrapper `((,) s)` applied to the value of the program
  `a`, which is simply `(s, a)`.

A handler is applied to a program using a `handle` function. In `exampleEchoTick`,
the `handleIO` function is used because `GetLine` and `PutStrLn` are operations
that relate to `IO`.
```haskell ignore
handleIO :: ( forall m . Monad m => Monad (t m), Functor f , ... )
         => Handler effs oeffs t f
         -> Prog (effs `Union` xeffs) a -> IO (Apply f a)
```
The result is `IO (Apply f)`, where `f` is the functor given by the wrapper of the handler, and `Apply f` removes any stray `Identity` and `Compose` functors.
This becomes important for handlers like `unticker`, so that the result
of `handleIO unticker p` when `p :: Prog [Tick] a` is a value of type `IO a` .
So far, we have been working with examples of _impure_ effects that ultimately
rely on `IO`. Another important class of effects is the class of _pure_ effects,
which we will look at next.


Working with Pure Handlers
--------------------------

A pure handler can be applied when all the effects in a program are
processed, and when none are produced:
```haskell ignore
handle :: ( Monad (ts Identity) , Functor f )
       => Handler effs '[] ts f
       -> Prog effs a -> Apply f a
```

For example, a pure state effect is provided in `Effect.Control.State`, which
supports `get` and `put` as operations that are indicated by `Get s` and `Put s`
in a signature.

Here is a program that increments the number in a state
and returns it:
```haskell
incr :: Progs [Put Int, Get Int] ()
incr = do x <- get
          put @Int (x + 1)
```
In order to keep the program modular, the effects in `effs` are given by a
constraint on the input type, saying that `Put Int` and `Get Int` are its
members.

This program can be executed by using a `state s` handler, where the
state is initialised to `s`:
```haskell ignore
state :: s -> Handler '[Put s, Get s]  -- input effects
                      '[]              -- output effects
                      '[StateT s]       -- transformer
                      '[(,) s]          -- wrapper
```

Executing the `incr` program with this handler can be achieved as follows:
```console
ghci> handle (state (41 :: Int)) incr
(42,())
```
Since the program has type `Prog effs ()`, with a pure value of `()`,
the result of applying the handler is `((,) Int)` applied to `()`,
thus giving back a value of type `(Int, ())`.

The type of the `state` handler promises to handle both `Put s` and `Get s`
operations, and so it is able to work with programs that use both, or
either one of these. Here is a program that only uses `Get String`:
```haskell
getStringLength :: Progs '[Get String] Int
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
state_ :: s -> Handler [Put s, Get s] '[] '[]
```
Here the final output wrapper is `Identity`, and so applying this to a program
of type `Prog sig a` will simply return a value of type `a`, since `Apply Identity a = a`.
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


Creating  Operations
--------------------

One of the key features of an effect system is to allow an effect engineer
to create new effects and interpret them in different ways. Although
`getLine` and `putStrLn` are special, in that they are processed by `evalIO`
and provided by the `effective` library, the `tick` operation is a
custom operation with a semantics given as we desire.

The `tick` operation is defined by providing a datastructure to hold the syntax
as data:
```haskell
type Tick = Alg Tick'
data Tick' k = Tick k
  deriving Functor

tick :: Member Tick sig => Prog sig ()
tick = call (Alg (Tick (return ())))
```
This uses a `Member` constraint to describe how `tick` can be used
in any program where `Tick` is in its signature. The `Alg` constructor
indicates that `Tick` is an algebraic operation.

The `unticker` and `ticker` handlers are examples of interpreters that
will interpret `Tick` in different ways. The simplest one is `unticker`,
which removes all instances of `Tick`:
```haskell
unticker :: Handler '[Tick] '[] '[] '[]
unticker = interpret gen where
  gen :: Effs '[Tick] m x -> Prog '[] x
  gen (Eff (Alg (Tick x))) = return x
```
The `gen` function describes how to generate a program from the operations
it recognises. In this instance, the program is always empty, and
simply returns `k`.

The `ticker` handler is a bit more complex: it works by interpreting
the `tick` operation into `get` and `put` operations, which interact
with an `Int` to keep track of how many ticks have been produced.
Notice that the `gen` function generates these operations from the given `tick`:
```haskell
tickState :: Handler '[Tick] '[Put Int, Get Int] '[] '[]
tickState = interpret gen where
  gen :: Effs '[Tick] m x -> Prog [Put Int, Get Int] x
  gen (Eff (Alg (Tick x))) = do n <- get
                                put @Int (n + 1)
                                return x
```
The `ticker` is produced by combining `tickState` with the `state` handler using
the _pipe_ combinator, written `h1 ||> h2` to pipe the handler `h1` into the
handler `h2`.

```haskell
ticker :: Handler '[Tick] '[] '[StateT Int] '[(,) Int]
ticker = tickState ||> state (0 :: Int)
```
Given `h1 :: Handler eff1 oeff1 t1 f1` and `h2 :: Handler eff2 oeff2 t2 f2`, the
result of `h1 ||> h2` is a handler that recognises all of `eff1`, the input
effects of `h1`, and passes any effects `oeff1` produced by `h1` to be processed
by `h2`. Here are the types involved:
```haskell ignore
(||>) :: ...
      => Handler effs1 oeffs1 t1 f1
      -> Handler effs2 oeffs2 t2 f2
      -> Handler effs  oeffs  t  f
```
The constraints on `||>` include:
```haskell ignore
  effs  ~ effs1
  oeffs ~ (oeffs1 :\\ effs2) `Union` oeffs2
  t     ~ HRAssoc (t1 `ComposeT` t2)
  f     ~ RAssoc (f2 `Compose` f1)
```
More specifically, the output effects `oeffs` include all the output
effects of `h1` that are not processed by `h2`, together with any effects
produced by `h2`

The transformer and wrapper of the handler are essentially the compositions of
those given by `h1` and `h2`, but the results are normalised using `HRAssoc` and
`RAssoc` to remove any stray identities and to right associate the compositions.


Intercepting Operations
-----------------------

Forwarding effects to I/O works in many situations, but sometimes it is rather
crude: the power of effects is in their ability to intercept and interpret
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
             '[]                              -- transformer
             '[]                              -- wrapper
getLineIncr = interpret $
  \(Eff (Alg (GetLine k))) -> do xs <- getLine
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
                            '[(,) Int]
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
getLineLength :: Progs '[GetLine] Int
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
  :: Handler '[GetLine] '[Get [String], Put [String]] '[] '[]
getLineState = interpret $
  \(Eff (Alg (GetLine k))) -> do xss <- get
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
getLinePure :: [String] -> Handler '[GetLine] '[] '[StateT [String]] '[(,) [String]]
getLinePure str = getLineState ||> (state str)

getLinePure_ :: [String] -> Handler '[GetLine] '[] '[StateT [String]] '[]
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
tell   :: Monoid w => w -> Progs '[Tell w] ()
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
putStrLnTell :: Handler '[PutStrLn] '[Tell [String]] '[] '[]
putStrLnTell = interpret $
  \(Eff (Alg (PutStrLn str k))) -> do tell [str]
                                      return k
```
This can in turn be piped into the `writer` handler to make
a pure version of `putStrLn`:
```haskell
putStrLnPure :: Handler '[PutStrLn] '[] '[WriterT [String]] '[(,) [String]]
putStrLnPure = putStrLnTell ||> writer
```
Now, a pure handler for both `putStrLn` and `getLine` can
be defined as the fusion of `putStrLnPure` and `getLinePure`.
```haskell
teletype :: [String]
         -> Handler '[GetLine, PutStrLn]
                    '[]
                    '[(StateT [String]), (WriterT [String])]
                    '[(,) [String]]
teletype str = getLinePure_ str |> putStrLnPure
```
The `fuse` combinator takes two handlers and creates one that accepts the union
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
             '[(,) [String], ((,) Int) ]
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
retell :: forall w w' . (Monoid w, Monoid w') => (w -> w') -> Handler '[Tell w] '[Tell w'] '[] '[]
retell f = interpret $
  \(Eff (Alg (Tell w k))) -> do tell (f w)
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
censor  :: Member (Censor w) sig => (w -> w) -> Prog sig a -> Prog sig
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
hoppy :: Progs '[Tell [String], Censor [String]] ()
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
  handle (censors @[String] id |> writer) hoppy === (["Hello Alfie!","esiotrot","!REGGIB TEG","Goodbye!"],())
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
ghci> handle (uncensors @[String] |> writer @[String]) hello
(["Hello world!","tortoise","get bigger!","Goodbye!"],())
```
One way to define `uncensors` is to process all `censor` operations with
`censors id`, followed by the `writer_` handler (which discards its output) to
remove any generated `tell` operations. To prevent this handler from touching
any `tell` operations that were in the program before censor, the `hide`
combinator removes them from being seen:
```haskell
uncensors :: forall w . Monoid w => Handler '[Censor w] '[] '[(ReaderT (w -> w)), (WriterT w)] '[]
uncensors = hide @'[Tell w] (censors @w id |> writer_ @w)
```
The key combinator here is `hide`:
```haskell ignore
hide :: forall sigs effs oeffs f . (Injects (effs :\\ sigs) effs, Injects oeffs oeffs)
     => Handler effs            oeffs f
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
  handle (uncensors @[String] |> writer) hoppy === (["Hello Alfie!","tortoise","get bigger!","Goodbye!"],())
```
-->

Censoring `PutStrLn`
--------------------

The `censors` handler is designed to work with the interaction between `censor`
and `tell`. Suppose the task is now to censor the `echo` program.
It is easy enough to see how a variation of `retell` could be written,
by interpreting `PutStrLn` operations:
```haskell
rePutStrLn :: (String -> String) -> Handler '[PutStrLn] '[PutStrLn] '[] '[]
rePutStrLn f = interpret $
  \(Eff (Alg (PutStrLn str k))) -> do putStrLn (f str)
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
shoutEcho :: Progs [Censor [String], GetLine, PutStrLn] ()
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
tellPutStrLn :: Handler '[Tell [String]] '[PutStrLn] '[] '[]
tellPutStrLn = interpret $
  \(Eff (Alg (Tell strs k))) -> do putStrLn (unwords strs)
                                   return k
```
This chain of handlers might be called `censorsPutStrLn`:
```haskell
censorsPutStrLn :: ([String] -> [String])
                -> Handler [PutStrLn, Tell [String], Censor [String]] '[PutStrLn] '[ReaderT ([String] -> [String])] '[]
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
logShoutEcho :: Progs '[PutStrLn, GetLine, Censor [String], Tell [String]] ()
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
ghci> handle (writer @[String] |> censorsPutStrLn id |> teletype ["Hello wor
ld!"]) logShoutEcho
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
logger :: String -> Progs [Tell [(Integer, String)], GetCPUTime] ()
logger str = do time <- getCPUTime
                tell [(time, str)]
```
However, this is a case where a reinterpretation might be better where all
instances of `tell` are augmented with the appropriate timestamp.
```haskell
telltime :: forall w . Monoid w => Handler '[Tell w] '[Tell [(Integer, w)], GetCPUTime] '[] '[]
telltime = interpret $
  \(Eff (Alg (Tell (w :: w) k))) -> do time <- getCPUTime
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
profile name p = call (Scp (Profile name (fmap return p)))
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
timer :: Handler '[Profile] '[Tell [(String, Integer)], GetCPUTime] '[] '[]
timer = interpretM timerAlg

timerAlg :: forall effs oeffs m
  . (Monad m, Members '[Tell [(String, Integer)],GetCPUTime] oeffs)
  => (forall x . Effs oeffs m x -> m x)
  -> (forall x . Effs '[Profile] m x -> m x)
timerAlg oalg (Eff (Scp (Profile name p))) =
  do t  <- eval oalg getCPUTime
     k  <- p
     eval oalg $ do
        t' <- getCPUTime
        tell [(name, t' - t)]
     return k
```
How exactly `getCPUTime` is measured, and what is done with the `ask` is left
to another handler. This easily allows, for instance, different ways of measuring time
to be implemented, or for logs to be enabled and disabled.

More generally, there may be other instruments that could be used, and indeed
the `timer` handler can alternatively be defined by using `profiler`:
```haskell
timer' :: Handler '[Profile] '[Tell [(String, Integer)], GetCPUTime] '[] '[]
timer' = profiler (flip (-)) getCPUTime
```
A new `profiler f instrument p` will inject the `instrument` before and after
`p` and collect two measurements: one before `p` and another after `p` is
executed. These are then combined by the given function `f` and emitted using
`ask`.
```haskell
profiler :: forall instr a b . (HFunctor instr, Member instr '[Tell [(String, b)], instr])
  => (a -> a -> b) -> Prog '[instr] a -> Handler '[Profile] '[Tell [(String, b)], instr] '[] '[]
profiler f instrument = interpretM (profilerAlg @instr f instrument)

profilerAlg :: forall instr effs oeffs m a b
  .  (HFunctor instr, Monad m, Member (Tell [(String, b)]) oeffs, Member instr oeffs)
  => (a -> a -> b)
  -> (Prog '[instr] a)
  -> (forall x . Effs oeffs m x -> m x)
  -> (forall x . Effs '[Profile] m x -> m x)
profilerAlg f instrument oalg (Eff (Scp (Profile name p))) =
  do t  <- eval oalg (weakenProg instrument)
     k  <- p
     eval oalg $ do
        t' <- (weakenProg instrument)
        tell [(name, f t t')]
     return k
```

For our teletype example, we can instrument all of the `getLine` operations
with a profiler as follows:
```haskell
getLineProfile :: Handler '[GetLine] '[Profile, GetLine] '[] '[]
getLineProfile = interpret alg where
  alg :: Effs '[GetLine] m x -> Prog [Profile, GetLine] x
  alg (Eff (Alg (GetLine k))) = profile "getLine" (getLine >>= return . k)
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
{-# LANGUAGE DataKinds #-}    -- Used for the list of effects
{-# LANGUAGE GADTs     #-}    -- Used for syntax
```
<!--
The following pragma is only needed for the testing framework.
```haskell top
{-# LANGUAGE TemplateHaskell #-}
```
-->

Imports
-------

This file has a number of imports:

```haskell top
import Control.Effect
import Control.Effect.Algebraic
import Control.Effect.Scoped
import Control.Effect.IO
import Control.Effect.State
import Control.Effect.Writer hiding (uncensors)

import Control.Monad.Trans.Identity
import Control.Monad.Trans.Compose
import Control.Monad.Trans.State.Strict (StateT)
import Control.Monad.Trans.Reader (ReaderT)
import Control.Monad.Trans.Writer (WriterT)

import Data.List.Kind
import Data.Char (toUpper)
import Data.HFunctor

import Prelude hiding (putStrLn, getLine)
```

<!--
We will hide the following from the README, because it is
only for testing the documentaton itself.
```haskell top
import Hedgehog hiding (test, evalIO, eval)
import Hedgehog.Main
import Hedgehog.Gen hiding (map)
import Hedgehog.Range

props :: Group
props = $$(discover)

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