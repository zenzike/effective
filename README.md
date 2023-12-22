Effective
==========

The `effective` library is an effect handlers library for Haskell that is
designed to allow users to define and interpret their own languages and
effects. This library incorporates support for both algebraic and scoped
effects, and is an implementation of the theory presented in [Modular Models of
Monoids with Operations](https://dl.acm.org/doi/10.1145/3607850) by Yang and
Wu, as well as [Effect Handlers in
Scope](https://dl.acm.org/doi/10.1145/2633357.2633358) by Wu, Schrijvers, and
Hinze.

This README is a literate Haskell file and therefore can be executed. You can interact
with its contents with `cabal repl readme` and follow the examples. The language extensions and imports required are at the bottom of this file.


Working with IO
---------------

The `Teletype` example is a rite of passage for monadic IO [^Gordon1992] where
the challenge is to show how IO of reading from and writing to the terminal can
be achieved. A program that interacts with the terminal is `echo`. This is a
simple program that will continue to echo the input obtained by `getLine` is
output to the terminal using `putStrLn` until a blank line is received by
`getLine`:
```haskell
echo :: Prog' [GetLine, PutStrLn] ()
echo = do str <- getLine
          unless (null str) $
            do putStrLn str
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
terminal user is immediately echoed back out to the terminal.


Working with Handlers
---------------------

A pure state effect is provided in `Effect.Control.State`, which supports
`get` and `put` as operations that are indicated by `Get s` and `Put s`
in a signature.

For example, here is a program that increments the number in a state
and returns it:
```haskell
incr :: Prog' [Put Int, Get Int] ()
incr = do x <- get
          put @Int (x + 1)
```
In order to keep the program modular, the effects in `effs` are given by a
constraint on the input type, saying that `Put Int` and `Get Int` are its
members.

This program can be executed by using a handler. For state, the usual
handler is given by:
```haskell ignore
state :: s -> ASHandler '[Put s, Get s]  -- input effects
                        '[]              -- output effects
                        '[((,) s)]       -- output wrapper
```
The signature of the handler tells us how it behaves:
* The input effects are `Put s` and `Get s`.
* The output effects are empty
* The output of this handler wraps the result with the functor `((,) s)`
When `state s` is used to handle a program of type `Prog effs a`,
the output will be the functor `((,) s)` applied to the value of the program
`a`, which is simply `(s, a)`.

Executing the `incr` program with this handler can be achieved as follows:
```haskell ignore
ghci> handle (state 41) incr :: (Int, ())
(42,())
```
Since the program has type `Prog effs ()`, with a pure value of `()`,
the result of applying the handler is `((,) Int)` applied to `()`,
thus giving back `(Int, ())`.

The type of the `state` handler promises to handle both `Put s` and `Get s`
operations, and so it is able to work with programs that use both, or
either one of these. Here is a program that only uses `Get String`:
```haskell
getStringLength :: Prog' '[Get String] Int
getStringLength = do xs <- get @String
                     return (length xs)
```
It can be handled using `state`:
```haskell ignore
ghci> handle (state "Hello!") getStringLength
("Hello!",6)
```
Notice that the `state` handler returns the final state as well as the final
return value of the program. A variation of the `state` handler is `state_`,
which does not return the final state:
```haskell ignore
state_ :: s -> ASHandler [Put s, Get s] '[] '[]
```
Here the final output wrapper is `'[]`, and so applying this to a program
of type `Prog sig a` will simply return a value of type `a`.
```haskell ignore
ghci> handle (state_ "Hello!") (do xs <- get @String; return (length xs))
6
```

The effect of `handle h p` is to use the handler `h` to remove _all_ the
effects in interpreting the program `p`. This relates to both the effects
of the program and effects output by a handler.
Trying to apply a handler that does not fully evaluate the effects in `p` will
result in a type error.
For example, the `echo` program cannot be handled with a state handler:
```haskell ignore
ghci> handle (state "Hello") echo

<interactive>:2:24: error: [GHC-39999]
    • No instance for ‘Member' GetLine '[] (ElemIndex GetLine '[])’
        arising from a use of ‘echo’
    • In the second argument of ‘handle’, namely ‘echo’
      In the expression: handle (state "Hello") echo
      In an equation for ‘it’: it = handle (state "Hello") echo
```
This is essentially saying that `GetLine` is not supported by the state
handler.


Forwarding Effects
------------------

Now suppose that the task is to count the number of times `getLine` is called
when the `echo` program is executed. One approach is to change the `echo`
program, and write something like `echoTick`, where an `incr` has been added
after each `getLine`:
```haskell
echoTick :: Prog' '[GetLine, Get Int, Put Int, PutStrLn] ()
echoTick =
  do str <- getLine
     incr
     unless (null str) $
       do putStrLn str
          echoTick
```
To execute such a program that uses both state and IO
requires a handler that is specialized to deal with IO:
```haskell
exampleEchoTick :: IO (Int, ())
exampleEchoTick = handleIO (state (0 :: Int)) echoTick
```
When this is executed, it counts the number of lines received:
```haskell ignore
ghci> exampleEchoTick
Hello
Hello
world!
world!

(3,())
```
This demonstrates how unhandled effects that are recognized by I/O can be
forwarded and dealt with after the execution of the handler.


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
  :: ASHandler '[GetLine]                       -- input effects
               '[GetLine, Get Int, Put Int]     -- output effects
               '[]                              -- output wrapper
getLineIncr = interpret $
  \(Eff (Algebraic (GetLine k))) ->
    do str <- getLine
       incr
       return (k str)
```
The handler says that it will deal with `[GetLine]` as an input effect,
and will output the effects `[GetLine, Get Int, Put Int]`.

Now the task is to connect this handler with `state`. This can
be achieved with a `pipe`:
```haskell
getLineIncrState :: ASHandler '[GetLine]   -- input effects
                              '[GetLine]   -- output effects
                              '[(,) Int]   -- output wrapper
getLineIncrState
  = pipe getLineIncr (state (0 :: Int))
```
This can then be executed using `handleIO`, which will deal with
the residual `GetLine` effect:
```haskell ignore
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
getLineLength :: Prog' '[GetLine] Int
getLineLength = do str <- getLine
                   return (length str)
```
As before, this can be evaluated using `evalIO`:
```haskell ignore
ghci> evalIO getLineLength
Hello
5
```
Better would be to provide those lines purely from a pure
list of strings. Here is how `getLine` can be interpreted in terms of the
operations `get` and `put` from a state containing a list of strings:
```haskell
getLineState
  :: Handler '[GetLine] '[Get [String], Put [String]] '[] fam
getLineState = interpret $
  \(Eff (Algebraic (GetLine k))) -> 
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
getLinePure :: [String] -> ASHandler '[GetLine] '[] '[(,) [String]]
getLinePure str = pipe getLineState (state str)

getLinePure_ :: [String] -> ASHandler '[GetLine] '[] '[]
getLinePure_ str = pipe getLineState (state_ str)
```
Now we have a means of executing a program that contains only a `GetLine` effect,
and extracting the resulting string:
```haskell ignore
handle (getLinePure ["hello", "world!"]) :: Prog '[GetLine] a -> ([String], a)
```
Executing this will get the first line in the list of strings and return its length,
and the same program can be executed either processed with IO.
```haskell ignore
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
```
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
```haskell ignore
ghci> handleIO (getLinePure_ ["Hello", "world!"]) echo
Hello
world
```
However, there is another solution: the `putStrLn` operation can also be
redirected to do something pure.

Outputting pure values is managed by the `writer` handler, in combination
with the `tell` operation:
```haskell ignore
writer :: Monoid w => Handler '[Tell w] '[] '[(,) w]
tell   :: Monoid w => w -> Prog' '[Tell w] ()
```
The signatures tell us that `tell` introduces the `Tell` effect, and
`writer` handles this effect.

The following simple example returns a list of strings, since a list of
elements is a monoid:
```haskell ignore
ghci> handle writer (tell ["Hello", "World!"]) :: ([String], ())
(["Hello","World!"],())
```
Using this, values can be written as the output of a program.

Now the task is to interpret all `putStrLn` operations in terms of the
`tell` operation:
```haskell
putStrLnTell :: Handler '[PutStrLn] '[Tell [String]] '[] fam
putStrLnTell = interpret $
  \(Eff (Algebraic (PutStrLn str k))) ->
     do tell [str]
        return k
```
This can in turn be piped into the `writer` handler to make
a pure version of `putStrLn`:
```haskell
putStrLnPure :: ASHandler '[PutStrLn] '[] '[(,) [String]]
putStrLnPure = pipe putStrLnTell writer
```
Now, a pure handler for both `putStrLn` and `getLine` can
be defined as the fusion of `putStrLnPure` and `getLinePure`.
```haskell
teletypePure
  :: [String]
  -> ASHandler '[GetLine, PutStrLn] '[] '[(,) [String]]
teletypePure str = fuse (getLinePure_ str) putStrLnPure
```
The `fuse` combinator takes two handlers and creates one that accepts the union
of their signatures. The handlers are run in sequence so that the output of the
first handler is fed into the input of the second. Any remaining output
operations are combined and become the output of the fusion.

Now the `echo` program can be executed in an entirely pure context:
```haskell ignore
ghci> handle (teletypePure ["Hello", "world!"]) echo
(["Hello","world!"],())
```
<!--
```haskell
prop_teletypePure :: Property
prop_teletypePure = property $ do
  xss <- forAll $ list (linear 0 1000) (string (linear 0 100) ascii)
  let xss' = takeWhile (/= "") xss
  handle (teletypePure xss) echo === (xss', ())
```
-->
The return value of `()` comes from the result of `echo` itself, and the list
of strings is the accumulated result of the `tell` commands.

One challenge is to count the number of times `getLine` is executed
while also processing it purely. No problem, the `getLineIncrState` can be used
to interpret `getLine` before passing the resulting `getLine` to `teletypePure`:
```haskell
teletypeTick
  :: [String]
  -> ASHandler '[GetLine, PutStrLn] '[] '[(,) [String], (,) Int]
teletypeTick str = fuse getLineIncrState (teletypePure str)
```
This can be executed using `handle`, passing in the
list of inputs to be fed to `getLine`:
```haskell ignore
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
retell :: forall w w' fam . (Monoid w, Monoid w') => (w -> w') -> Handler '[Tell w] '[Tell w'] '[] fam
retell f = interpret $
  \(Eff (Algebraic (Tell w k ))) -> 
    do tell (f w)
       return k
```
Simply put, every `tell w` is intercepted, and retold as `tell (f w)`. Thus,
a simple message can be made louder at the flick of a switch:
```haskell ignore
ghci> handle (retell (map toUpper) <&> writer @String) (tell "get bigger!")
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
hoppy :: Prog' '[Tell [String], Censor [String]] ()
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
```haskell ignore
ghci> handle (censors @[String] id <&> writer) hoppy :: ([String], ())
(["Hello Alfie!","esiotrot","!REGGIB TEG","Goodbye!"],())
```
Notice how `"get bigger!"` is both reversed and made uppercase because
the ciphers have been accumulated.
<!--
```haskell
prop_esiotrot :: Property
prop_esiotrot = property $ do
  handle (censors @[String] id <&> writer) hoppy === (["Hello Alfie!","esiotrot","!REGGIB TEG","Goodbye!"],())
```
-->

Hiding Operations
-----------------

Since `censor` is an operation, it can be given different semantics by a
different handler. For instance, here is type of the `uncensor` handler:
```haskell ignore
uncensors :: forall w . Monoid w => Handler '[Censor w] '[] '[]
```
This handler removes all censorship from the program. The type promises that no other
effects are generated, and that the result is pure.
```haskell ignore
ghci> handle (uncensors @[String] <&> writer @[String]) hello
(["Hello world!","tortoise","get bigger!","Goodbye!"],())
```
One way to define `uncensors` is to process all `censor` operations with
`censors id`, followed by the `writer_` handler (which discards its output) to
remove any generated `tell` operations. To prevent this handler from touching
any `tell` operations that were in the program before censor, the `hide`
combinator removes them from being seen:
```haskell
uncensors :: forall w fam . Monoid w => Handler '[Censor w] '[] '[] ASFam
uncensors = hide @'[Tell w] (censors @w id <&> writer_ @w)
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
  handle (uncensors @[String] <&> writer) hoppy === (["Hello Alfie!","tortoise","get bigger!","Goodbye!"],())

prop_uncensors' :: Property
prop_uncensors' = property $ do
  handle (W.uncensors @[String] <&> writer) hoppy === (["Hello Alfie!","tortoise","get bigger!","Goodbye!"],())
```
-->

Censoring `PutStrLn`
--------------------

The `censors` handler is designed to work with the interaction between `censor`
and `tell`. Suppose the task is now to censor the `echo` program.
It is easy enough to see how a variation of `retell` could be written,
by interpreting `PutStrLn` operations:
```haskell
rePutStrLn :: (String -> String) -> Handler '[PutStrLn] '[PutStrLn] '[] fam
rePutStrLn f = interpret $
  \(Eff (Algebraic (PutStrLn str k))) -> do putStrLn (f str)
                                            return k
```

```haskell ignore
ghci> handle (rePutStrLn (map toUpper) <&> teletypePure ["tortoise"]) echo
(["TORTOISE"],())
```
<!--
```haskell
prop_rePutStrLn :: Property
prop_rePutStrLn = property $ do
  xss <- forAll $ list (linear 0 1000) (string (linear 0 100) ascii)
  let xss' = takeWhile (/= "") xss
  handle (rePutStrLn (map toUpper) <&> teletypePure xss) echo
    === (map (map toUpper) xss',())
```
-->

A more localized approach is to use the `censor` operation so
that a censored echo can be used:
```haskell
shoutEcho :: Prog' [Censor [String], GetLine, PutStrLn] ()
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
tellPutStrLn :: Handler '[Tell [String]] '[PutStrLn] '[] fam
tellPutStrLn = interpret $
  \(Eff (Algebraic (Tell strs k))) -> do putStrLn (unwords strs)
                                         return k
```
This chain of handlers might be called `censorsPutStrLn`:
```haskell
censorsPutStrLn
  :: (fam (Effs '[Tell [String]]), fam (Effs '[]),
      fam (Effs [Tell [String], Censor [String]]))
  => ([String] -> [String])
  -> Handler '[PutStrLn, Tell [String], Censor [String]]
             '[PutStrLn]
             '[]
              fam
censorsPutStrLn cipher = putStrLnTell <&> censors cipher <&> tellPutStrLn
```
The ensuing chain of handlers seems to do the job:
```haskell ignore
ghci> handle (censorsPutStrLn id <&> teletypePure ["Hello world!"])
             shoutEcho
(["HELLO WORLD!"],())
```
<!--
```haskell
prop_shouty :: Property
prop_shouty = property $ do
  handle (censorsPutStrLn id <&> teletypePure ["Hello world!"]) shoutEcho
    === (["HELLO WORLD!"],())
```
-->
However, things can get muddled if the program contains a mixture
of `tell` and `putStrLn` operations.

For example, here is a program that uses `tell` to log the fact
that the shouty echo program is being entered before doing so:
```haskell
logShoutEcho :: Prog' '[PutStrLn, GetLine, Censor [String], Tell [String]] ()
logShoutEcho = do tell ["Entering shouty echo"]
                  shoutEcho
```
It is tempting to execute the program with the following:
```haskell ignore
ghci> handle (censorsPutStrLn id <&> teletypePure ["Hello world!"]) logShoutEcho
(["Entering shouty echo","HELLO WORLD!"],())
```
<!--
```haskell
prop_logShouty :: Property
prop_logShouty = property $ do
  handle (censorsPutStrLn id <&> teletypePure ["Hello world!"]) logShoutEcho
    === (["Entering shouty echo","HELLO WORLD!"],())
```
-->
It seems to work, but the problem is that the logged messages are treated
in exactly the same way as the pure `putStrLn` values: everything is
accumulated into the same list of strings. The problem is exasperated
when `handleIO` is used: the logged messages are immediately output to the
terminal:
```haskell ignore
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
```haskell ignore
ghci> handle (writer @[String] <&> censorsPutStrLn id <&> teletypePure ["Hello world!"]) logShoutEcho
(["HELLO WORLD!"],(["Entering shouty echo"],()))
```
<!--
```haskell
prop_logShoutEcho :: Property
prop_logShoutEcho = property $ do
  handle (writer @[String] <&> censorsPutStrLn id <&> teletypePure ["Hello world!"]) logShoutEcho
    === (["HELLO WORLD!"],(["Entering shouty echo"],()))
```
-->
This pure version separates the two kinds of logged messages; those
that come from `tell` are processed first (and so in the inner tuple),
and then the messages from `putStrLn` are on the outside.

This even works with `handleIO`:
```haskell ignore
ghci> handleIO (writer @[String] <&> censorsPutStrLn id) logShoutEcho
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
occurrence of the log:
```haskell
logger :: String -> Prog' [Tell [(Integer, String)], GetCPUTime] ()
logger str = do time <- getCPUTime
                tell [(time, str)]
```

Members
-------

There are three scenarios to consider when trying to engineer a fit between a
program (shaft) of type `Prog effs a` and a handler (hole) of type `Handler
ieffs ts fs oeffs`, depending on how their interfaces correspond:

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
   effects can be dealt with using an algebra as a parameter to `handleWith`.

When there is transition between program and handler, there may be a difference
in the orders of the effects presented in the signatures. The philosophy of 
effect handlers is that a program can be handled in different ways to create
different semantics. Although it is reasonable for a program to insist on a
particular order in which certain effects should be handled, the `effective`
library leaves this choice entirely to the handler.

Graded Effects
--------------

There are two of defining operations using `effective`, which we will call
_graded_ style and _member_ style. In graded style operations the signature
parameter to `Prog` says precisely which effects are present in a program: On
the other hand, in member style an operation is in fact a family of operations
where there is a `Member` constraint for effect. The graded technique is
considered more advanced and is detailed more carefully in the
[documentation](docs/Graded.md).


Language Extensions
-------------------

The `effective` library requires the `DataKinds` extension since
this is used to keep track of effect signatures.

```haskell top
{-# LANGUAGE DataKinds #-}     -- Used for the list of effects
{-# LANGUAGE GADTs #-}         -- Pattern match on GADTs
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
import Control.Monad (unless)
import Control.Effect
import Control.Handler
import Control.Family.AlgScp
import Control.Effect.State
import Control.Effect.Writer hiding (uncensors)
import qualified Control.Effect.Writer as W
import Control.Effect.IO

import Data.Char (toUpper)

import Prelude hiding (putStrLn, getLine)
import Data.Char (toUpper)
```

<!--
We will hide the following from the README, because it is
only for testing the documentaton itself.
```haskell top
import Hedgehog hiding (test, evalIO)
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

[^Gordon1992]: A. Gordon. Functional Programming and Input/Output. PhD Thesis, King's College London. 1992

