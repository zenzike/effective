<!--
```haskell
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

module ScopedOperations where

import Prelude hiding (getLine, putStrLn)

import Control.Effect
import Control.Effect.Reader (ReaderT)
import Control.Effect.Writer hiding (uncensors)

import Data.Char (toUpper)

import Handlers
import TeletypePure

import Hedgehog
import Hedgehog.Gen hiding (map, maybe)
import Hedgehog.Range
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
retell :: forall w w' a .
          (w -> w')
       -> Handler '[Tell w] '[Tell w'] '[] a a
retell f = interpret1 $ \(Tell w k) ->
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
censor  :: Member (Censor w) effs => (w -> w) -> Prog effs a -> Prog effs a
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
hide :: forall heffs effs oeffs f . (Members (effs :\\ heffs) effs, Members oeffs oeffs)
     => Proxy heffs
     -> Handler effs             oeffs f
     -> Handler (effs :\\ heffs) oeffs f
```
This takes in a handler, returns it where any effects provided by the type parameter `heffs`
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
rePutStrLn f = interpret1 $ \(PutStrLn str k) ->
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
tellPutStrLn = interpret1 $ \(Tell strs k) ->
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

<!--
```haskell
examples :: Group
examples = Group "Scoped Operations"
  [ ("esiotrot",   prop_esiotrot)
  , ("uncensors",  prop_uncensors)
  , ("rePutStrLn", prop_rePutStrLn)
  ]
```
-->
