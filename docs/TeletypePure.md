<!--
```haskell
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

module TeletypePure where

import Prelude hiding (getLine, putStrLn)

import Control.Effect
import Control.Effect.State
import Control.Effect.Writer

import Handlers

import Hedgehog
import Hedgehog.Gen hiding (map, maybe)
import Hedgehog.Range
```
-->

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
getLineState = interpret1 $ \(GetLine k) ->
  do xss <- get
     case xss of
       []        -> return (k "")
       (xs:xss') -> do put xss'
                       return (k xs)
```

The signature of `getLineState` says that it is a handler that recognizes
`GetLine` operations and interprets them in terms of output effects `Get [String]` and `Put [String]`.
Interpreting effects in terms of other, more primitive, effects allows other
handlers to deal with those more primitive effects.

The `getLineState` handler will process the `GetLine` effect in the
echo program, and in so doing will output `Get [String]` and `Put [String]`
effects. These can be handled by a state handler. The output of the
`getLineState` handler can be piped into the `state` handler to produce
a new handler. Here are two variations:
```haskell
getLinePure :: [String] -> Handler '[GetLine] '[] '[StateT [String]] a (a, [String])
getLinePure str = getLineState \\ (state str)

getLinePure_ :: [String] -> Handler '[GetLine] '[] '[StateT [String]] a a
getLinePure_ str = getLineState \\ (state_ str)
```
Now we have a means of executing a program that contains only a `GetLine` effect,
and extracting the resulting string:
```haskell ignore
handle (getLinePure ["hello", "world!"]) :: Prog '[GetLine] a -> (a, [String])
```
Executing this will get the first line in the list of strings and return its length,
and the same program can be executed either processed with IO.
```console
ghci> handle (getLinePure ["Hello", "world!"]) getLineLength
(5,["world!"])
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
putStrLnTell = interpret1 $ \(PutStrLn str k) ->
  do tell [str]
     return k
```
This can in turn be piped into the `writer` handler to make
a pure version of `putStrLn`:
```haskell
putStrLnPure :: Handler '[PutStrLn] '[] '[WriterT [String]] a ([String], a)
putStrLnPure = putStrLnTell \\ writer
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
             ([String], (a, Int))
teletypeTick str = getLineIncrState |> teletype str
```
This can be executed using `handle`, passing in the
list of inputs to be fed to `getLine`:
```console
ghci> handle (teletypeTick ["Hello", "world!"]) echo
(["Hello","world!"],((),3))
```
<!--
```haskell
prop_teletypeTick :: Property
prop_teletypeTick = property $ do
  xss <- forAll $ list (linear 0 1000) (string (linear 0 100) ascii)
  let xss' = takeWhile (/= "") xss
  handle (teletypeTick xss) echo === (xss', ((), length xss' + 1))
```
-->

<!--
```haskell
examples :: Group
examples = Group "Pure Teletype"
  [ ("teletypePure", prop_teletypePure)
  , ("teletypeTick", prop_teletypeTick)
  ]
```
-->
