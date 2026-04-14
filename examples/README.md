Effective Examples
==================

This package contains examples of effects and handlers created using `effective`
which you can refer to for guidance when defining your own. Contributions
welcome!


README
------

This README is a literate Haskell file and therefore can be executed:
```console
git clone effective
cd effective/examples
cabal test readme
cabal repl readme
```
This should test some properties and then bring you into `ghci` where you can
follow the examples.


Scoped Effects
--------------

### Scope (minimal example)

_Module:
[`Control.Effect.Examples.Scoped.Scope`](./src/Control/Effect/Examples/Scoped/Scope.hs)_

Each `scope` scoped operation takes a single continuation. The corresponding
`scopeId` handler will simply run these continuations when the `scope` operation
is encountered, without applying any monad transformers.

``` haskell
scopeExample :: Int ! '[Scope]
scopeExample = do
  result <- scope $ do
    return (19 + 23)

  return result
```

``` console
ghci> handle scopeId scopeExample
42
```

<!--
``` haskell
prop_scopeId :: Property
prop_scopeId = property $ do
  x <- forAll (Gen.int (Range.linear 0 1000))
  let p = scope (return x)
  handle scopeId p === x
```
-->


<!--
Language extensions:

``` haskell top
{-# LANGUAGE TemplateHaskell #-}
```
-->


Imports
-------

This file has a number of imports:

``` haskell top
import Control.Effect
import Control.Effect.Examples
```

<!--
Testing entrypoint:

``` haskell top
import Hedgehog (Property, checkParallel, discover, forAll, property, (===))
import Hedgehog.Main (defaultMain)
import Hedgehog.Gen qualified as Gen
import Hedgehog.Range qualified as Range

main :: IO ()
main = defaultMain [checkParallel $$(discover)]
```
-->
