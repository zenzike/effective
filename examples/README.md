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

### Identity (minimal example)

_Module:
[`Control.Effect.Examples.Scoped.Identity`](./src/Control/Effect/Examples/Scoped/Identity.hs)_

The `identity` scoped operation takes a single continuation. The corresponding
`runIdentity` handler will simply run these continuations when the `identity`
operation is encountered, without applying any monad transformers.

``` haskell
identityExample :: Int ! '[Identity]
identityExample = do
  result <- identity $ do
    return (19 + 23)

  return result
```

``` console
ghci> handle runIdentity identityExample
42
```

<!--
``` haskell
prop_identity :: Property
prop_identity = property $ do
  x <- forAll (Gen.int (Range.linear 0 1000))
  let p = identity (return x)
  handle runIdentity p === x
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
import Control.Effect hiding (Identity, identity)
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
