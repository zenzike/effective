```haskell
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE QualifiedDo #-}

module State where

import Hedgehog
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range

import Control.Effects
import Control.Handler
import Control.Effect.State
import Control.Effect.Maybe
import Control.Monad (replicateM_)

incr :: Prog' '[Get Int, Put Int] ()
incr = do
  x <- get
  put @Int (x + 1)

example_incr :: Property
example_incr = property $ do
  n <- forAll $ Gen.int $ Range.linear 1 1000
  handle (state n) incr === (n+1,())

decr :: Prog' '[Get Int, Put Int, Throw] ()
decr = do
  x <- get
  if x > 0
    then put @Int (x - 1)
    else throw

catchDecr :: Prog' [Get Int, Put Int, Throw, Catch] ()
catchDecr = do
  decr
  catch
    (do decr
        decr)
    (return ())

catchDecr' :: Prog [Get Int, Put Int, Throw, Catch] ()
catchDecr' = catchDecr @[Get Int, Put Int, Throw, Catch]

globalState
  :: s -> ASHandler '[Throw, Catch, Put s, Get s]
                    '[]
                    '[(,) s, Maybe]
globalState s = except <&> state s

-- This is global state because the `Int` is decremented
-- twice before the exception is thrown.
example_globalState :: Property
example_globalState = property $
    (handle (globalState 2) catchDecr :: (Int, Maybe ()))
  ===
    (0,Just ())

localState
  :: s -> ASHandler '[Put s, Get s, Throw, Catch]
                    '[]
                    '[Maybe, ((,) s)]
localState s = state s <&> except

-- With local state, the state is reset to its value
-- before the catch where the exception was raised.
example_localState :: Property
example_localState = property $
    (handle (localState 2) catchDecr :: Maybe (Int, ()))
  ===
    Just (1, ())

example_localState' :: Property
example_localState' = property $
    (handle (localState 2) catchDecr :: Maybe (Int, ()))
  ===
    Just (1, ())

example_decr :: Property
example_decr = property $ do
  n <- forAll $ Gen.int $ Range.linear (-1000) 1000
  if n > 0
    then handle (localState n) decr === Just (n - 1,())
    else handle (localState n) decr === Nothing

example_incrDecr :: Property
example_incrDecr = property $ do
  n <- forAll $ Gen.int $ Range.linear (-1000) 1000
  if n >= 0
    then handle (localState n) (do incr; decr) === Just (n, ())
    else handle (localState n) (do incr; decr) === Nothing

example_decr' :: Property
example_decr' = property $ do
  n <- forAll $ Gen.int $ Range.linear (-1000) 1000
  if n > 0
    then handle (globalState n) decr === (n - 1, Just ())
    else handle (globalState n) decr === (n, Nothing)

example_incrDecr' :: Property
example_incrDecr' = property $ do
  n <- forAll $ Gen.int $ Range.linear 0 1000
  if n >= 0
    then handle (globalState n) (do incr; decr) === (n, Just ())
    else handle (globalState n) (do incr; decr) === (n+1, Nothing)

catchDecr44 :: Prog' '[Get Int, Put Int, Throw, Catch] ()
catchDecr44 = do
  decr
  catch
    (do decr
        decr)
    (do replicateM_ 44 incr)

-- For instance you might want to allocate a bit more memory ...
-- and a bit more ... and so on.
example_Retry1 :: Property
example_Retry1 = property $
    (handle (retry <&> state 2) catchDecr44 :: (Int, Maybe ()))
  ===
    (42,Just ())

examples :: Group
examples = $$(discoverPrefix "example_")
```haskell
