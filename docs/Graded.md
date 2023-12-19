```haskell top:0
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MonoLocalBinds #-}

```

```haskell top:1
module Graded where

import Control.Effects
import Control.Family.AlgScp
import qualified Control.Effect.State as State
import Control.Effect.State hiding (get, put)
import Control.Effect.Maybe hiding (catch, throw)
import qualified Control.Effect.Maybe as Maybe
import Data.List.Kind (Union, Insert)
import Control.Monad (replicateM_)
```

A different way of using this library is to use _graded monads_.
This offers a bottom-up type inference for programs rather than a
top-down one.

* *Top-down* With a top-down strategy, the handlers dictate the
  effects that the program accepts. This is the "members" way of working
  with the `effective` library, where the type of programs remains flexible,
  and the input list of handlers is rigid, and is the default.

* *Bottom-up* (graded): With a bottom-up strategy, the programs dictate the
  effects that must be handled. This is the "graded" way of working with the
  `effective` library, where the type of programs is rigid, and
  the input list of handlers is flexible. This is described in more detail
  in this file.

In the graded interface to this library the types of programs are more precise
making it harder to make mistakes, but also harder to write since the types are
less forgiving!

To use the library in this way, the operations must be made monomorphic,
where the signature exposes only the effect that is used:
```haskell
get :: Prog '[Get s] s
get = State.get

put :: s -> Prog '[Put s] ()
put = State.put

throw :: Prog '[Throw] ()
throw = Maybe.throw
```

To use these operations together requires a graded `do` block:
```haskell
incr :: Prog '[Get Int, Put Int] ()
incr = Graded.do
  x <- get
  put @Int (x + 1)
```
This is made possible by enabling the `QualifiedDo` language
extension, and when the appropriate import:
```haskell top:0
{-# LANGUAGE QualifiedDo #-}
```
```haskell top:1
import qualified Control.Monad.Graded as Graded
```


Note that the `incr` program would not compile with the signature `Prog '[Put
Int, Get Int] ()`, where the effects are reversed, since it is _flow_ typed:
the type of the program must follow the control flow of its effects.


A flow-graded program is not always compatible with conditionals,
since both branches of an `if_then_else_` must have the same type.
In the `decr` program, one branch only exposes a `Put Int`
effect, whereas the other is `Throw`.
In order to make both branches have the same effects, one approach
is to use `return` with a suitable signature that allows the
branches to unify:
```haskell
decr :: Prog [Get Int, Put Int, Throw] ()
decr = Graded.do
  x <- get
  if (x > 0)
    then Graded.do return () :: Prog [Put Int, Throw] ()
                   put @Int (x - 1)
    else Graded.do return () :: Prog [Put Int, Throw] ()
                   throw
```
This can be fixed by using `RebindableSyntax` and offering a more
flexible version of conditionals that unifies the type of its
branches in the output. However, at present GHC does not allow
rebinding of `case`.



The definition of scoped operations fits neatly with member style operations,
but a little more care is required. Consider the type of `catch`:
```haskell ignore
catch
  :: (Member Catch sig) => Prog sig a -> Prog sig a -> Prog sig a
catch p q = injCall (Scp (Catch (fmap return (p))
                                (fmap return (q))))
```
The subprograms `p` and `q` will have their types unified with the output of
`catch`. The type of the subprograms cannot be fixed in advance, which means
that a `Member` constraint will be required. For the purposes of unification,
it is convenient if the programs `p` and `q` have the same type signature,
sharing `sig` with the overall type.

A more precise type to `catch` can be given where the two subprograms can have
differing types, so long as they can be injected into the final type. 
```haskell
catch
  :: ( Member Catch sig''
     , Injects sig  sig''
     , Injects sig' sig''
     , sig'' ~ Insert Catch (Union sig sig'))
  => Prog sig a -> Prog sig' a -> Prog sig'' a
catch p q = injCall (Scoped (Catch
  (fmap return (weakenProg p))
  (fmap return (weakenProg q))))
```


```haskell ignore
catchDecr :: Prog [Get Int, Put Int, Throw, Catch] ()
catchDecr = Graded.do
  decr
  catch
    (Graded.do decr
               decr)
    (Graded.return ())
```

```haskell
catchDecr :: Prog [Get Int, Put Int, Throw, Catch] ()
catchDecr = Graded.do
  decr
  catch
    (Graded.do decr
               decr)
    (Graded.do replicateM_ 44 incr)

-- monus :: Int -> Int -> Prog '[Throw] Int
-- monus x y = do if x < y then throw else return (x - y)


-- safeMonus :: Int -> Int -> Prog [Throw, Catch] Int
-- safeMonus x y = catch' (monus' x y) (return 0 :: Prog '[] Int)
```
