
A modal text editor is an example of an effectful system with scoped operations.

```haskell
module Editor where

data Mode' k where
  InsertMode :: k -> Mode' k
  NormalMode :: k -> Mode' k
  deriving Functor
type Mode = Scoped Mode'

insertMode :: Member Mode sig => Prog sig a -> Prog sig a
insertMode = injCall (Scoped (InsertMode (fmap return p)))

normalMode :: Member mode sig => Prog sig a -> Prog sig a
insertMode = injCall (Scoped (NormalMode (fmap return p)))

editor :: Members '[Mode] sig => Prog sig a
editor = undefined
```

