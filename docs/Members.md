<!--
```haskell
{-# LANGUAGE OverloadedStrings #-}

module Members where

import Hedgehog
```
-->

Members
-------

There are three scenarios to consider when trying to engineer a fit between a
program (shaft) of type `Prog effs a` and a handler (hole) of type
`Handler ieffs oeffs ts fs`, depending on how their interfaces correspond:

1. *Transition* (`effs = ieffs`): The program and the handler have the same
   effects. In the effective library, every effect is
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

<!--
```haskell
examples :: Group
examples = Group "Members" []
```
-->
