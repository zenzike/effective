{-|
Module      : Main
Description : Test suite
License     : BSD-3-Clause
Maintainer  : Nicolas Wu
Stability   : experimental

= Approach

Laws are tested as equations between programs. Both sides are run under a
handler, with random values and with random programs built by "Gen" from the operations of each effect, for the
computations that the equation leaves free.
The treatment of fused handlers follows Yang and Wu [2021], who study which
combination of theories a composite of modular handlers is correct for.

  * Sum: a composite respects the equations of
    its parts. Tested in "Fusion.Sum" with `Law.sum`, which runs the laws
    of each effect against fusions.

  * Commutative tensor: the operations of the two theories commute.
    Tested in "Fusion.Commute".

  * Distributive tensor: the operations of the
    one theory distribute over those of the other. 
    Tested in "Fusion.Distribute".

  * Other equations between two effects: for instance the
    put-or law of global state. Tested in "Fusion.Interact".

= Reference

[Yang and Wu 2021] Zhixuan Yang and Nicolas Wu. Reasoning about Effect
Interaction by Fusion. /Proc. ACM Program. Lang./ 5, ICFP, Article 73.
<https://doi.org/10.1145/3473578>
-}
module Main (main) where

import Test.Tasty

import qualified Effect.State as State
import qualified Effect.Reader as Reader
import qualified Effect.Writer as Writer
import qualified Effect.Maybe as Maybe
import qualified Effect.Except as Except
import qualified Effect.Nondet as Nondet
import qualified Effect.Concurrency as Concurrency
import qualified Effect.HStore as HStore
import qualified Effect.WithName as WithName
import qualified Effect.IO as IO
import qualified Effect.Yield as Yield
import qualified Fusion.Sum as Sum
import qualified Fusion.Commute as Commute
import qualified Fusion.Interact as Interact
import qualified Fusion.Distribute as Distribute
import qualified Staged.Handlers as StagedHandlers
import qualified Staged.Programs as Staged
import qualified Staged.Plugin as Plugin
import qualified Internal.AlgTrans as AlgTrans
import qualified Internal.TH as TH

main :: IO ()
main = defaultMain $ testGroup "effective"
  [ State.tests
  , Reader.tests
  , Writer.tests
  , Maybe.tests
  , Except.tests
  , Nondet.tests
  , Concurrency.tests
  , Sum.tests
  , Commute.tests
  , Interact.tests
  , Distribute.tests
  , HStore.tests
  , WithName.tests
  , IO.tests
  , Yield.tests
  , AlgTrans.tests
  , StagedHandlers.tests
  , Staged.tests
  , Plugin.tests
  , TH.tests
  ]
