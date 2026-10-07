{-# LANGUAGE DataKinds #-}

{-|
Module      : Fusion.Commute
Description : Whether the operations of fused handlers commute
License     : BSD-3-Clause
Maintainer  : Nicolas Wu
Stability   : experimental

Whether the operations of two effects commute depends on the order in which
their handlers are fused. When they do, the fusion is a handler for the
commutative tensor of the two theories.
-}
module Fusion.Commute (tests) where

import Control.Effect
import Control.Effect.State
import Control.Effect.Reader
import Control.Effect.Writer
import Control.Effect.Maybe
import Control.Effect.Nondet
import qualified Control.Effect.Nondet.List as List
import Control.Effect.Nondet.Cut (cutList, onceNondet)
import qualified Control.Effect.Except as E
import Control.Effect.Concurrency
import Control.Effect.WithName

import Test.Tasty
import Test.Tasty.HUnit

import Effect.State (genState)
import Effect.Reader (genReader)
import Effect.Writer (genWriter)
import Effect.Maybe (genExcept)
import qualified Effect.Except as Except
import Effect.Nondet (genNondet, genOnce)
import Effect.Concurrency (genConcur)
import Law
import Gen

tests :: TestTree
tests = testGroup "Commute"
--  reader        writer        state        except        nondet        concur
  [ readerReader, readerWriter, readerState, readerExcept, readerNondet, readerConcur
  ,               writerWriter, writerState, writerExcept, writerNondet, writerConcur
  ,                             stateState,  stateExcept,  stateNondet,  stateConcur
  ,                                          exceptExcept, exceptNondet, exceptConcur
  ,                                                        nondetNondet, nondetConcur
  ,                                                                      concurConcur
  ]

--    row |> col | reader  writer  state   except  nondet  concur
--    -----------+-----------------------------------------------
--    reader     | yes     yes     yes     yes     yes     yes
--    writer     | yes     yes     yes     yes     yes     yes
--    state      | yes     yes     yes     yes     yes     yes
--    except     | yes     no      no      no      no      no
--    nondet     | yes     no      no      -       -       -
--    concur     | yes     no      no      -       -       -

readerReader :: TestTree
readerReader = testGroup "reader/reader"
  [ law "reader a |> reader b" $
      commute (named (Proxy @"a")) (named (Proxy @"b"))
        (\r -> handle (renameEffs (Proxy @"a") (reader r)
                    |> renameEffs (Proxy @"b") (reader (r + 1))))
  ]
  where
    named :: forall n effs. Member (n :@ Ask Int) effs => Proxy n -> GenProg effs
    named n = genAlg [const (askP n)]

readerWriter :: TestTree
readerWriter = testGroup "reader/writer"
  [ law "reader |> writer" $
      commute genReader genWriter (\r -> handle (reader r |> writer @[Int]))
  , law "writer |> reader" $
      commute genWriter genReader (\r -> handle (writer @[Int] |> reader r))
  ]

readerState :: TestTree
readerState = testGroup "reader/state"
  [ law "reader |> state" $
      commute genReader genState (\s -> handle (reader s |> state s))
  , law "state |> reader" $
      commute genState genReader (\s -> handle (state s |> reader s))
  ]

readerExcept :: TestTree
readerExcept = testGroup "reader/exceptions"
  [ law "reader |> except" $
      commute genReader genExcept (\r -> handle (reader r |> except))
  , law "except |> reader" $
      commute genExcept genReader (\r -> handle (except |> reader r))
  ]

readerNondet :: TestTree
readerNondet = testGroup "reader/nondeterminism"
  [ law "reader |> list" $
      commute genReader genNondet (\r -> handle (reader r |> list))
  , law "list |> reader" $
      commute genNondet genReader (\r -> handle (list |> reader r))
  ]

readerConcur :: TestTree
readerConcur = testGroup "reader/concurrency"
  [ law "reader |> resump" $
      commute genReader genConcur
        (\r -> unListActs . handle (reader r |> resump @(CCSAction Bool)))
  , law "resump |> reader" $
      commute genConcur genReader
        (\r -> unListActs . handle (resump @(CCSAction Bool) |> reader r))
  ]

writerWriter :: TestTree
writerWriter = testGroup "writer/writer"
  [ law "writer a |> writer b" $
      commute (named (Proxy @"a")) (named (Proxy @"b"))
        (\_ -> handle (renameEffs (Proxy @"a") (writer @[Int])
                    |> renameEffs (Proxy @"b") (writer @[Int])))
  ]
  where
    named :: forall n effs. Member (n :@ Tell [Int]) effs => Proxy n -> GenProg effs
    named n = genAlg [\x -> x <$ tellP n [x]]

writerState :: TestTree
writerState = testGroup "writer/state"
  [ law "writer |> state" $
      commute genWriter genState (\s -> handle (writer @[Int] |> state s))
  , law "state |> writer" $
      commute genState genWriter (\s -> handle (state s |> writer @[Int]))
  ]

writerExcept :: TestTree
writerExcept = testGroup "writer/exceptions"
  [ law "writer |> except" $
      commute genWriter genExcept (\_ -> handle (writer @[Int] |> except))

  , testCase "except |> writer:  throw and tell do not commute" $ do
      let run = handle (except |> writer @[Int])
      run (throw >> tell [1 :: Int] >> return ()) @?= ([], Nothing)
      run (tell [1 :: Int] >> throw >> return ()) @?= ([1], Nothing)
  ]

writerNondet :: TestTree
writerNondet = testGroup "writer/nondeterminism"
  [ law "writer |> list" $
      commute genWriter genNondet (\_ -> handle (writer @[Int] |> list))

  , testCase "list |> writer:  coin and tell do not commute" $ do
      let run = handle (list |> writer @[Int])
      run (coin >> tell [1 :: Int]) @?= ([1, 1], [(), ()])
      run (tell [1 :: Int] >> coin >> return ()) @?= ([1], [(), ()])
  ]

writerConcur :: TestTree
writerConcur = testGroup "writer/concurrency"
  [ law "writer |> resump" $
      commute genWriter genConcur
        (\_ -> unListActs . handle (writer @[Int] |> resump @(CCSAction Bool)))

  , testCase "resump |> writer:  par and tell do not commute" $ do
      let run = fmap unListActs . handle (resump @(CCSAction Bool) |> writer @[Int])
      run (fork >> tell [1 :: Int]) @?= ([1, 1], [([], ()), ([], ())])
      run (tell [1 :: Int] >> fork) @?= ([1], [([], ()), ([], ())])
  ]

stateState :: TestTree
stateState = testGroup "state/state"
  [ law "state a |> state b" $
      commute (named (Proxy @"a")) (named (Proxy @"b"))
        (\s -> handle (renameEffs (Proxy @"a") (state s)
                    |> renameEffs (Proxy @"b") (state (s + 1))))
  ]
  where
    named :: forall n effs. Members '[n :@ Get Int, n :@ Put Int] effs
          => Proxy n -> GenProg effs
    named n = genAlg [const (getP n), \s -> s <$ putP n s]

stateExcept :: TestTree
stateExcept = testGroup "state/exceptions"
  [ law "state |> except" $
      commute genState genExcept (\s -> handle (state s |> except))
  , law "state |> Except.except" $
      commute genState Except.genExcept (\s -> handle (state s |> E.except @Int))

  , testCase "except |> state:  throw and put do not commute" $ do
      let run = handle (except |> state (0 :: Int))
      run (throw >> put (1 :: Int) >> return ()) @?= (Nothing, 0)
      run (put (1 :: Int) >> throw >> return ()) @?= (Nothing, 1)
  ]

stateNondet :: TestTree
stateNondet = testGroup "state/nondeterminism"
  [ law "state |> list" $
      commute genState genNondet (\s -> handle (state s |> list))
  , law "state |> logic" $
      commute genState genNondet (\s -> handle (state s |> logic))
  , law "state |> List.backtrack" $
      commute genState (genNondet <> genOnce)
        (\s -> handle (state s |> List.backtrack))
  , law "state |> cutList" $
      commute genState genNondet (\s -> handle (state s |> cutList))
  , law "state |> onceNondet" $
      commute genState (genNondet <> genOnce)
        (\s -> handle (state s |> onceNondet))

  , testCase "list |> state:  coin and put do not commute" $ do
      let run = handle (list |> state (0 :: Int))
      run (coin >> put (5 :: Int) >> next) @?= ([5, 5], 6)
      run (put (5 :: Int) >> coin >> next) @?= ([5, 6], 7)
  ]

stateConcur :: TestTree
stateConcur = testGroup "state/concurrency"
  [ law "state |> resump" $
      commute genState genConcur
        (\s -> unListActs . handle (state s |> resump @(CCSAction Bool)))

  , testCase "resump |> state:  par and put do not commute" $ do
      let run = (\(l, t) -> (unListActs l, t))
              . handle (resump @(CCSAction Bool) |> state (0 :: Int))
      run (fork >> put (5 :: Int) >> next) @?= ([([], 5), ([], 5)], 6)
      run (put (5 :: Int) >> fork >> next) @?= ([([], 5), ([], 6)], 7)
  ]

exceptExcept :: TestTree
exceptExcept = testGroup "exceptions/exceptions"
  [ testCase "except a |> except b:  throw a and throw b do not commute" $ do
      let run = handle (renameEffs (Proxy @"a") except
                     |> renameEffs (Proxy @"b") except)
      run (throwP (Proxy @"a") >> throwP (Proxy @"b") >> return ()) @?= Just Nothing
      run (throwP (Proxy @"b") >> throwP (Proxy @"a") >> return ()) @?= Nothing
  ]

exceptNondet :: TestTree
exceptNondet = testGroup "exceptions/nondeterminism"
  [ testCase "except |> list:  throw and coin do not commute" $ do
      let run = handle (except |> list)
      run (throw >> coin >> return ()) @?= [Nothing]
      run (coin >> throw >> return ()) @?= [Nothing, Nothing]
  ]

exceptConcur :: TestTree
exceptConcur = testGroup "exceptions/concurrency"
  [ testCase "except |> resump:  throw and par do not commute" $ do
      let run = unListActs . handle (except |> resump @(CCSAction Bool))
      run (throw >> fork) @?= [([], Nothing)]
      run (fork >> throw >> return ()) @?= [([], Nothing), ([], Nothing)]

    -- resump |> except: there is no such fusion. Resumptions forward only
    -- scoped operations with one scope, and @catch@ has two.
  ]

-- There is no fusion: lists forward only scoped operations with one scope,
-- and @\<|>@ has two.
nondetNondet :: TestTree
nondetNondet = testGroup "nondeterminism/nondeterminism" []

-- There is no fusion in either order. Lists and resumptions forward only
-- scoped operations with one scope, and @par@ and @\<|>@ have two.
nondetConcur :: TestTree
nondetConcur = testGroup "nondeterminism/concurrency" []

-- There is no fusion, for the same reason.
concurConcur :: TestTree
concurConcur = testGroup "concurrency/concurrency" []

fork :: Member Par effs => Prog effs ()
fork = par (return ()) (return ())

coin :: Members '[Empty, Choose] effs => Prog effs Bool
coin = return True <|> return False

-- | Returns the state and increments it.
next :: Members '[Get Int, Put Int] effs => Prog effs Int
next = get >>= \x -> x <$ put (x + 1)
