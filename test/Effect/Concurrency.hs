{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PartialTypeSignatures #-}

{-|
Module      : Effect.Concurrency
Description : Laws and examples for concurrency
License     : BSD-3-Clause
Maintainer  : Nicolas Wu
Stability   : experimental

The handlers of "Control.Effect.Concurrency" that are based on resumptions.
`resump` and `jresump` list every schedule of a program, once for each way of
reaching it, so programs are compared by their sets of schedules. The
handlers that follow a given schedule are tested to stay within that set.
A handler explores every interleaving, so the programs are kept small.
The handlers that use threads, `ccsByQSem`, `parIOAlg` and `jparIOAlg`,
are tested by examples, with their output in a `Log`. The staged forms of
the handlers here are only compiled, in "Staged.Handlers".
-}
module Effect.Concurrency
  ( tests, genConcur, genJConcur
    -- * Programs shared with the staged handlers
  , IOPar, ActNames (..), HR, bohem, handshake, shakehand, resHS
  ) where

import Control.Effect
import Control.Effect.Concurrency
import Control.Effect.Concurrency.Operations
  (Act, Par, JPar, Res, CCSAction (..), act, par, jpar, res)
import Control.Effect.IO
import Control.Effect.Reader
import Control.Effect.Writer
import Control.Effect.WithName
import Control.Monad (replicateM_)

import qualified Control.Concurrent.QSem as QSem
import Data.List (isInfixOf, sort)
import qualified Data.Set as Set
import Data.Tuple (swap)

import Hedgehog
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import Test.Tasty
import Test.Tasty.HUnit (testCase, assertBool, (@?=))

import Effect.IO (Log, say, writerLog, withLog)
import Law
import Gen

-- | Actions on one of two channels, named by a `Bool`, for the laws.
type B = CCSAction Bool

tests :: TestTree
tests = testGroup "Concurrency"
  [ testGroup "resump"
    [ law "par m n  =  par n m, when both return 0" $ do
        m <- small 6 genConcur
        n <- small 6 genConcur
        schedules (par (0 <$ m) (0 <$ n)) === schedules (par (0 <$ n) (0 <$ m))
    , law "par (par m n) o  =  par m (par n o), when all return 0" $ do
        m <- small 4 genConcur
        n <- small 4 genConcur
        o <- small 4 genConcur
        schedules (par (par (0 <$ m) (0 <$ n)) (0 <$ o))
          === schedules (par (0 <$ m) (par (0 <$ n) (0 <$ o)))
    , law "par m (return y)  =  m" $ do
        m <- small 6 genConcur
        y <- forAll genInt
        schedules (par m (return y)) === schedules m
    , law "par (return x) m  =  x <$ m" $ do
        m <- small 6 genConcur
        x <- forAll genInt
        schedules (par (return x) m) === schedules (x <$ m)
    , testCase "an action is visible" $
        schedules (0 <$ act (Action True)) @?= Set.fromList [([Action True], 0)]
    , testCase "an action and its coaction synchronise under res" $
        schedules (res (Action True) (par (0 <$ act (Action True)) (0 <$ act (CoAction True))))
          @?= Set.fromList [([Silent True], 0)]
    , testCase "an action alone is blocked under res" $
        schedules (res (Action True) (0 <$ act (Action True))) @?= Set.empty
    ]

  , testGroup "jresump"
    [ law "jpar m n  =  swap <$> jpar n m" $ do
        m <- small 6 genJConcur
        n <- small 6 genJConcur
        jschedules (jpar m n) === jschedules (swap <$> jpar n m)
    , law "jpar m (return y)  =  (\\x -> (x, y)) <$> m" $ do
        m <- small 6 genJConcur
        y <- forAll genInt
        jschedules (jpar m (return y)) === jschedules ((\x -> (x, y)) <$> m)
    , testCase "an action and its coaction synchronise under res" $
        jschedules (res (Action True) (jpar (1 <$ act (Action True)) (2 <$ act (CoAction True))))
          @?= Set.fromList [([Silent True], (1, 2 :: Int))]
    ]

    -- A handler that follows a schedule finds one of the schedules of the
    -- handler that lists them all, or else is blocked.
  , testGroup "following a schedule"
    [ law "resumpWith" $ do
        m  <- small 8 genConcur
        bs <- forAllWith (show . take 40) choices
        follows (schedules m) (unActsMb (handle (resumpWith @B bs) m))
    , law "resumpWithM" $ do
        m <- small 8 genConcur
        b <- forAll Gen.bool
        unActsMb (handle (resumpWithM @'[] @B (return b)) m)
          === unActsMb (handle (resumpWith @B (repeat b)) m)
    , law "jresumpWith" $ do
        m  <- small 8 genJConcur
        bs <- forAllWith (show . take 40) choices
        follows (jschedules m) (unActsMb (handle (jresumpWith @B bs) m))
    ]
  , examples
  ]
  where
    small n g = forAllWith (const "<program>") (Gen.resize n (genProg g))

    -- `resumpWith` and `jresumpWith` fail with a pattern match error when
    -- their list of choices runs out, so the schedules here are infinite.
    choices = cycle <$> Gen.list (Range.linear 1 40) Gen.bool

    follows all (trace, Just x)  = assert (Set.member (trace, x) all)
    follows _   (_,     Nothing) = success

-- | Examples of the handlers by resumptions, and of those by threads.
-- `parIOAlg` forks a thread and does not wait for it, so only the output of
-- the main thread, and what must precede it, is certain to be in the log.
examples :: TestTree
examples = testGroup "examples"
  [ testGroup "resumptions"
    [ testCase "a global writer sees every schedule" $ do
        let (out, acts) = test1
        out @?= "ABDAADADABCDDCCDBADCCDDC"
        map fst (unListActs acts) @?= replicate 4 [Silent Handshake]
    , testCase "a local writer sees its own thread" $
        unListActs test2 @?= replicate 4 ([Silent Handshake], ("AC", ()))
    , testCase "a named writer below par is local" $ do
        let (out, acts) = test5
        out @?= "ABAAAABBA"
        unListActs acts @?= replicate 4 ([Silent Handshake], ("C", ()))
    , testCase "jpar returns both results" $ do
        let (out, acts) = test8
        out @?= fst test1
        unListActs acts @?= replicate 4 ([Silent Handshake], (0, 1))
    , testCase "resumpWith follows the given schedule" $
        [ (out, unActsMb acts) | (out, acts) <- [test31, test32, test33, test34] ]
          @?= [ (out, ([Silent Handshake], Just ())) | out <- ["ABCD", "ABDC", "BADC", "BACD"] ]
    ]
  , testGroup "threads"
    [ testCase "par synchronised by semaphores" $ do
        ((), out) <- withLog test4
        sort (takeWhile (`notElem` "CD") out) @?= "AAAAABBBBB"
        filter (== 'C') out @?= "CCCCC"
    , testCase "par synchronised by ccsByQSem" $ do
        (r, out) <- withLog test7
        r @?= Right ()
        sort (takeWhile (`notElem` "CD") out) @?= "AB"
        assertBool "the main thread finished" ('C' `elem` out)
    , testCase "jpar synchronised by ccsByQSem" $ do
        (r, out) <- withLog test9
        r @?= Right (0, 1)
        (sort (take 2 out), sort (drop 2 out)) @?= ("AB", "CD")
    , testCase "bohem" $ do
        (r, out) <- withLog intro1
        r @?= Right ()
        assertBool out ("I am just a poor boy" `isInfixOf` out)
    , testCase "bohem, with a lock on tell" $ do
        (r, out) <- withLog intro2
        r @?= Right ()
        assertBool out ("I am just a poor boy" `isInfixOf` out)
    , testCase "bohem, with thread identifiers" $ do
        (r, out) <- withLog intro3
        r @?= Right ()
        assertBool out ("LL: I am just a poor boy. " `isInfixOf` out)
    ]
  ]

-- | The set of schedules of a program: its traces, each with its result.
schedules :: Ord a => Prog '[Act B, Par, Res B] a -> Set.Set ([B], a)
schedules = Set.fromList . unListActs . handle resump

jschedules :: Ord a => Prog '[Act B, JPar, Res B] a -> Set.Set ([B], a)
jschedules = Set.fromList . unListActs . handle jresump

-- | Actions and coactions on two channels, parallel composition, and the
-- restriction of a channel. A handler may explore every interleaving of the
-- branches of @par@, so these are kept small.
genConcur :: Members '[Act (CCSAction Bool), Par, Res (CCSAction Bool)] effs
          => GenProg effs
genConcur = genAlg [\x -> x <$ act (action x)] <> GenProg (\sub ->
  [ Gen.subterm2 (tiny sub) (tiny sub) (\p q env -> par (p env) (q env))
  , Gen.subtermM sub (\p -> (\b -> res (Action b) . p) <$> Gen.bool) ])
  where
    tiny = Gen.scale (`div` 4)

-- | As `genConcur`, with the parallel composition that returns both results.
genJConcur :: Members '[Act (CCSAction Bool), JPar, Res (CCSAction Bool)] effs
           => GenProg effs
genJConcur = genAlg [\x -> x <$ act (action x)] <> GenProg (\sub ->
  [ Gen.subterm2 (tiny sub) (tiny sub) (\p q env -> uncurry (+) <$> jpar (p env) (q env))
  , Gen.subtermM sub (\p -> (\b -> res (Action b) . p) <$> Gen.bool) ])
  where
    tiny = Gen.scale (`div` 4)

-- | An action or a coaction on one of two channels.
action :: Int -> CCSAction Bool
action x = (if even x then Action else CoAction) (x `mod` 4 < 2)

-- The programs of the examples, and of their staged forms.

type IOPar = '[Alg IO, Par, JPar]

ioPar :: Algebra IOPar IO
ioPar = ioAlg # parIOAlg # jparIOAlg

data ActNames = Handshake | Raisehand deriving (Show, Eq, Ord)

-- | Actions on the channels of `ActNames`, for the examples.
type HR = CCSAction ActNames

bohem :: () ! [Act HR, Res HR, Par, Tell String]
bohem = par (resHS $ par (do tell "I am just a poor boy"; handshake)
                         (do shakehand; tell "I need no sympathy"))
            (tell "Oh poor boy")

handshake :: Member (Act HR) effs => Prog effs ()
handshake = act (Action Handshake)

shakehand :: Member (Act HR) effs => Prog effs ()
shakehand = act (CoAction Handshake)

resHS :: Member (Res HR) effs => Prog effs x -> Prog effs x
resHS x = res (Action Handshake) x

prog :: Members '[Par, Act HR, Res HR, Tell String] effs => Prog effs ()
prog = resHS (par (do tell "A"; handshake; tell "C")
                  (do tell "B"; shakehand; tell "D"))

test1 :: (String, ListActs HR ())
test1 = handle (resump |> writer @String) prog

test2 :: ListActs HR (String, ())
test2 = handle (writer @String |> resump) prog

-- ABCD
test31 :: (String, ActsMb HR ())
test31 = handle (fuse (resumpWith (False : True : True : True : [])) (writer @String)) prog

-- ABDC
test32 :: (String, ActsMb HR ())
test32 = handle (fuse (resumpWith (False : True : True : False : [])) (writer @String)) prog

-- BADC
test33 :: (String, ActsMb HR ())
test33 = handle (fuse (resumpWith (False : False : True : True : [])) (writer @String)) prog

-- BACD
test34 :: (String, ActsMb HR ())
test34 = handle (fuse (resumpWith (False : False : True : False : [])) (writer @String)) prog

prog2 :: Members '[Par, Alg IO] effs => Log -> Prog effs ()
prog2 out =
  do p <- io (QSem.newQSem 0)
     q <- io (QSem.newQSem 0)
     par (do replicateM_ 5 (say out "A")
             io (QSem.waitQSem p)
             io (QSem.signalQSem q)
             replicateM_ 5 (say out "C"))
         (do replicateM_ 5 (say out "B")
             io (QSem.signalQSem p)
             io (QSem.waitQSem q)
             replicateM_ 5 (say out "D"))

test4 :: Log -> IO ()
test4 out = handleIO' (Proxy @IOPar) ioPar (identity @'[]) (prog2 out)

tell' :: forall w effs. (Member ("t2" :@ (Tell w)) effs) => w -> Prog effs ()
tell' w = callPAlg (Proxy @"t2") (Tell_ w ())

prog3 :: Members '[Par, Act HR, Res HR, Tell String, "t2" :@ (Tell String)] effs => Prog effs ()
prog3 = resHS (par (do tell "A"; handshake; tell' "C")
                   (do tell "B"; shakehand; tell' "D"))

-- The cloned `tell` operations are handled before `par` so they behave
-- like thread-local writers while the original `tell`s are global.
test5 :: (String, ListActs HR (String, ()))
test5 = handle (renameEffs (Proxy @"t2") writer |> resump |> writer) prog3

test7 :: Log -> IO (Either String ())
test7 out = handleIO' (Proxy @IOPar) ioPar (ccsByQSem @ActNames |> writerLog out) prog

prog5 :: Members '[JPar, Act HR, Res HR, Tell String] effs => Prog effs (Int, Int)
prog5 = resHS (jpar (do tell "A"; handshake; tell "C"; return 0)
                    (do tell "B"; shakehand; tell "D"; return 1))

test8 :: (String, ListActs HR (Int, Int))
test8 = handle (jresump |> writer @String) prog5

test9 :: Log -> IO (Either String (Int, Int))
test9 out = handleIO' (Proxy @IOPar) ioPar (ccsByQSem @ActNames |> writerLog out) prog5

-- ((threadId >> printWithId) \\ reader)  >> (ccsByQSem \\ State SemMap)

-- Give a local thread ID to every process
threadId :: Handler '[Par] '[Par, Local String] '[] a a
threadId = interpretM1 $ \alg (Par a b) ->
  parM alg (localM alg (++ "L") a) (localM alg (++ "R") b)
-- Prepend every output operation with a thread ID
tellWithId :: Handler '[Tell String] '[Tell String, Ask String] '[] a a
tellWithId= interpret1 $ \(Tell s k) ->
  do id <- ask
     tell (id ++ ": " ++ s ++ ". ")
     return k

tellWithLock :: Handler '[Tell String] '[Tell String, Act HR, Par, Res HR] '[] a a
tellWithLock = Handler
  (Runner $ \oalg p ->
    let daemon =
          do callM oalg (Act (CoAction Raisehand) ())
             callM oalg (Act (Action Raisehand) ())
             daemon
    in do resM oalg (Action Raisehand) $
            parM oalg p daemon)
  (algTrans1 $ \oalg (Tell s k) ->
    do actM oalg (Action Raisehand)
       tellM oalg s
       actM oalg (CoAction Raisehand)
       return k)

-- Processes can tell strings and their output is tagged with their ID
ccsWithTell :: Log
            -> Handler [Par, Tell String, Act HR, Res HR]
                 [Par, Alg IO]
                 _
                 a
                 (Either String a)
ccsWithTell out =
  ((threadId |> tellWithId) \\ reader "")
    |> tellWithLock
    |> ccsByQSem @ActNames
    |> writerLog out

intro1 :: Log -> IO (Either String ())
intro1 out = handleIO' (Proxy @'[Par]) ioPar (ccsByQSem @ActNames |> writerLog out) bohem

intro2 :: Log -> IO (Either String ())
intro2 out = handleIO' (Proxy @'[Par]) ioPar (tellWithLock |> ccsByQSem @ActNames |> writerLog out) bohem

intro3 :: Log -> IO (Either String ())
intro3 out = handleIO' (Proxy @'[Par]) ioPar (ccsWithTell out) bohem
