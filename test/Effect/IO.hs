{-|
Module      : Effect.IO
Description : Running programs in IO, and a log for their output
License     : BSD-3-Clause
Maintainer  : Nicolas Wu, Zhixuan Yang
Stability   : experimental

Tests of handlers that run in @IO@ write to a `Log` rather than to @stdout@,
so that the order of their output can be inspected. `writerLog` handles
`Tell` by writing to the log, as `writerIO` does to @stdout@.
-}
module Effect.IO (tests, Log, say, writerLog, withLog) where

import Control.Effect
import Control.Effect.IO
import Control.Effect.Writer

import Data.IORef

import Test.Tasty
import Test.Tasty.HUnit

tests :: TestTree
tests = testGroup "IO"
  [ testCase "handleIO" $ do
      ((), out) <- withLog (\log -> handleIO (identity @'[]) (say log "x"))
      out @?= "x"
  ]

-- | The output of concurrent programs is collected in a log, so that tests
-- can inspect the order in which it was produced.
type Log = IORef String

say :: Member (Alg IO) effs => Log -> String -> Prog effs ()
say ref s = io (atomicModifyIORef' ref (\l -> (l ++ s, ())))

-- | A variant of `writerIO` that writes to a log rather than to @stdout@.
writerLog :: Log -> Handler '[Tell String] '[Alg IO] '[] a a
writerLog ref = interpret1 $ \(Tell s k) -> do say ref s; return k

withLog :: (Log -> IO a) -> IO (a, String)
withLog run = do
  ref <- newIORef ""
  x   <- run ref
  out <- readIORef ref
  return (x, out)
