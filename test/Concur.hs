module Main where

import Prelude hiding (log, putStrLn, putStr)
import Control.Effect
import Control.Effect.IO
import Control.Effect.Writer
import Control.Effect.Concurrency
import Control.Effect.Family.Algebraic
import Control.Monad
import Control.Effect.Clone
import Control.Effect.Yield

import Data.Proxy 

main :: IO ()
main = return ()

data ActNames = Handshake deriving (Show, Eq, Ord)
type HS = CCSAction ActNames

handshake :: Member (Act HS) sig => Prog sig ()
handshake = act (Action Handshake)

shakehand :: Member (Act HS) sig => Prog sig ()
shakehand = act (CoAction Handshake)

resHS :: Member (Res HS) sig => Prog sig x -> Prog sig x
resHS x = res (Action Handshake) (res (CoAction Handshake) x)

prog :: Members '[Par, Act HS, Res HS, Tell String] sig => Prog sig ()
prog = resHS (par (do tell "A"; handshake; tell "C")
                  (do tell "B"; shakehand; tell "D"))

test1 :: (String, ListActs HS ())
test1 = handle (resump |> writer @String) prog

test2 :: ListActs HS (String, ())
test2 = handle (writer @String |> resump) prog

-- ABCD
test31 :: (String, ActsMb HS ())
test31 = handle (fuse (resumpWith (False : True : True : True : [])) (writer @String)) prog

-- ABDC
test32 :: (String, ActsMb HS ())
test32 = handle (fuse (resumpWith (False : True : True : False : [])) (writer @String)) prog

-- BADC
test33 :: (String, ActsMb HS ())
test33 = handle (fuse (resumpWith (False : False : True : True : [])) (writer @String)) prog

-- BACD
test34 :: (String, ActsMb HS ())
test34 = handle (fuse (resumpWith (False : False : True : False : [])) (writer @String)) prog

prog2 :: Members '[NewQSem, SignalQSem, WaitQSem, Par, PutStr] sig => Prog sig ()
prog2 = 
  do p <- newQSem 0
     q <- newQSem 0
     par (do replicateM_ 5 (putStr "A")
             waitQSem p
             signalQSem q
             replicateM_ 5 (putStr "C")) 
         (do replicateM_ 5 (putStr "B")
             signalQSem p
             waitQSem q
             replicateM_ 5 (putStr "D")) 

test4 :: IO ()
test4 = handleIO (Proxy @IOEffects) (identity @'[]) prog2

tell' :: forall w sig. (Member (Clone (Tell w)) sig, Monoid w) => w -> Prog sig ()
tell' w = cloneAlg (Tell w ())

prog3 :: Members '[Par, Act HS, Res HS, Tell String, Clone (Tell String)] sig => Prog sig ()
prog3 = resHS (par (do tell "A"; handshake; tell' "C")
                   (do tell "B"; shakehand; tell' "D"))

-- The cloned `tell` operations are handled before `par` so they behave
-- like thread-local writers while the original `tell`s are global.
test5 :: (String, ListActs HS (String, ()))
test5 = handle (cloneHdl writer |> resump |> writer) prog3

prog4 :: Member (Alg IO) sig => Prog sig ()
prog4 = liftIO (putChar 'x') 

test6 :: IO ()
test6 = handleIO (Proxy @IOEffects) (identity @'[]) prog4

test7 :: IO (Either String ())
test7 = handleIO (Proxy @IOEffects) (ccsByQSem @ActNames |> writerIO) (prog >> putStrLn "")


prog5 :: Members '[JPar, Act HS, Res HS, Tell String] sig => Prog sig (Int, Int)
prog5 = resHS (jpar (do tell "A"; handshake; tell "C"; return 0)
                    (do tell "B"; shakehand; tell "D"; return 1))

test8 :: (String, ListActs HS (Int, Int))
test8 = handle (jresump |> writer @String) prog5

test9 :: IO (Either String (Int, Int))
test9 = handleIO (Proxy @IOEffects) (ccsByQSem @ActNames |> writerIO) prog5

prog6 :: Members '[Yield Int Int, PutStrLn] sig => Int -> Prog sig Int
prog6 n = do putStrLn ("Ping " ++ show n)
             n' <- yield (n + 1)
             prog6 n'

prog6' :: Members '[Yield Int Int, PutStrLn] sig => Int -> Prog sig Int
prog6' n
  | n > 100   = do putStrLn "Too big"; return n
  | otherwise = do putStrLn ("Pong " ++ show n)
                   n' <- yield (2 * n)
                   prog6' n'

test10 :: IO (Either Int Int)
test10 = handleIOApp (Proxy @'[PutStrLn])
           (pingpongWith (prog6' @'[Yield Int Int, MapYield Int Int, PutStrLn])) 
           (prog6 0)