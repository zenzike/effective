{-# LANGUAGE DataKinds #-}
module Main where

import Prelude hiding (log, putStrLn, putStr)
import Control.Effect
import Control.Effect.IO
import Control.Effect.Writer
import Control.Effect.Concurrency
import Control.Effect.Concurrency.Action
import Control.Monad

type HS = CCSAction ()

handshake :: Member (Act HS) sig => Prog sig ()
handshake = act (Action ())

shakehand :: Member (Act HS) sig => Prog sig ()
shakehand = act (CoAction ())

resHS :: Member (Res HS) sig => Prog sig x -> Prog sig x
resHS x = res (Action ()) (res (CoAction ()) x)

prog :: Members '[Par, Act HS, Res HS, Tell String] sig => Prog sig ()
prog = resHS (par (do tell "A"; handshake; tell "C")
                  (do tell "B"; shakehand; tell "D"))

test1 :: (String, ListActs HS ())
test1 = handle (fuse resump (writer @String)) prog

test2 :: ListActs HS (String, ())
test2 = handle (fuse (writer @String) resump ) prog

test31 :: (String, ActsMb HS ())
test31 = handle (fuse (resumpWith (False : True : True : True : [])) (writer @String)) prog

test32 :: (String, ActsMb HS ())
test32 = handle (fuse (resumpWith (False : True : True : False : [])) (writer @String)) prog

test33 :: (String, ActsMb HS ())
test33 = handle (fuse (resumpWith (False : False : True : False : [])) (writer @String)) prog

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

main :: IO ()
main = return ()