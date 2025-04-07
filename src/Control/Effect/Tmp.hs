module Control.Effect.Tmp where

import Prelude hiding (log)
import Control.Concurrent
import Control.Monad.Trans.Reader
import Control.Monad.Trans.Class

type Con = ReaderT (QSem, QSem) IO

handshake :: Con ()
handshake = do (p, q) <- ask; lift (do waitQSem p; signalQSem q)

shakehand :: Con ()
shakehand = do (p, q) <- ask; lift (do signalQSem p; waitQSem q)

log :: String -> Con ()
log s = lift (putStr s)

par :: Con x -> Con y -> Con x
par l r = do (p, q) <- ask
             lift $
               do forkIO (runReaderT (fmap (const ()) r) (p, q))
                  runReaderT l (p, q)

nu :: Con x -> Con x
nu c = do p <- lift (newQSem 0)
          q <- lift (newQSem 0)
          local (\_ -> (p, q)) c

runCon :: Con x -> IO x
runCon c = do p <- newQSem 0
              q <- newQSem 0
              runReaderT c (p,q)

prog1 :: Con ()
prog1 = do par (do log "A"; handshake; log "C")
               (do log "B"; shakehand; log "D")

-- the main thread doesn't wait for other threads
test :: Con ()
test = par (return ()) (do handshake; log "A")

-- "A" and "C" may shake hand, so "AC" is a possible outcome
prog2 :: Con ()
prog2 = par (par (do handshake; log "B")
                 (do shakehand; log "C")) 
            (do handshake; log "A")

-- Only "B" and "C" can shake hand
prog3 :: Con ()
prog3 = par (nu $ par (do handshake; log "B")
                      (do shakehand; log "C")) 
            (do handshake; log "A")