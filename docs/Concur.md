```haskell
module Concur where

import Prelude hiding (log)
import Control.Effect
import Control.Effect.Concurrency

data HLAct = H | Log String | Tau deriving (Show, Eq)

instance Action HLAct where
  merge H H = Just Tau
  merge _ _ = Nothing


type Con = CResT HLAct IO 

act :: HLAct -> Con ()
act a = prefix a (return ())

handshake :: Con ()
handshake = act H

log :: String -> Con ()
log s = act (Log s)

prog :: Con ()
prog = res H (par (do log "A"; handshake; log "A") 
                  (do log "B"; handshake; log "B"))
```