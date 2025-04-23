{-# LANGUAGE DataKinds #-}

module Control.Effect.Accum where

import Control.Effect
import Control.Effect.Algebraic

import Control.Monad.Trans.Accum (AccumT)
import qualified Control.Monad.Trans.Accum as A


type Accum m a = Alg Accum
data Accum' m a = Accum m a

data For m a = For m

runAccum :: w -> Handler '[Accum, For] '[] '[AccumT w] '[((,) w)]
runAccum w = handler' _ undefined -- (runAccumT w)
