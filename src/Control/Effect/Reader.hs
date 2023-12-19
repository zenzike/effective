{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}

module Control.Effect.Reader where

import Control.Effects
import Control.Family.AlgScp
import Control.Handler
import Data.HFunctor
import Control.Monad.Trans.Class (lift)
import qualified Control.Monad.Trans.Reader as R

data Ask' r k where
  Ask :: (r -> k) -> Ask' r k
  deriving Functor

type Ask r = Algebraic (Ask' r)

ask :: Member (Ask r) sig => Prog sig r
ask = (Call . inj) (Algebraic (Ask return))

asks :: Member (Ask r) sig => (r -> a) -> Prog sig a
asks f = fmap f ask

data Local' r k where
  Local :: (r -> r) -> k -> Local' r k
  deriving Functor

type Local r = Scoped (Local' r)

local :: Member (Local r) sig => (r -> r) -> Prog sig a -> Prog sig a
local f p = injCall (Scoped (Local f (fmap return p)))

readerRun
  :: Monad m
  => r -> (forall x . Effs oeffs m x -> m x)
  -> (forall x . R.ReaderT r m x -> m x)
readerRun r oalg = flip R.runReaderT r

readerAlg
  :: Monad m
  => (forall x. oeff m x -> m x)
  -> (forall x.  Effs [Ask r, Local r] (R.ReaderT r m) x -> R.ReaderT r m x)
readerAlg oalg eff
  | Just (Algebraic (Ask p)) <- prj eff =
      do r <- R.ask
         return (p r)
  | Just (Scoped (Local (f :: r -> r) p)) <- prj eff =
      R.local f p
      -- do r <- R.ask
      --    lift (p (f r))

readerFwd
  :: (Monad m, HFunctor sig)
  => (forall x. sig m x -> m x)
  -> (forall x. sig (R.ReaderT r m) x -> R.ReaderT r m x)
readerFwd alg op =
  do r <- R.ask
     lift (alg (hmap (flip R.runReaderT r) op))


-- This handler can forward operations in any family
reader :: r -> Handler [Ask r, Local r] '[] '[] fam
reader r = handler (readerRun r) readerAlg readerFwd
