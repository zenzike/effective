{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}

module Control.Effect.Reader where

import Data.Functor.Composes
import Control.Effect
-- import Control.Monad.Trans.Class (lift)
import qualified Control.Monad.Trans.Reader as R

data Ask r k where
  Ask :: (r -> k) -> Ask r k
  deriving Functor

ask :: Member (Ask r) sig => Prog sig r
ask = (Call . inj) (Alg (Ask return))

asks :: Member (Ask r) sig => (r -> a) -> Prog sig a
asks f = fmap f ask

data Local r k where
  Local :: (r -> r) -> k -> Local r k
  deriving Functor

local :: Member (Local r) sig => (r -> r) -> Prog sig a -> Prog sig a
local f p = injCall (Scp (Local f (fmap return p)))

reader :: r -> Handler [Ask r, Local r] '[] '[]
reader r = Handler $ Handler' (readerRun r)
                              readerAlg
                              readerFwd

readerRun
  :: Monad m
  => r -> (forall x . Effs oeffs m x -> m x)
  -> (forall x . R.ReaderT r m x -> m (Comps '[] x))
readerRun r oalg = fmap CNil . flip R.runReaderT r

readerAlg
  :: Monad m
  => (forall x. oeff m x -> m x)
  -> (forall x.  Effs [Ask r, Local r] (R.ReaderT r m) x -> R.ReaderT r m x)
readerAlg oalg eff
  | Just (Alg (Ask p)) <- prj eff =
      do r <- R.ask
         return (p r)
  | Just (Scp (Local (f :: r -> r) (p))) <- prj eff =
      R.local f p
      -- do r <- R.ask
      --    lift (p (f r))
      -- TODO: This correspondence is interesting. What does it teach us?

readerFwd
  :: Monad m
  => (forall x. Effs sig m x -> m x)
  -> (forall x. Effs sig (R.ReaderT r m) x -> R.ReaderT r m x)
readerFwd xalg = undefined

