{-# LANGUAGE DataKinds #-}
module Control.Effect.Yield where

import Control.Effect
import Control.Effect.Internal.Forward
import Control.Effect.Algebraic
import Control.Monad.Trans.YRes 
import Data.HFunctor
import qualified Control.Monad.Trans.YRes as Y


type Yield a b = Alg (Yield_ a b)
data Yield_ a b x = Yield a (b -> x) deriving Functor 

{-# INLINE yield #-}
yield :: Member (Yield a b) sig => a -> Prog sig b
yield a = call' (Alg (Yield a id))

yieldAlg :: Monad m => Algebra '[Yield a b] (YResT a b m)
yieldAlg eff
  | Just (Alg (Yield a k)) <- prj eff = Y.yield a (fmap return k)


pingpongWith :: forall oeffs a b y .
                ( HFunctor (Effs oeffs)
                , ForwardEffs oeffs (YResT b a) )
             => (a -> Prog (Yield b a ': oeffs) y)
             -> Handler '[Yield a b] oeffs (YResT a b) (Either y)

pingpongWith q = Handler run (\_ -> yieldAlg) where
  run :: forall m . Monad m => Algebra oeffs m 
      -> (forall x. YResT a b m x -> m (Either y x))
  run oalg p = pingpong p (eval (yieldAlg # fwdEffs oalg) . q)