{-# LANGUAGE DataKinds, MonoLocalBinds #-}
module Control.Effect.Yield where

import Control.Effect
import Control.Effect.Family.Algebraic
import Control.Monad.Trans.YRes 
import Data.HFunctor
import qualified Control.Monad.Trans.YRes as Y
#ifdef INDEXED
import GHC.TypeNats
import Data.List.Kind
#endif

type Yield a b = Alg (Yield_ a b)
data Yield_ a b x = Yield a (b -> x) deriving Functor 

{-# INLINE yield #-}
yield :: Member (Yield a b) sig => a -> Prog sig b
yield a = call' (Alg (Yield a id))

yieldAlg :: Monad m => Algebra '[Yield a b] (YResT a b m)
yieldAlg eff
  | Just (Alg (Yield a k)) <- prj eff = Y.yield a (fmap return k)

yieldAT :: AlgTransM '[Yield a b] '[] '[YResT a b]
yieldAT = AlgTrans (\_ -> yieldAlg)

pingpongWith :: forall oeffs a b y .
                ( HFunctor (Effs oeffs)
#ifdef INDEXED
                , KnownNat (Data.List.Kind.Length oeffs)
#endif
                , Forwards oeffs '[YResT b a] )
             => (a -> Prog (Yield b a ': oeffs) y)
             -> Handler '[Yield a b] oeffs '[YResT a b] '[Either y]
pingpongWith q = handler run (\_ -> yieldAlg) where
  run :: forall m . Monad m => Algebra oeffs m 
      -> (forall x. YResT a b m x -> m (Either y x))
  run oalg p = pingpong p (eval (yieldAlg # fwds @_ @'[YResT b a] oalg) . q)