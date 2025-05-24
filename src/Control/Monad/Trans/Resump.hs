{-|
Module      : Control.Monad.Trans.Resump
Description : Resumption monad transformer
License     : BSD-3-Clause
Maintainer  : Zhixuan Yang
Stability   : experimental

This module contains the definition of the resumption monad transformer, also
known as the /free monad transformer/. For every functor @s@ and monad @m@,
a computation of the monad @ResT s m@ is an interleaving of @m@-computations
and @s@-computations. The datatype @ResT s m@ has universal properties:

  1. It carries the initial algebra of the functor @μ x. m (a + s x)@. This is
  how we define @ResT s m a@ below.

  2. As a monad @ResT s m@ over @Type@ is that it is the coproduct of 
  @m@ and the @Free s@ in the category of monads, evidenced by `elimRes` below.

  3. In the Kleisli category @Kl(m)@ of the monad @m@, the object @a + s (ResT s m a)@
  carries an initial algebra for the endofunctor @F_m . (a + s -) . U_m)@, where 
  @F_m ⊣ U_m : Kl(m) -> Type@ is the Kleisli adjunction for the monad @m@. This
  is evidenced by `sresAlg` and `foldSRes` below.
  Moreover, @ResT s m a@ also carries an algebra of this functor (`resAlg` below) and
  there is a homomorphism from `resAlg` to `sresAlg`, making `resAlg` as a weak
  initial algebra.
  (In general, for every functor @s@ over @Type@, the datatype @s (μ x. m (s
  x))@, which is isomorphic to simply @μ x. s (m x)@ carries an initial algebra for 
  the functor @F_m . s . U_m : Kl(m) -> Kl(m)@ over the Kleisli category.)
-}
module Control.Monad.Trans.Resump  where

import Data.HFunctor ( HFunctor(..) )

import Control.Monad
import Data.Bifunctor ( Bifunctor(bimap) )
import Control.Monad.Trans.Class ( MonadTrans(..) )

-- | The resumption monad transformer.
newtype ResT s m a = ResT { unResT :: m (Either a (s (ResT s m a))) }

instance (Functor s, Functor m) => Functor (ResT s m) where
  fmap f (ResT m) = ResT $ fmap (bimap f (fmap (fmap f))) m

instance (Functor s, Monad m) => Applicative (ResT s m) where
  {-# INLINE pure #-}
  pure x = ResT (return (Left x))

  {-# INLINE (<*>) #-}
  (<*>) = ap

instance (Functor s, Monad m) => Monad (ResT s m) where
  ResT r >>= k = ResT $
     do x <- r
        case x of
          Left x   -> unResT (k x)
          Right sr -> return (Right (fmap (>>= k) sr))

instance Functor s => HFunctor (ResT s) where
  {-# INLINE hmap #-}
  hmap h (ResT mx) = ResT (fmap (fmap (fmap (hmap h))) (h mx))

instance Functor s => MonadTrans (ResT s) where
  lift m = ResT (fmap Left m)

-- | The algebraic operation of signature @s@ on the monad @ResT s m@.
resOp :: Monad m => s (ResT s m a) -> ResT s m a
resOp o = ResT $ return (Right o)

-- | The algebraic operation of signature @s@ on the monad @ResT s m@, without
-- a continuation after the operation.
resOp' :: (Functor s, Monad m) => s a -> ResT s m a
resOp' o = ResT $ return (Right (fmap return o))

-- | The universal property of the monad @ResT s m x@ as the coproduct of the monad
-- @m@ and the free monad over @s@.
elimRes :: Monad n
        => (forall x. m x -> n x)            -- ^ a monad morphism
        -> (forall x. s x -> n x)            -- ^ a natural transformation
        -> (forall x. ResT s m x -> n x)     -- ^ a monad morphism
elimRes l r res = 
  do e <- l (unResT res)
     case e of
       Left a  -> return a
       Right m -> do res' <- r m; elimRes l r res'

-- * Universal properties of @ResT@ in the Kleisli category
--
-- Given a functor @s@ and a monad @m@, we have an endofunctor over the Kleisli
-- category:
--
-- > (F_m . (a + s -) . U_m)  :  Kl(m) -> Kl(m)
--
-- which sends every object @x@ to @a + s (m x)@ and every arrow @f : x -> m y@
-- to @return . (either id (fmap @s ((>>=) f))) : a + (s (m x)) -> m (a + s (m y))@.
--
-- The datatype @ResT (s m a)@ carries a weak initial algebra of this functor.

-- | The algebra of @ResT s m a@ in the Kleisli category said above.
resAlg :: (Functor s, Monad m) => Either a (s (m (ResT s m a))) -> m (ResT s m a)
resAlg (Left a)  = return (return a)
resAlg (Right b) = (return . resOp . fmap (ResT . join . fmap unResT)) b

-- | The fold in the Kleisli category evidencing the weak initiality of @resAlg@.
-- The resulting morphism @ResT s m a -> m t@ is an algebra homomorphism in the Kleisli
-- category but it may not be the unique one. In particular, 
--
-- > foldRes (resAlg . Left) (resAlg . Right) :: ResT s m a -> m (ResT s m a)
--
-- is not the identity homomorphism in @Kl(m)@. To see this, we notice that 
-- the morphism above  \'forces\' the outermost layer of @m@ of the supplied
-- @ResT s m a@, while the identity homomorphism is just a 
-- @return :: ResT s m a -> m (ResT s m a)@.
foldRes :: (Functor s, Monad m) => (a -> m t) -> (s (m t) -> m t) -> (ResT s m a -> m t)
foldRes ret salg r = 
  do e <- unResT r
     case e of
       Left  x -> ret x
       Right s -> salg (fmap (foldRes ret salg) s)


-- | The carrier of the initial algebra of the functor @F_m . (a + s -) . U_m@.
-- This can be alternatively defined as 
-- > newtype SResT s m a = SResT (Either a (s (m (SResT s m a)))).
type SResT s m a = Either a (s (ResT s m a))

-- | The initial algebra carried by @SResT@.
sresAlg :: (Functor s, Monad m) 
        => Either a (s (m (SResT s m a))) -> m (SResT s m a)
sresAlg (Left a)  = return (Left a)
sresAlg (Right b) = return (Right (fmap ResT b))

-- | The inverse of the initial algebra in the Kleisli category 
sresAlgInv :: (Functor s, Monad m) 
           => SResT s m a -> m (Either a (s (m (SResT s m a))))
sresAlgInv (Left a) = return (Left a)
sresAlgInv (Right b) = return (Right (fmap unResT b))

-- | The universal property of @sresAlg@ as the initial algebra of @F_m . (a + s -) . U_m@.
foldSRes :: (Functor s, Monad m)
         => (a -> m t)             -- ^ @ret@
         -> (s (m t) -> m t)       -- ^ @salg@
         -> (SResT s m a -> m t)   -- ^ An algebra homomorphism from @sresAlg@ to @either ret salg@.
foldSRes ret salg = 
  sresAlgInv 
  >=> (return . fmap (fmap (>>= foldSRes ret salg))) 
  >=> either ret salg