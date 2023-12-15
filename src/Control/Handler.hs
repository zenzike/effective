{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE IncoherentInstances #-}

module Control.Handler where

import Control.Effects
import Control.Family.Base
import Data.List.Kind
import Data.Functor.Identity
import Data.Functor.Composes
import Data.HFunctor
import Data.HFunctor.HCompose
import Control.Monad.Trans.Identity
import Control.Monad.Trans.Cont
import Control.Monad ( join, ap, liftM )
import Control.Monad.Trans.Class

type Handler
  :: [Effect]                             -- effs  : input effects
  -> [Effect]                             -- oeffs : output effects
  -> [Type -> Type]                       -- f     : carrier type
  -> Family                               -- fam   : forwarding family
  -> Type
data Handler effs oeffs fs fam
  =  forall t . (HFunctor t, MonadTrans t)
  => Handler (Handler' effs oeffs t fs fam)

type Handler'
  :: [Effect]                             -- effs  : input effects
  -> [Effect]                             -- oeffs : output effects
  -> ((Type -> Type) -> (Type -> Type))   -- t     : monad transformer
  -> [Type -> Type]                       -- f     : carrier type
  -> Family                               -- fam   : forwarding family
  -> Type
data Handler' effs oeffs t fs fam =
  Handler'
  { hrun :: forall m . Monad m
         => (forall x . Effs oeffs m x -> m x)
         -> (forall x . t m x -> m (Comps fs x))

  , halg :: forall m . Monad m
         => (forall x . Effs oeffs m x -> m x)
         -> (forall x . Effs effs (t m) x -> t m x)

  , hfwd :: forall m (sig :: Effect)
         . ( Monad m, fam sig , HFunctor sig )
         => (forall x . sig m x -> m x)
         -> (forall x . sig (t m) x -> t m x)
  }


handler
  :: (MonadTrans t, HFunctor t, Functor f)
  => (forall m a . Monad m => t m a -> m (f a))
  -> (forall m . Monad m
    => (forall x . Effs oeffs m x -> m x)
    -> (forall x . Effs effs (t m) x -> t m x))
  -> (forall m sigs . ( Monad m, fam sigs )
    => (forall x . sigs m x -> m x)
    -> (forall x . sigs (t m) x -> t m x))
  -> Handler effs oeffs '[f] fam
handler run malg mfwd = Handler (Handler' (const (fmap comps . run)) malg mfwd)


-- TODO: A better error message for unsafePrj
interpret
  :: forall eff effs oeffs fam
  .  Member eff effs
  => (forall m x . eff m x -> Prog oeffs x)
  -> Handler effs oeffs '[] fam
interpret f = interpret' (\oalg -> eval oalg . f . unsafePrj)
  where
    unsafePrj :: Effs effs m x -> eff m x
    unsafePrj x = case prj x of Just y -> y

interpret'
  :: (forall m . Monad m
     => (forall x . Effs oeffs m x -> m x)
     -> (forall x . Effs effs m x -> m x))
  -> Handler effs oeffs '[] fam
interpret' alg
  = Handler $ Handler'
      (const (\(IdentityT mx) -> fmap CNil mx))
      (\oalg -> IdentityT . alg oalg . hmap runIdentityT)
      (\alg  -> IdentityT . alg . hmap runIdentityT)

fuse :: forall effs1 effs2 oeffs1 oeffs2 fs1 fs2 effs oeffs fam .
  ( All Functor fs1, All Functor fs2, All Functor (fs2 :++ fs1)
  , Expose fs2
  , Append effs1 (effs2 :\\ effs1)
  , Append (oeffs1 :\\ effs2) (oeffs2 :\\ (oeffs1 :\\ effs2))
  , Append (oeffs1 :\\ effs2) effs2
  , Append (oeffs1 :\\ effs2) oeffs2
  , Injects (oeffs1 :\\ effs2) oeffs, Injects oeffs2 oeffs
  , Injects oeffs1 ((oeffs1 :\\ effs2) :++ effs2)
  , Injects (effs2 :\\ effs1) effs2
  , effs  ~ effs1 `Union` effs2
  , oeffs ~ (oeffs1 :\\ effs2) `Union` oeffs2 
  , fam (Effs (oeffs1 :\\ effs2))
  , fam (Effs effs2))
  => Handler effs1 oeffs1 fs1 fam
  -> Handler effs2 oeffs2 fs2 fam
  -> Handler (effs1 `Union` effs2) ((oeffs1 :\\ effs2) `Union` oeffs2 ) (fs2 :++ fs1) fam
fuse (Handler h1) (Handler h2) = Handler (fuse' h1 h2)

fuse' :: forall effs1 effs2 oeffs1 oeffs2 t1 t2 fs1 fs2 effs oeffs fam .
  ( All Functor (fs2 :++ fs1)
  , MonadTrans t1
  , MonadTrans t2
  , HFunctor t1
  , HFunctor t2
  , Expose fs2
  , Append effs1 (effs2 :\\ effs1)
  , Append (oeffs1 :\\ effs2) (oeffs2 :\\ (oeffs1 :\\ effs2))
  , Append (oeffs1 :\\ effs2) effs2
  , Append (oeffs1 :\\ effs2) oeffs2
  , Injects (oeffs1 :\\ effs2) oeffs, Injects oeffs2 oeffs
  , Injects oeffs1 ((oeffs1 :\\ effs2) :++ effs2)
  , Injects (effs2 :\\ effs1) effs2
  , effs  ~ effs1 `Union` effs2
  , oeffs ~ (oeffs1 :\\ effs2) `Union` oeffs2 
  , fam (Effs (oeffs1 :\\ effs2))
  , fam (Effs effs2))
  => Handler' effs1 oeffs1 t1 fs1 fam
  -> Handler' effs2 oeffs2 t2 fs2 fam
  -> Handler' effs oeffs (HCompose t1 t2) (fs2 :++ fs1) fam
fuse' (Handler' run1 malg1 mfwd1) (Handler' run2 malg2 mfwd2) =
  Handler' run malg mfwd where
    run :: forall m . Monad m
        => (forall x. Effs oeffs m x -> m x)
        -> (forall x. HCompose t1 t2 m x -> m (Comps (fs2 :++ fs1) x))
    run oalg
      = fmap (unexpose @fs2 @fs1)
      . run2 (oalg . injs)
      . run1 (weakenAlg $ heither @(oeffs1 :\\ effs2) @(effs2)
          (mfwd2 (weakenAlg oalg))
          (malg2 (weakenAlg oalg)))
      . getHCompose

    malg :: forall m . Monad m
      => (forall x . Effs oeffs m x -> m x)
      -> (forall x. Effs effs (HCompose t1 t2 m) x -> HCompose t1 t2 m x)
    malg oalg
      = HCompose
      . hunion @effs1 @effs2
          (malg1 (weakenAlg $ heither @(oeffs1 :\\ effs2) @effs2
                                (mfwd2 (weakenAlg oalg))
                                (malg2 (weakenAlg oalg))))
          (mfwd1 (malg2 (oalg . injs)))
      . hmap getHCompose

    mfwd
      :: forall m sig . ( Monad m , fam sig, HFunctor sig )
      => (forall x. sig m x -> m x)
      -> forall x. sig (HCompose t1 t2 m) x -> HCompose t1 t2 m x
    mfwd alg
      = HCompose
      . mfwd1 (mfwd2 alg)
      . hmap getHCompose

(<&>) :: forall effs1 effs2 oeffs1 oeffs2 fs1 fs2 effs oeffs fam .
  ( All Functor fs1, All Functor fs2, All Functor (fs2 :++ fs1)
  , Expose fs2
  , Append effs1 (effs2 :\\ effs1)
  , Append (oeffs1 :\\ effs2) (oeffs2 :\\ (oeffs1 :\\ effs2))
  , Append (oeffs1 :\\ effs2) effs2
  , Append (oeffs1 :\\ effs2) oeffs2
  , Injects (oeffs1 :\\ effs2) oeffs, Injects oeffs2 oeffs
  , Injects oeffs1 ((oeffs1 :\\ effs2) :++ effs2)
  , Injects (effs2 :\\ effs1) effs2
  , fam (Effs (oeffs1 :\\ effs2))
  , fam (Effs effs2) 
  , effs  ~ effs1 `Union` effs2
  , oeffs ~ (oeffs1 :\\ effs2) `Union` oeffs2 )
  => Handler effs1 oeffs1 fs1 fam
  -> Handler effs2 oeffs2 fs2 fam
  -> Handler (effs1 `Union` effs2) ((oeffs1 :\\ effs2) `Union` oeffs2 ) (fs2 :++ fs1) fam
(<&>) = fuse

pipe :: forall effs1 effs2 oeffs1 oeffs2 fs1 fs2 oeffs fam .
  ( All Functor (fs2 :++ fs1)
  , Expose fs2
  , oeffs ~ ((oeffs1 :\\ effs2) `Union` oeffs2)
  , Append (oeffs1 :\\ effs2) effs2
  , Injects oeffs2 oeffs
  , Injects oeffs1 ((oeffs1 :\\ effs2) :++ effs2)
  , Injects (oeffs1 :\\ effs2) oeffs
  , fam (Effs (oeffs1 :\\ effs2)) )
  => Handler effs1 oeffs1 fs1 fam
  -> Handler effs2 oeffs2 fs2 fam
  -> Handler effs1 ((oeffs1 :\\ effs2) `Union` oeffs2) (fs2 :++ fs1) fam
pipe (Handler h1) (Handler h2) = Handler (pipe' h1 h2)

pipe' :: forall effs1 effs2 oeffs1 oeffs2 t1 t2 fs1 fs2 oeffs fam .
  ( All Functor (fs2 :++ fs1)
  , MonadTrans t1
  , MonadTrans t2
  , HFunctor t1
  , HFunctor t2
  , Expose fs2
  , oeffs ~ ((oeffs1 :\\ effs2) `Union` oeffs2)
  , Append (oeffs1 :\\ effs2) effs2
  , Injects oeffs2 oeffs
  , Injects oeffs1 ((oeffs1 :\\ effs2) :++ effs2)
  , Injects (oeffs1 :\\ effs2) oeffs 
  , fam (Effs (oeffs1 :\\ effs2)) )
  => Handler' effs1 oeffs1 t1 fs1 fam
  -> Handler' effs2 oeffs2 t2 fs2 fam
  -> Handler' effs1 ((oeffs1 :\\ effs2) `Union` oeffs2) (HCompose t1 t2) (fs2 :++ fs1) fam
pipe' (Handler' run1 malg1 mfwd1) (Handler' run2 malg2 mfwd2) =
  Handler' run malg mfwd where
  run  :: forall m . Monad m
    => (forall x . Effs ((oeffs1 :\\ effs2) `Union` oeffs2) m x -> m x)
    -> (forall x . HCompose t1 t2 m x -> m (Comps (fs2 :++ fs1) x))
  run oalg
    = fmap (unexpose @fs2 @fs1)
    . run2 (oalg . injs)
    . run1 (weakenAlg $ heither @(oeffs1 :\\ effs2) @(effs2)
        (mfwd2 (weakenAlg oalg))
        (malg2 (weakenAlg oalg)))
    . getHCompose

  malg :: forall m . Monad m
    => (forall x . Effs ((oeffs1 :\\ effs2) `Union` oeffs2) m x -> m x)
    -> (forall x . Effs effs1 (HCompose t1 t2 m) x -> HCompose t1 t2  m x)
  malg oalg
    = HCompose
    . (malg1 (weakenAlg $ heither @(oeffs1 :\\ effs2) @effs2
                            (mfwd2 (weakenAlg oalg))
                            (malg2 (weakenAlg oalg))))
    . hmap getHCompose

  mfwd
    :: forall m sig . (Monad m , fam sig, HFunctor sig)
    => (forall x. sig m x -> m x)
    -> forall x. sig (HCompose t1 t2 m) x -> HCompose t1 t2 m x
  mfwd alg
    = HCompose
    . mfwd1 (mfwd2 alg)
    . hmap getHCompose

pass :: forall sig effs oeffs fs fam .
  ( All Functor fs
  , Append effs (sig :\\ effs)
  , Append (oeffs :\\ sig) sig
  , Append (oeffs :\\ sig) (sig :\\ (oeffs :\\ sig))
  , Injects sig ((oeffs :\\ sig) :++ (sig :\\ (oeffs :\\ sig)))
  , Injects oeffs ((oeffs :\\ sig) :++ sig)
  , Injects (oeffs :\\ sig) ((oeffs :\\ sig) :++ (sig :\\ (oeffs :\\ sig)))
  , Injects (sig :\\ effs) sig 
  , fam (Effs (oeffs :\\ sig))
  , fam (Effs sig) )
  => Handler effs oeffs fs fam
  -> Handler (effs `Union` sig) ((oeffs :\\ sig) `Union` sig) fs fam
pass h = fuse h (forward @sig)

forward :: Handler effs effs '[] fam
forward = Handler $ Handler'
  (const (\(IdentityT mx) -> fmap CNil mx))
  (\oalg -> IdentityT . oalg . hmap runIdentityT)
  (\alg  -> IdentityT . alg . hmap runIdentityT)


handle :: forall ieffs fs fam a .
  ( Recompose fs , All fam ieffs )
  => Handler ieffs '[] fs fam
  -> Prog ieffs a -> (Composes fs a)
handle (Handler h) p = handle' h p

handle' :: forall ieffs t fs fam a .
  ( Monad (t Identity)
  , Recompose fs, All fam ieffs )
  => Handler' ieffs '[] t fs fam
  -> Prog ieffs a -> Composes fs a
handle' (Handler' run malg mfwd)
  = runIdentity
  . fmap @Identity (recompose @fs @a)
  . run @Identity (absurdEffs . injs)
  . eval (malg (absurdEffs . injs))

handleWith :: forall ieffs oeffs xeffs m fs a fam .
  ( Monad m
  , Recompose fs
  , Append ieffs (xeffs :\\ ieffs)
  , Injects oeffs xeffs
  , Injects (xeffs :\\ ieffs) xeffs
  , fam (Effs xeffs) )
  => (forall x. Effs xeffs m x -> m x)
  -> Handler ieffs oeffs fs fam
  -> Prog (ieffs `Union` xeffs) a -> m (Composes fs a)
handleWith xalg (Handler (Handler' run malg mfwd))
  = fmap @m (recompose @fs @a)
  . run @m (xalg . injs)
  . eval (hunion @ieffs @xeffs (malg (xalg . injs)) (mfwd xalg))

-- handleOne
--   :: (Monad (HComps ts (Prog oeffs)), Recompose fs)
--   => Handler effs ts fs oeffs -> Prog effs a -> Prog oeffs (Composes fs a)
-- handleOne (Handler run malg mfwd)
--   = fmap recompose . run (Call . fmap return) . eval (malg (Call . fmap return))
-- 
-- handleOneWith
--   :: (Monad (HComps ts (Prog oeffs)), Recompose fs)
--   => (forall x . Effs oeffs (Prog oeffs) x -> Prog oeffs x)
--   -> Handler effs ts fs oeffs -> Prog effs a -> Prog oeffs (Composes fs a)
-- handleOneWith xalg (Handler run malg mfwd)
--   = fmap recompose . run xalg . eval (malg xalg)
-- 
-- handleSome
--   :: forall sig eff oeffs ts fs a
--   .  (Injects oeffs (oeffs :++ sig), Injects sig (oeffs :++ sig), Append eff sig
--   ,  Monad (HComps ts (Prog (oeffs :++ sig))), Recompose fs)
--   => Handler eff ts fs oeffs -> Prog (eff :++ sig) a -> Prog (oeffs :++ sig) (Composes fs a)
-- handleSome (Handler run malg mfwd)
--   = fmap recompose
--   . run (Call . injs . fmap return)
--   . eval (heither @eff @sig (malg @(Prog (oeffs :++ sig)) (Call . injs . fmap return))
--                             (mfwd @(Prog (oeffs :++ sig)) (Call . injs . fmap return)))



weaken
  :: forall ieffs ieffs' oeffs oeffs' ts fs fam
  . ( Injects ieffs ieffs'
    , Injects oeffs oeffs'
    )
  => Handler ieffs' oeffs fs fam
  -> Handler ieffs oeffs' fs fam
weaken (Handler (Handler' run malg mfwd))
  = Handler (Handler' (\oalg -> run (oalg . injs)) (\oalg -> malg (oalg . injs) . injs) mfwd)

hide
  :: forall sigs effs oeffs f fam
  .  (Injects (effs :\\ sigs) effs, Injects oeffs oeffs)
  => Handler effs oeffs f fam -> Handler (effs :\\ sigs) oeffs f fam
hide h = weaken h
-- (\/)
--   :: forall effs1 effs2 ts fs oeffs
--   . (Append effs1 effs2)
--   => Handler effs1 ts fs oeffs
--   -> Handler effs2 ts fs oeffs
--   -> Handler (effs1 :++ effs2) ts fs oeffs
-- Handler run1 malg1 mfwd1 \/ Handler run2 malg2 mfwd2
--   = Handler run1 (\oalg -> heither (malg1 oalg) (malg2 oalg)) mfwd1


-- transform
--   :: forall effs ts
--   . ( All MonadTrans ts, Functor (HComposes ts Identity) )
--   => Handler effs ts '[HComposes ts Identity] effs
-- transform = Handler run malg mfwd where
--   run  :: forall m . Monad m
--        => (forall x . Effs effs m x -> m x)
--        -> (forall x . HComps ts m x -> m (Comps '[HComposes ts Identity] x))
--   run alg (HNil x)  = fmap (CCons . Identity . CNil) x
--   run alg (HCons x) = (fmap (CCons . undefined . fmap CNil) . return @m) x
-- 
--   malg :: forall m . Monad m
--        => (forall x . Effs effs m x -> m x)
--        -> (forall x . Effs effs (HComps ts m) x -> HComps ts m x)
--   malg = undefined
-- 
--   mfwd :: forall m sig . Monad m
--        => (forall x . Effs sig m x -> m x)
--        -> (forall x . Effs sig (HComps ts m) x -> HComps ts m x)
--   mfwd = undefined

-- A second way:
-- fuse the handler with a trivial one that targets
-- all of xeffs. I expect these to be equivalent.

weakenAlg
  :: forall eff eff' m x . (Injects eff eff')
  => (Effs eff' m x -> m x)
  -> (Effs eff  m x -> m x)
weakenAlg alg = alg . injs

-- Modular carriers
-- ----------------
--
-- So far the carriers of our library have always been a monad:
-- the algebras in a `Handler` are always of some monad `m`.
-- However, this is not always possible or desirable.
-- For example, although it is known that the (functorial)
-- composition of two applicatives is applicative, the
-- composition of two monads need not be a monad. Concretely,
-- the composition of `m` and the list monad `[]` is not a monad
-- (sometimes called `ListT` done wrong). It can be modelled
-- by `m [x]` for all x. Such a functor can nevertheless be a carrier:
data ListC m x = ListC (m [x])

-- The caveat is that we can use this carrier for nondet computations so long
-- as there are no scoped operations such as `search` or `once`.
--
-- Another example is ContT; since there only algebraic operations
-- can be forwarded.
data Carrier c f asig = Carrier
  { crun :: forall m x . Monad m => c m x -> m (f x)
  , calg :: forall m x . Monad m => Effs asig Identity (c m x) -> c m x
  , cfwd :: forall m x . Monad m => m (c m x) -> c m x
  , cgen :: forall m x . Monad m => x -> c m x
  }

newtype Carry (c :: (Type -> Type) -> Type -> Type)
              (m :: Type -> Type)
              a
  = Carry (forall x . Cont (c m x) a)
  deriving Functor

-- convert :: forall c f asig fam . Functor f
--   => Carrier c f asig -> Handler' asig '[] (Carry c) '[f] JustAlg
-- convert (Carrier cfwd calg crun cgen) = Handler' run alg fwd where
--   run :: Monad m
--       => (forall x. Effs '[] m x -> m x)
--       -> (forall x. Carry c m x -> m (Comps '[f] x))
--   run oalg (Carry mx) = fmap comps $ (crun (runCont mx cgen))
-- 
--   alg :: forall m . Monad m
--       => (forall x. Effs '[] m x -> m x)
--       -> (forall x. Effs asig (Carry c m) x -> Carry c m x)
--   alg oalg = go calg oalg where
--     go :: forall asig'
--        . (forall m x . Monad m => Effs asig' Identity (c m x) -> c m x)
--        -> (forall x. Effs '[] m x -> m x)
--        -> (forall x. Effs asig' (Carry c m) x -> Carry c m x)
--     go calg oalg (Eff (Alg x)) = Carry (cont (\k -> calg (fmap k (Eff (Alg x)))))
--     go calg oalg (Eff (Scp x)) = error "convert: operations should be algebraic!"
--     go calg oalg (Effs x)      = go (calg . Effs) oalg x
-- 
--   fwd :: ()
--   fwd = undefined
  -- fwd :: Monad m
  --     => (forall x. Effs sig m x -> m x)
  --     -> (forall x. Effs sig (Carry c m) x -> Carry c m x)
  -- fwd oalg (Eff (Alg x)) = Carry (cont (\k -> (cfwd . oalg . Eff . Alg)(fmap k x)))
  -- fwd oalg (Eff (Scp x)) = error "convert: Cannot forward scoped operations!"
  -- fwd oalg (Effs (x))    = fwd (oalg . Effs) x


