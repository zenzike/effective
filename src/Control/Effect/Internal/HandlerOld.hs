{-|
Module      : Control.Effect.Internal.Handler
Description : Handlers and handler combinators
License     : BSD-3-Clause
Maintainer  : Nicolas Wu
Stability   : experimental
-}

{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ImpredicativeTypes #-}

module Control.Effect.Internal.Handler where
import Control.Effect.Internal.Handler.Type
import Control.Effect.Internal.Prog
import Control.Effect.Internal.Effs
import Control.Effect.Internal.Forward

import GHC.Base
import Unsafe.Coerce


import Control.Monad.Trans.Class
import Control.Monad.Trans.Identity
import Control.Monad.Trans.Compose

import Data.List.Kind


import Data.Functor.Identity
import Data.Functor.Compose
import Data.HFunctor


{-
The original version of Handler included a forwarder:
```
   mfwd :: forall m sig . Monad m
         => (forall x . Effs sig m x -> m x)
         -> (forall x . Effs sig (t m) x -> t m x)
```
This was replaced by the `Forward` class, which works with families,
since it is too onerous forward every form of signature.

An alternative design would be for the forwarding function to be
provided when the handler is constructed, by the `Forward` class.
However, this means that the family of values that can be
forwarded is then exposed at the type level of the handler type:
```
  data Handler effs oeffs t fs feffs
```
where `feffs` is the family of effects that can be forwarded, and then we would
need constraints such as `Forward feffs t` to be in place. The advantage
is that custom effects can forward more flexibly, but at the cost
of added complexity in the signature.
That complexity could be hidden by another datatype, much
in the same way as `Handler` obscures the underlying `t` type.

Another design, which was previously implemented
is to have families explicit in the handler signature.
A list of such families would indicate those that can be handled.
If `h1 :: Handler eff1 t1 fam1`, and `h2 :: Handler eff2 t2 fam2`, then the two
can be composed so long as `fam1 ⊇ fam2`. All of `eff1` will be
dealt with into carrier the `t1` carrier, and need not concern `h2`,
so long as the carrier is compatible with `eff2`. However, if `eff2` contains a
family of effects that is not recognised by `h1`, then it is
impossible to forward those effects and fusion is impossible.

Yet another design is to use a handler of the form:
```
type Handler
  :: [Effect]                          -- effs  : input effects
  -> [Effect]                          -- oeffs : output effects
  -> [Type -> Type]                    -- f     : carrier type
  -> Type
data Handler effs oeffs fs
  =  forall t . (MonadTrans t
              -- Forward effs t
                )
  => Handler (Handler effs oeffs t fs)
```
This is a wrapper around a handler that involves a transformer
held as an existential held in some unexposed variable `t`.
The problem with this a approach is that handlers can no longer
fuse easily, since fusion requires a `Forward` constraint
that mentions `t` explicitly.

The closest `fuse` using this interface is:
```
fuse
  :: forall effs1 effs2 oeffs1 oeffs2 fs1 fs2 oeffs1' .
  ( Functor (RComps fs1), RSplit fs2
  , Append effs1 (effs2 :\\ effs1),  Append (oeffs1 :\\ effs2) effs2
  , Injects oeffs2 ((oeffs1 :\\ effs2) :++ (oeffs2 :\\ (oeffs1 :\\ effs2)))
  , Injects oeffs1 ((oeffs1 :\\ effs2) :++ effs2)
  , Injects (oeffs1 :\\ effs2)    ((oeffs1 :\\ effs2) :++ (oeffs2 :\\ (oeffs1 :\\ effs2)))
  , Injects (effs2 :\\ effs1) effs2
  , oeffs1' ~ oeffs1 :\\ effs2
  , forall t . MonadTrans t => Forward effs2 t
  , forall t . MonadTrans t => Forward oeffs1' t
  )
  => Handler effs1 oeffs1 fs2
  -> Handler effs2 oeffs2 fs1
  -> Handler (effs1 :++ (effs2 :\\ effs1))
             ((oeffs1 :\\ effs2) :++ (oeffs2 :\\ (oeffs1 :\\ effs2)))
             (fs2 :++ fs1)
fuse (Handler h1) (Handler h2) = Handler (fuse h1 h2)
```
This uses `Forward` constraints that work regardless of `t`,
that is, `forall t . MonadTrans t => Forward effs2 t`. While this is definable
for algebraic effects, it is not possible for all scoped effects.

-}

-- | A t'Handler' will process input effects @effs@ and produce output effects
-- @oeffs@, while working with the monad transformer @t@. The final value
-- will be wrapped with @f@.
--
-- > type Handler
-- >   :: [Effect]                             -- effs  : input effects
-- >   -> [Effect]                             -- oeffs : output effects
-- >   -> ((Type -> Type) -> (Type -> Type))   -- t     : semantics transformer
-- >   -> (Type -> Type)                       -- f     : carrier wrapper
-- >   -> Type
--
type Handler
  :: [Effect]                             -- ^ effs  : input effects
  -> [Effect]                             -- ^ oeffs : output effects
  -> ((Type -> Type) -> (Type -> Type))   -- ^ t     : semantics transformer
  -> (Type -> Type)                       -- ^ f     : carrier wrapper
  -> Type
data Handler effs oeffs ts fs =
  Handler
  { -- | Modular monad transformer runner into carrier wrapper
    hrun
      :: forall m . Monad m
      => Algebra oeffs m                  -- ^ output algebra
      -> (forall x . ts m x -> m (fs x))  -- ^ transformer to wrapper

    -- | Modular algebra into @ts m@
  , halg :: forall m . Monad m
         => Algebra oeffs m               -- ^ output algebra
         -> Algebra effs (ts m)
  }

-- | Given @hrun@ and @halg@ will construct a @Handler effs oeffs t fs@. This
-- is a simplified version of the @Handler@ constructor where @run@ does
-- not need to be a modular runner.
{-# INLINE handler #-}
handler
  :: (forall m a . Monad m => t m a -> m (f a))
  -> (forall m . Monad m => Algebra oeffs m -> Algebra effs (t m))
  -> Handler effs oeffs t f
handler run alg = Handler (\oalg -> run) (\oalg -> alg oalg)

-- | The identity handler.
{-# INLINE identity #-}
identity :: Handler '[] '[] IdentityT Identity
identity = Handler hrun halg where

  hrun :: Monad m => Algebra '[] m -> forall x. IdentityT m x -> m (Identity x)
  hrun _ (IdentityT x) = fmap Identity x

  halg :: Algebra '[] m -> Algebra '[] (IdentityT m)
  halg _ = absurdEffs

-- | Weakens a handler from @Handler effs oeffs t f@ to @Handler effs' oeffs' t f@,
-- when @effs'@ injects into @effs@ and @oeffs@ injects into @oeffs'@.
{-# INLINE weaken #-}
weaken
  :: forall effs effs' oeffs oeffs' t f
  . ( Injects effs' effs
    , Injects oeffs oeffs'
    )
  => Handler effs  oeffs  t f
  -> Handler effs' oeffs' t f
weaken (Handler run halg)
  = (Handler (\oalg -> run (oalg . injs)) (\oalg -> halg (oalg . injs) . injs))

-- | Hides the effects in @heffs@ from the handler. The type argument @heffs@ typically
-- needs given explicitly.
{-# INLINE hide #-}
hide
  :: forall heffs effs oeffs ts fs
  .  (Injects (effs :\\ heffs) effs, Injects oeffs oeffs)
  => Handler effs oeffs ts fs
  -> Handler (effs :\\ heffs) oeffs ts fs
hide h = weaken h

-- | Operations from the output effect @oeffs@ of a handler can be added
-- to the input effect if the handler can forward it.
{-# INLINE bypass #-}
bypass
  :: forall beffs effs oeffs ts fs
  . ( Injects beffs oeffs, Forwards beffs ts, 
      Append effs (beffs :\\ effs), Injects (beffs :\\ effs) beffs )
  => Handler effs oeffs ts fs
  -> Handler (effs `Union` beffs) oeffs ts fs
bypass (Handler run alg) = Handler run (\oalg -> 
  hunion @effs @beffs (alg oalg) (fwds (oalg . injs)))

-- | The result of @interpret rephrase@ is a new @Handler effs oeffs IdentityT Identity@.
-- This is created by using the supplied @rephrase :: Effs effs m x -> Prog oeffs x@
-- parameter to translate @effs@ into a program that uses @oeffs@.
interpret
  :: forall effs oeffs
  .  ( HFunctor (Effs effs), HFunctor (Effs oeffs) )
  => (forall m x . Effs effs m x -> Prog oeffs x)   -- ^ @rephrase@
  -> Handler effs oeffs IdentityT Identity
interpret rephrase = interpretM talg
  where
    talg :: forall m . Monad m
         => (forall x. Effs oeffs m x -> m x)
         -> (forall x. Effs effs m x  -> m x)
    talg oalg op = eval oalg (rephrase op)

-- | A special case of `interpret` for one effect @eff@.
interpret1
  :: forall eff oeffs
  .  ( HFunctor eff, HFunctor (Effs oeffs) )
  => (forall m x . eff m x -> Prog oeffs x)
  -> Handler '[eff] oeffs IdentityT Identity
interpret1 rephrase = interpret (\(Eff e) -> rephrase e)

-- | The result of @interpretM mrephrase@ is a new @Handler effs oeffs IdentityT Identity@.
-- This is created by using the supplied @mrephrase :: (forall x . Effs oeffs m x -> m x) -> Effs effs m x -> m x@ parameter.
-- to rephrase @effs@ into an arbitrary monad @m@.
-- When @mrephrase@ is used, it is given an @oalg :: Effs oeffs m x -> m x@
-- parameter that makes it possible to create a value in @m@.
interpretM
  :: forall effs oeffs .
  HFunctor (Effs effs)
  =>
    (forall m . Monad m =>
      (forall x . Effs oeffs m x -> m x)
    -> (forall x . Effs effs m x -> m x))   -- ^ @mrephrase@
  -> Handler effs oeffs IdentityT Identity
interpretM mrephrase
  = Handler @effs @oeffs @IdentityT
      (const (fmap Identity . runIdentityT))
      (\oalg -> IdentityT . mrephrase oalg . hmap runIdentityT)

-- HERE BE DRAGONS
{-
Fusing handlers `h1 :: Handler effs1 oeffs1 t1 fs1` and `h2 :: Handler effs2
oeffs2 t2 fs2` results in a handler that can deal with the effects of `eff1` and
those of `eff2`, as well as appropriately deal with effects `oeff1` that get
output by the first handler.

A handler consists of `malg`, which deals with all the operations in the
syntax tree that the handler will be applied to, and `run`, which
turns the final transformed monad into a functor.

The task of of the `malg` algebra is to interpret the union of `effs1` and
`effs2`. To do so, it must appropriately use the output algebra `oalg` that it
is given, which is responsible for handling any effects that the handler
may produce. The effects in `oeffs1` are produced by `h1`, and
the effects in `oeffs2` are produced by `h2`. If an effect `oeff1` is in
`effs2`, then it means that it is produced by `h1` and can be consumed by `h2`.
To do so, `malg2` is used. Any other effect produced by `h1` will not
be recognised by `h2`, and must therefore be forwarded into the `t2`
transformer as outlined by the `fwd @(oeffs1 :\\ effs2) t2` function.

Effects

means that any syntax of `eff2` must be forwarded by the
transformer `t1` of `h1`, since the effect must bypass `eff1` into syntax in the
context given by `t1`, ready to be consumed by the second handler.  This is
captured by the `Forward eff2 t1` constraint.

When the effect is from `effs2`, the `malg2` handler must
of course play a part. The problem is that the
carrier that is targeted is `t ~ ComposeT t1 t2`,
whereas `malg` can only work for `t2` carriers.
This makes sense, since the operations in `effs2` must operate
only after `h1` has done its work on the syntax tree.
To make use of `malg` operate with the `t1` carrier,
-}
{-# INLINE fuse #-}
{-# INLINE (|>) #-}
fuse, (|>)
  :: forall effs1 effs2 oeffs1 oeffs2 ts1 ts2 fs1 fs2 effs oeffs ts fs
  . ( effs  ~ effs1 `Union` effs2
    , oeffs ~ (oeffs1 :\\ effs2) `Union` oeffs2
    , ts    ~ HRAssoc (ts1 `ComposeT` ts2)
    , fs    ~ RAssoc (fs2 `Compose` fs1)
    , forall m . Monad m => Monad (ts2 m)
#if __GLASGOW_HASKELL__ <= 904
    , forall m . Monad m => Monad (ts1 (ts2 m))
#endif
    , Forwards (oeffs1 :\\ effs2) ts2
    , Forwards effs2 ts1
    , Injects (oeffs1 :\\ effs2) oeffs
    , Injects (effs2 :\\ effs1) effs2
    , Injects oeffs2 oeffs
    , Injects oeffs1 ((oeffs1 :\\ effs2) :++ effs2)
--    , KnownNat (Length effs1)
--    , KnownNat (Length effs2)
    , Append (oeffs1 :\\ effs2) effs2
    , Append effs1 (effs2 :\\ effs1)
    )
  => Handler effs1 oeffs1 ts1 fs1   -- ^ @h1@
  -> Handler effs2 oeffs2 ts2 fs2   -- ^ @h2@
  -> Handler effs  oeffs  ts  fs

-- | A synonym for `fuse`.
(|>) = fuse

-- | Fuses two handlers @h1 :: Handler effs1 oeffs1 t1 f1@ and @h2 :: Handler effs2 oeffs2 t2 f2@ together.
-- The result is @Handler effs oeffs t f@ where:
--
-- > effs  ~ effs1 `Union` effs2                 -- input effects
-- > oeffs ~ (oeffs1 :\\ effs2) `Union` oeffs2   -- output effects
-- > t     ~ HRAssoc (t1 `ComposeT` t2)          -- semantics transformer
-- > f     ~ RAssoc  (f2 `Compose` f1)           -- carrier wrapper
--
-- The resulting handler consumes all the effects recognised by either @h1@ or
-- @h2@, with priority for @h1@. Any effects output by @h1@ will be consumed by
-- @h2@. Any effects not recognised are forwarded into @oeffs@.
--
-- The semantics transformer @t@ and the carrier wrapper @f@ are normalised
-- using 'HRAssoc' and 'RAssoc' respectively, which removes any identities
-- and reassociates all compositions to the right.
fuse (Handler run1 malg1) (Handler run2 malg2) = Handler run halg where
  {-# INLINE run #-}
  run :: forall m . Monad m => Algebra oeffs m -> forall x. ts m x -> m (fs x)
  run oalg
    = unsafeCoerce @(m (fs2 (fs1 _x))) @(m (fs _x))
    . run2 (oalg . injs)
    . run1 (weakenAlg @oeffs1 @((oeffs1 :\\ effs2) :++ effs2) $
        heither @(oeffs1 :\\ effs2) @effs2
          (fwds @(oeffs1 :\\ effs2) @(ts2)
            (weakenAlg @(oeffs1 :\\ effs2) @oeffs oalg))
          (malg2 (weakenAlg @oeffs2 @oeffs oalg)))
    . unsafeCoerce @(ts m _) @(ts1 (ts2 m) _)

  {-# INLINE halg #-}
  halg :: forall m . Monad m => Algebra oeffs m -> Algebra effs (ts m)
  halg oalg
    = unsafeCoerce @(ts1 (ts2 m) _) @(ts m _)
    . hunion @effs1 @effs2
        (malg1 (weakenAlg $
          heither @(oeffs1 :\\ effs2) @effs2
            (fwds @(oeffs1 :\\ effs2) @ts2 (weakenAlg oalg))
            (malg2 (weakenAlg oalg))))
        (fwds @effs2 @ts1 (malg2 (oalg . injs)))
    . unsafeCoerce @(Effs effs (ts m) _) @(Effs effs (ts1 (ts2 m)) _)

infixr 9 |>>
{-# INLINE simpleFuse #-}
simpleFuse, (|>>) 
              :: forall effs1 t1 f1 effs2 t2 f2 t f.
              ( Forwards effs2 t1
              , forall m. Monad m => Monad (t2 m)
              , forall m. Monad m => Monad (t1 (t2 m))
              , Append effs1 effs2
              , HFunctor (Effs (effs1 :++ effs2))
              , t ~ (t1 `ComposeT` t2)
              , f ~ (f2 `Compose` f1)
              )
           => Handler effs1 '[] t1 f1 -> Handler effs2 '[] t2 f2 
           -> Handler (effs1 :++ effs2) '[] t f
(|>>) = simpleFuse
simpleFuse (Handler r1 a1) (Handler r2 a2) =
   Handler (\(o :: Algebra '[] m) ->
                 fmap Compose 
               . r2 absurdEffs 
               . r1 absurdEffs 
               . getComposeT )
           (\(o :: Algebra '[] m) -> 
               ComposeT 
             . heither (a1 absurdEffs) (fwds (a2 absurdEffs)) 
             . hmap getComposeT)

infixr 9 ||>>
{-# INLINE simpleFuseU #-}
{-# INLINE (||>>) #-}
simpleFuseU, (||>>) 
              :: forall effs1 t1 f1 effs2 t2 f2 t f.
              ( Forwards effs2 t1
              , forall m. Monad m => Monad (t2 m)
              , forall m. Monad m => Monad (t1 (t2 m))
              , Append effs1 (effs2 :\\ effs1)
              , Injects (effs2 :\\ effs1) effs2
              , HFunctor (Effs (effs1 `Union` effs2))
              , t ~ (t1 `ComposeT` t2)
              , f ~ (f2 `Compose` f1)
              )
           => Handler effs1 '[] t1 f1 -> Handler effs2 '[] t2 f2 
           -> Handler (effs1 `Union` effs2) '[] t f
(||>>) = simpleFuseU
simpleFuseU (Handler r1 a1) (Handler r2 a2) =
   Handler (\(o :: Algebra '[] m) ->
                 fmap Compose 
               . r2 absurdEffs 
               . r1 absurdEffs 
               . getComposeT )
           (\(o :: Algebra '[] m) -> 
               ComposeT 
             . hunion (a1 absurdEffs) (fwds (a2 absurdEffs)) 
             . hmap getComposeT)

{-# INLINE pipe #-}
{-# INLINE (||>) #-}
pipe, (||>)
  :: forall effs1 effs2 oeffs1 oeffs2 ts1 ts2 fs1 fs2 effs oeffs ts fs
  . ( effs  ~ effs1
    , oeffs ~ (oeffs1 :\\ effs2) `Union` oeffs2
    , ts    ~ HRAssoc (ts1 `ComposeT` ts2)
    , fs    ~ RAssoc (fs2 `Compose` fs1)
    , MonadTrans ts1
    , MonadTrans ts2
#if __GLASGOW_HASKELL__ <= 904
    , forall m . Monad m => Monad (ts2 m)
#endif
    , Forwards (oeffs1 :\\ effs2) ts2
    , Injects (oeffs1 :\\ effs2) oeffs
    , Injects oeffs2 oeffs
    , Injects oeffs1 ((oeffs1 :\\ effs2) :++ effs2)
    -- , KnownNat (Length effs2)
    , Append (oeffs1 :\\ effs2) effs2
    )
  => Handler effs1 oeffs1 ts1 fs1    -- ^ Handler @h1@
  -> Handler effs2 oeffs2 ts2 fs2    -- ^ Handler @h2@
  -> Handler effs  oeffs  ts  fs

-- | A synonym for 'pipe'
(||>) = pipe

-- | Pipe results of handler @h1 :: Handler effs1 oeffs1 t1 f1@ into @h2 :: Handler effs2 oeffs2 t2 f2@.
-- The result is @Handler effs oeffs t f@ where:
--
-- > effs  ~ effs1                               -- input effects
-- > oeffs ~ (oeffs1 :\\ effs2) `Union` oeffs2   -- output effects
-- > ts    ~ HRAssoc (ts1 `ComposeT` ts2)        -- semantics transformer
-- > fs    ~ RAssoc (fs2 `Compose` fs1)          -- carrier wrapper
--
-- The resulting handler consumes all the effects recognised by @h1@.
-- Any effects output by @h1@ will be consumed by
-- @h2@. Any effects not recognised are forwarded into @oeffs@.
--
-- The semantics transformer @t@ and the carrier wrapper @f@ are normalised
-- using 'HRAssoc' and 'RAssoc' respectively, which removes any identities
-- and reassociates all compositions to the right.
pipe (Handler run1 malg1)  (Handler run2 malg2) = Handler run halg where
  run :: forall m . Monad m => Algebra oeffs m -> forall x. ts m x -> m (fs x)
  run oalg
    = unsafeCoerce @(m (fs2 (fs1 _x))) @(m (fs _x))
    . run2 (oalg . injs)
    . run1 (weakenAlg $ heither @(oeffs1 :\\ effs2) @effs2
        (fwds @(oeffs1 :\\ effs2) @ts2 (weakenAlg oalg))
        (malg2 (weakenAlg oalg)))
    . unsafeCoerce @(ts m _x) @(ts1 (ts2 m) _x)

  halg :: forall m . Monad m =>
    Algebra oeffs m ->
    Algebra effs (ts m)
  halg oalg
    = unsafeCoerce @(ts1 (ts2 m) _x) @(ts m _x)
    . malg1 (weakenAlg $ heither @(oeffs1 :\\ effs2) @effs2
        (fwds @(oeffs1 :\\ effs2) @ts2 (weakenAlg oalg))
        (malg2 (weakenAlg oalg)))
    . unsafeCoerce @(Effs _effs (ts m) _x) @(Effs _effs (ts1 (ts2 m)) _x)

-- pass :: forall sig effs oeffs fs fam .
--   ( All Functor fs
--   , Append effs (sig :\\ effs)
--   , Append (oeffs :\\ sig) sig
--   , Append (oeffs :\\ sig) (sig :\\ (oeffs :\\ sig))
--   , Injects sig ((oeffs :\\ sig) :++ (sig :\\ (oeffs :\\ sig)))
--   , Injects oeffs ((oeffs :\\ sig) :++ sig)
--   , Injects (oeffs :\\ sig) ((oeffs :\\ sig) :++ (sig :\\ (oeffs :\\ sig)))
--   , Injects (sig :\\ effs) sig
--   , fam (Effs (oeffs :\\ sig))
--   , fam (Effs sig) )
--   => Handler effs oeffs fs fam
--   -> Handler (effs `Union` sig) ((oeffs :\\ sig) `Union` sig) fs fam
-- pass h = fuse h (forward @sig)
--      (\alg  -> IdentityT . alg . hmap runIdentityT)

-- | @handle h p@ uses the handler @h@ to evaluate the program @p@. All of the
-- effects @effs@ in the program must be recognised by the handler,
-- and the handler must produce no effects.
-- The result is normalised with 'Apply' so that any t`Identity` functors are removed.
{-# INLINE handle #-}
handle :: forall effs ts f a .
  ( Monad (ts Identity) , Functor f, HFunctor (Effs effs) )
  => Handler effs '[] ts f        -- ^ Handler @h@ with no output effects
  -> Prog effs a                  -- ^ Program @p@ with effects @effs@
  -> Apply f a
handle (Handler run halg)
  = unsafeCoerce @(f a) @(Apply f a)
  . runIdentity
  . inline (run @Identity) absurdEffs
  . eval (inline (halg absurdEffs))

{-# INLINE handleN #-}
handleN :: forall effs ts f a .
  ( Monad (ts Identity) , Functor f, HFunctor (Effs effs) )
  => Handler effs '[] ts f        -- ^ Handler @h@ with no output effects
  -> Prog effs a                  -- ^ Program @p@ with effects @effs@
  -> f a
handleN (Handler run halg)
  = runIdentity
  . run @Identity absurdEffs
  . eval (halg absurdEffs)

-- handle'
--   :: forall effs oeffs ts fs a . (Monad (HComps ts (Prog oeffs)), Functors fs)
--   => Handler effs oeffs ts fs -> Prog effs a -> Prog oeffs (RComposes fs a)
-- handle' (Handler run halg)
--   = fmap unRComps . run (\x -> Call x id return) . eval (halg (\x -> Call x id return))

-- handle''
--   :: forall sig eff oeffs ts fs a
--   .  (Injects oeffs (oeffs :++ sig), Injects sig (oeffs :++ sig)
--   ,  Monad (HComps ts (Prog (oeffs :++ sig)))
--   , Functors fs
--   , KnownNat (Length eff)
--   , KnownNat (Length sig)
--   , Forward (Effs sig)  (HComps ts)
--   )
--   => Handler eff oeffs ts fs -> Prog (eff :++ sig) a -> Prog (oeffs :++ sig) (RComposes fs a)
-- handle'' (Handler run halg)
--   = fmap unRComps
--   . run (\x -> Call (injs x) id return)
--   . eval (heither @eff @sig (halg @(Prog (oeffs :++ sig)) (\x -> Call (injs x) id return))
--                             (fwd (\x -> Call (injs x) id return)))


-- | @handleM xalg h p@ uses the handler @h@ to evaluate the program @p@. Any
-- residual effects in @xeffs@ not recognised by @h@ must be consumed by the
-- algebra @xalg@. If an effect is both in @effs@ and @xeffs@, it is handled by @h@.
handleM :: forall effs oeffs xeffs m t f a .
  ( Monad m
  , forall m . Monad m => Monad (t m)
  , Forwards xeffs t
  , Injects oeffs xeffs
  , Injects (xeffs :\\ effs) xeffs
  , Append effs (xeffs :\\ effs)
  , HFunctor (Effs (effs :++ (xeffs :\\ effs)))
  )
  => Algebra xeffs m               -- ^ Algebra @xalg@ for external effects @xeffs@
  -> Handler effs oeffs t f        -- ^ Handler @h@
  -> Prog (effs `Union` xeffs) a   -- ^ Program @p@ that contains @xeffs@
  -> m (Apply f a)
handleM xalg (Handler run halg)
  = unsafeCoerce @(m (f a)) @(m (Apply f a))
  . run @m (xalg . injs)
  . eval (hunion @effs @xeffs (halg (xalg . injs)) (fwds xalg))

-- | @handleMP h p@ uses the handler @h@ to evaluate the program @p@, resulting
-- in a program with effects @xeffs@ that are not recognised by @h@.
-- If an effect is both in @effs@ and @xeffs@, it is handled by @h@.
handleP :: forall effs oeffs xeffs t f a .
  ( forall m . Monad m => Monad (t m)
  , Forwards xeffs t
  , Injects oeffs xeffs
  , Injects (xeffs :\\ effs) xeffs
  , Append effs (xeffs :\\ effs)
  , HFunctor (Effs (effs :++ (xeffs :\\ effs)))
  , HFunctor (Effs xeffs)
  )
  => Handler effs oeffs t f        -- ^ Handler @h@
  -> Prog (effs `Union` xeffs) a   -- ^ Program @p@ that contains @xeffs@
  -> Prog xeffs (Apply f a)
handleP = handleM progAlg

-- | @handleM' xalg h p@ is a variant of `handleM` where @effs `Union` xeffs@ is replaced
-- by simply '(:++)'. This function should be used only when @effs@ and @xeffs@ have
-- empty intersection. 
-- In most cases, you should just use `handleM` but sometimes limitations regarding class 
-- constraints in GHC necessitate the use of @handleM'@ (for example, in `Control.Effect.HOStore.Safe.handleHSM`.)

handleM' :: forall effs oeffs xeffs m t f a .
  ( Monad m
  , forall m . Monad m => Monad (t m)
  , Forwards xeffs t
  , Injects oeffs xeffs
  , Append effs xeffs
  , HFunctor (Effs (effs :++ xeffs))
  )
  => Algebra xeffs m               -- ^ Algebra @xalg@ for external effects @xeffs@
  -> Handler effs oeffs t f        -- ^ Handler @h@
  -> Prog (effs :++ xeffs) a       -- ^ Program @p@ that contains @xeffs@
  -> m (Apply f a)
handleM' xalg (Handler run halg)
  = unsafeCoerce @(m (f a)) @(m (Apply f a))
  . run @m (xalg . injs)
  . eval (heither @effs @xeffs (halg (xalg . injs)) (fwds xalg))


-- | @handleP' h p@ is a variant of `handleP` where @effs `Union` xeffs@ is replaced
-- by simply '(:++)'. This function should be used only when @effs@ and @xeffs@ have
-- empty intersection. 
-- In most cases, you should just use `handleP` but sometimes limitations regarding class 
-- constraints in GHC necessitate the use of @handleP'@ (for example, in `Control.Effect.HOStore.Safe.handleHSM`.)
handleP' :: forall effs oeffs xeffs t f a .
  ( Forwards xeffs t
  , forall m . Monad m => Monad (t m)
  , Injects oeffs xeffs
  , Append effs xeffs
  , HFunctor (Effs (effs :++ xeffs))
  , HFunctor (Effs xeffs)
  ) => Handler effs oeffs t f        -- ^ Handler @h@
  -> Prog (effs :++ xeffs) a         -- ^ Program @p@ that contains @xeffs@
  -> Prog xeffs (Apply f a)
handleP' = handleM' progAlg