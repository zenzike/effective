{-|
Module      : Control.Effect.Internal.Handler
Description : Handlers and handler combinators
License     : BSD-3-Clause
Maintainer  : Nicolas Wu, Zhixuan Yang
Stability   : experimental

This module contains the definition of handlers in @effective@. A handler
consists of an algebra transformer and a runner. The algebra transformer handles
operations and is the main component of a handler, while a runner is supposed to
do some initialisation or finalisation work.

The function `handle` and its variations apply a handler to a program. Other
functions in this module are handler combinators that build handlers from
smaller ones.

Handler combinators are the main innovation of this library.

  1. They improve runtime performance of effect handling by collapsing nested
  layers of effect handlers into a single handler (which is stored with
  efficient data structures).

  2. They provide an expressive language for controlling the interaction of
  effect handlers.

A good way to think about a handler @Handler effs oeffs ts a b@ is as a circuit with
input wire @effs@ and output wire @oeffs@. Then handler combinators provide
different ways to wire those circuits together.
-}

{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PartialTypeSignatures #-}

module Control.Effect.Internal.Handler where

import Control.Effect.Internal.Algebra
import Control.Effect.Internal.AlgTrans
import Control.Effect.Internal.AlgTrans.Type
import Control.Effect.Internal.Runner
import Control.Effect.Internal.Prog
import Control.Effect.Internal.Forward

import Data.Kind
import Data.List.Kind
import Data.Functor.Identity
import Data.HFunctor
import Data.Proxy

-- $namingConvention
--
-- Type-variable names for effect signatures follow a consistent convention.
-- An /effect/ (@eff@) is identified with its signature functor (e.g. @State Int@); 
-- @effs@ is a list of effects (e.g. @\'[State Int, Reader String]@).
--
-- Singular and plural forms:
--
-- * @eff@                 — one effect (e.g. in @Member eff effs@).
-- * @effs@                — a list of effects, the input to a handler (default).
-- * @oeff@ \/ @oeffs@     — single \/ list of /output/ effects from a handler.
-- * @xeffs@               — e/x/ternal effects supplied by an outside algebra,
--                          monad, or residual program (e.g. @handleM@, @evalAT@).
-- * @effs1@, @effs2@      — operands of a binary type operation (e.g. 'Union', ':\\'),
--                          numbered handlers in compositions (e.g. @generalFuse@),
--                          or paired rows where the old names were @xeffs@ and @yeffs@.
--
-- Combinator-specific prefixes appear only in the signature of the one
-- function they name, distinguishing that function's parameter from the
-- surrounding @effs@\/@oeffs@:
--
-- * @heffs@ — signatures to /h/ide       ('hide').
-- * @beffs@ — signatures to /b/ypass     ('withFwds').
-- * @feffs@ — signatures to /f/use       ('generalFuse').
-- * @ieffs@ — signatures to /i/ntercept  ('generalFuse', paired with @feffs@).

-- | A t'Handler' will process input effects @effs@ and produce output effects
-- @oeffs@, while working with a list of monad transformers @ts@. The final value
-- will be wrapped with @fs@.

type Handler
  :: [Effect]                             -- ^ effs  : input effects
  -> [Effect]                             -- ^ oeffs : output effects
  -> [(Type -> Type) -> (Type -> Type)]   -- ^ ts    : a list of carrier transformers
  -> Type                                 -- ^ a     : input type
  -> Type                                 -- ^ b     : output type
  -> Type

data Handler effs oeffs ts a b =
  Handler
  { -- | Given @oeffs@-effects on any monad @m@, run @Apply ts m a@ to obtain @m b@.
    -- This is the place for doing initialisation/finalisation work for a handler.
    hrun :: Runner oeffs ts a b Monad

    -- | Handling @effs@-effects using @oeffs@-effects by transforming
    -- @effs@-effects on any monad @m@ to @effs@-effects on @Apply ts m@.
  , halg :: AlgTrans effs oeffs ts Monad
  }

-- | Staged version of handlers.
type HandlerC
  :: [Effect]                             -- ^ effs  : input effects
  -> [Effect]                             -- ^ oeffs : output effects
  -> [(Type -> Type) -> (Type -> Type)]   -- ^ ts    : a list of carrier transformers
  -> Type                                 -- ^ a     : input type
  -> Type                                 -- ^ b     : output type
  -> Type

data HandlerC effs oeffs ts a b =
  HandlerC
  { -- | Given @oeffs@-effects on any monad @m@, running the monad transformer stack
    -- @ts m x@ into @m (fs x)@.
    hrunC :: RunnerC oeffs ts a b Monad

    -- | Transforming @oeffs@-effects on any monad @m@ to @effs@-effects on @ts m@.
  , halgC :: AlgTransC effs oeffs ts Monad
  }

-- * Handler Combinators

-- | A wrapper of the @Handler@ constructor.
{-# INLINE handler #-}
handler
  :: forall effs oeffs ts a b.
     (forall m. Monad m => Algebra oeffs m -> Apply ts m a -> m b)
     -- ^ Runner
  -> (forall m. Monad m => Algebra oeffs m -> Algebra effs (Apply ts m))
     -- ^ Algebra transformer
  -> Handler effs oeffs ts a b
handler run alg = Handler (Runner run) (AlgTrans alg)

-- | Given @hrun@ and @halg@, constructs a @Handler effs oeffs ts fs@. This
-- is a simplified version of the @Handler@ constructor where @run@ and @alg@ do
-- not need output effects.
{-# INLINE handler' #-}
handler'
  :: (forall m. Monad m => Apply ts m a -> m b)
     -- ^ Runner
  -> (forall m. Monad m => Algebra effs (Apply ts m))
     -- ^ Algebra
  -> Handler effs oeffs ts a b
handler' run alg = Handler (Runner (\_ -> run)) (AlgTrans (\(_ :: Algebra oeffs m) -> alg @m))

-- | A handler that handles nothing. This function is supposed to be used with `<:` by
-- @a1 <: a2 <: a3 <: ... <: fromRunner r@.
{-# INLINE fromRunner #-}
fromRunner
  :: forall ts a b. (forall m. Monad m => Apply ts m a -> m b) -- ^ Runner
  -> Handler '[] '[] ts a b
fromRunner run = Handler (Runner (\_ -> run)) (AlgTrans (const emptyAlg))

-- | Adding an algebra transformer to an existing handler. This function is supposed to be used with 
-- `fromRunner` by @a1 <: a2 <: a3 <: ... <: fromRunner r@.
{-# INLINE (<:) #-}
infixr <:
(<:)
  :: forall effs oeffs effs' oeffs' ts a b.
     UnionAT# effs effs' oeffs oeffs'
  => AlgTrans effs oeffs ts Monad               -- ^ Algebra transformer to add
  -> Handler effs' oeffs' ts a b                -- ^ Handler to extend
  -> Handler (effs `Union` effs') (oeffs `Union` oeffs') ts a b
algs <: Handler hrun halg = Handler (weakenREffs hrun) (weakenCS (algs `unionAT` halg))

-- | The identity handler that doesn't transform the effects.
{-# INLINE identity #-}
identity :: Handler effs effs '[] a a
identity = Handler idRunner idAT

type Comp# effs1 ts1 ts2 = (CompR# ts1 ts2 , CompAT# ts1 ts2)

-- | Compose two handlers.
{-# INLINE comp #-}
comp
  :: ( forall m. Monad m => MonadApply ts2 m
     , Comp# effs1 ts1 ts2 )
  => Handler effs1 effs2 ts1 a1 a2
     -- ^ The first handler
  -> Handler effs2 effs3 ts2 a2 a3
     -- ^ The second handler
  -> Handler effs1 effs3 (ts1 :++ ts2) a1 a3
comp (Handler r1 a1) (Handler r2 a2) =
  Handler (weakenRCSMonad (compR a2 r1 r2)) (weakenCSMonad (compAT a1 a2))

-- | Weakens a handler from @Handler effs oeffs ts fs@ to @Handler effs' oeffs' ts fs@,
-- when @effs'@ injects into @effs@ and @oeffs@ injects into @oeffs'@.
{-# INLINE weaken #-}
weaken
  :: forall effs effs' oeffs oeffs' ts a b.
     ( Members effs' effs , Members oeffs oeffs' )
  => Handler effs  oeffs  ts a b     -- ^ Handler to weaken
  -> Handler effs' oeffs' ts a b
weaken (Handler run halg)
  = Handler (weakenR @_ @oeffs' run) (weakenEffs halg)

type Hide# heffs effs oeffs = (Members (effs :\\ heffs) effs, Members oeffs oeffs)

-- | Hides the effects in @heffs@ from the handler. The type argument @heffs@
-- must be given explicitly since it is only mentioned inside a non-injective
-- type family `:\\`.
{-# INLINE hide #-}
hide
  :: forall heffs effs oeffs ts a b.
     Hide# heffs effs oeffs
  => Proxy heffs                    -- ^ Effects to hide
  -> Handler effs oeffs ts a b      -- ^ Handler to hide effects from
  -> Handler (effs :\\ heffs) oeffs ts a b
hide _ h = weaken h

type Bypass# beffs effs oeffs =
  ( Members (beffs :\\ effs) beffs
  , Members beffs beffs
  , Members effs effs
  , Members oeffs (oeffs `Union` beffs)
  , Members beffs (oeffs `Union` beffs) )

-- | Operations from the output effect @oeffs@ of a handler can be added
-- to the input effect if the handler can forward it.
{-# INLINE withFwds #-}
withFwds
  :: forall beffs effs oeffs ts a b.
     ( ForwardsM beffs ts
     , Bypass# beffs effs oeffs )
  => Proxy beffs                                      -- ^ Effects to bypass
  -> Handler effs oeffs ts a b                        -- ^ Handler
  -> Handler (effs `Union` beffs) (oeffs `Union` beffs) ts a b
withFwds _ (Handler run alg) = Handler (weakenR run) (withFwdsAT (Proxy @beffs) alg)

-- | An algebra transformer that doesn't transform the carrier can be
-- regarded as a handler trivially.
{-# INLINE fromAT #-}
fromAT :: AlgTrans effs oeffs '[] Monad -> Handler effs oeffs '[] a a
fromAT at = handler (\_ -> id) (getAT at)

-- | Interpret @effs@-effects using @oeffs@-effects without transforming the carrier.
-- This is done by using the supplied @rephrase@ parameter to translate @effs@
-- into a program that uses @oeffs@.
--
-- The function `interpret` is most useful for algebraic operations. For other families
-- of operations, `interpretM` is more useful.
{-# INLINE interpret #-}
interpret
  :: forall effs oeffs a.
     (forall m x . Case effs m x (Prog oeffs x))   -- ^ @rephrase@
  -> Handler effs oeffs '[] a a
interpret = fromAT . interpretAT

-- | A special case of `interpret` for one effect @eff@.
{-# INLINE interpret1 #-}
interpret1
  :: forall eff oeffs a.
     (forall m x. eff m x -> Prog oeffs x)   -- ^ Effect rephrasing function
  -> Handler '[eff] oeffs '[] a a
interpret1 rephrase = interpret (rephrase :% emptyCase)

{-# INLINE interpretM #-}
-- | A generalisation of `interpret` for non-algebraic operations.
-- The result of @interpretM mrephrase@ is a new @Handler effs oeffs '[] '[]@.
-- This is created by using the supplied @mrephrase@ parameter
-- to rephrase @effs@ into an arbitrary monad @m@.
-- When @mrephrase@ is used, it is given an @oalg :: Algebra oeffs m@
-- parameter that makes it possible to create a value in @m@.
interpretM
  :: forall effs oeffs a .
     (forall m. Monad m => Algebra oeffs m
                        -> Algebra effs m)   -- ^ @mrephrase@
  -> Handler effs oeffs '[] a a
interpretM mrephrase
  = handler @effs @oeffs @'[] (const id) mrephrase

-- | Staged version of `interpretM`.
interpretMC
  :: forall effs oeffs a .
     (forall m. Monad m => AlgebraC oeffs m
                         -> AlgebraC effs m)   -- ^ @mrephrase@
  -> HandlerC effs oeffs '[] a a
interpretMC mrephrase
  = HandlerC (RunnerC $ \_ -> [|| id ||]) (AlgTransC mrephrase)

-- | Interpreting one operation.
{-# INLINE interpretM1 #-}
interpretM1
  :: forall eff oeffs a.
     (forall m. Monad m => Algebra oeffs m
                        -> (forall x . eff m x -> m x))   -- ^ @mrephrase@
  -> Handler '[eff] oeffs '[] a a
interpretM1 mrephrase
  = handler @'[eff] @oeffs @'[] (const id) (\oalg -> mrephrase oalg :# emptyAlg)

-- | Staged version of `interpretM1`
interpretM1C
  :: forall eff oeffs a .
     (forall m. Monad m => AlgebraC oeffs m
                        -> CodeQ (eff m -.> m))   -- ^ @mrephrase@
  -> HandlerC '[eff] oeffs '[] a a
interpretM1C mrephrase
  = HandlerC (RunnerC $ \_ -> [|| id ||]) (AlgTransC (\oalgc -> mrephrase oalgc :#$ emptyAlgC ))

-- | Case splitting on the union of two effect rows. Note that `Union` is defined
-- to be @effs1 ++ (effs2 :\\ effs1)@, so if an effect @e@ is both a member of @effs1@
-- and @effs2@, it is consumed by the first handler.
{-# INLINE caseHdl #-}
caseHdl
  :: forall effs1 effs2 oeffs ts a1 a2 a3 a4.
     CaseTrans# effs1 effs2
  => Handler effs1 oeffs ts a1 a2
     -- ^ The first handler
  -> Handler effs2 oeffs ts a3 a4
     -- ^ The second handler
  -> Handler (effs1 `Union` effs2) oeffs ts a1 a2
caseHdl (Handler r1 a1) (Handler _ a2) = Handler r1 (caseATsameCS a1 a2)

-- | Case splitting on the union of two effect rows, and the two handlers may output
-- different effects. The runner of the resulting handler is the runner of the argument.
{-# INLINE unionHdl #-}
unionHdl
  :: forall effs1 effs2 oeffs1 oeffs2 ts a1 a2 a3 a4.
     UnionAT# effs1 effs2 oeffs1 oeffs2
  => Handler effs1 oeffs1 ts a1 a2
     -- ^ The first handler
  -> Handler effs2 oeffs2 ts a3 a4
     -- ^ The second handler
  -> Handler (effs1 `Union` effs2) (oeffs1 `Union` oeffs2) ts a1 a2
unionHdl (Handler r1 a1) (Handler _ a2) = Handler (weakenR r1) (weakenCS (unionAT a1 a2))

-- | Case splitting on the union of two effect rows, and the two handlers may output
-- different effects.
{-# INLINE unionHdlAT #-}
unionHdlAT
  :: forall effs1 effs2 oeffs1 oeffs2 ts a1 a2 a3 a4.
     UnionAT# effs1 effs2 oeffs1 oeffs2
  => Handler  effs1 oeffs1 ts a1 a2
     -- ^ Handler
  -> AlgTrans effs2 oeffs2 ts Monad
     -- ^ Algebra transformer to combine with the handler
  -> Handler (effs1 `Union` effs2) (oeffs1 `Union` oeffs2) ts a1 a2
unionHdlAT (Handler r1 a1) a2 = Handler (weakenR r1) (weakenCS (unionAT a1 a2))

-- | Case splitting on the append of two effect rows, and the two handlers may output
-- different effects.
{-# INLINE appendHdl #-}
appendHdl
  :: forall effs1 effs2 oeffs1 oeffs2 ts a1 a2 a3 a4.
     AppendAT# effs1 effs2 oeffs1 oeffs2
  => Handler effs1 oeffs1 ts a1 a2
     -- ^ The first handler
  -> Handler effs2 oeffs2 ts a3 a4
     -- ^ The second handler
  -> Handler (effs1 :++ effs2) (oeffs1 :++ oeffs2) ts a1 a2
appendHdl (Handler r1 a1) (Handler _ a2) = Handler (weakenR r1) (weakenCS (appendAT a1 a2))

-- | The combinator @h1 |> h2@ is an archetype of handler fusion. Its property is that
-- @
--    handleP h2 (handleP h1 prog) = handleP (h1 |> h2) prog
-- @
-- Explicitly, fusing handlers @h1 :: Handler effs1 oeffs1 ts1 fs1@ and @h2 ::
-- Handler effs2 oeffs2 ts2 fs2@ results in a handler that can deal with the
-- effects of @effs1@ and those of @effs2@, as well as deal with the effects
-- @oeffs1@ produced by @h1@ using @h2@ appropriately. More precisely, if a
-- member of @oeffs1@ is in @effs2@, then it is consumed by @h2@; if it is not
-- in @effs2@, it can only be reproduced by the fused handler, and in this case
-- it has to be forwardable by @ts2@. Moreover, the effects @effs2@ are
-- handled by @h2@ so they must be forwardable by @ts1@.
infixr 9 `fuse`, |>
{-# INLINE fuse #-}
{-# INLINE (|>) #-}
fuse, (|>)
  :: forall effs1 effs2 oeffs1 oeffs2 ts1 ts2 a1 a2 a3.
     ( forall m. Monad m => MonadApply ts2 m
     , ForwardsM effs2 ts1
     , ForwardsM (oeffs1 :\\ effs2) ts2
     , FuseAT# effs1 effs2 oeffs1 oeffs2 ts1 ts2
     , FuseR# effs2 oeffs1 oeffs2 ts1 ts2 )
  => Handler effs1 oeffs1 ts1 a1 a2   -- ^ @h1@
  -> Handler effs2 oeffs2 ts2 a2 a3   -- ^ @h2@
  -> Handler (effs1 `Union` effs2)
             ((oeffs1 :\\ effs2) `Union` oeffs2)
             (ts1 :++ ts2)
             a1 a3
fuse (Handler run1 malg1) (Handler run2 malg2)
  = Handler (weakenRCSMonad (fuseR malg2 run1 run2)) (weakenCSMonad (fuseAT malg1 malg2))

-- | A synonym for `fuse`.
(|>) = fuse

-- | Staged version of `fuse`
infixr 9 `fuseC`, |>$
fuseC, (|>$)
  :: forall effs1 effs2 oeffs1 oeffs2 ts1 ts2 a1 a2 a3.
     ( forall m. Monad m => MonadApply ts2 m
     , ForwardsM effs2 ts1
     , ForwardsM (oeffs1 :\\ effs2) ts2
     , FuseAT# effs1 effs2 oeffs1 oeffs2 ts1 ts2
     , FuseR# effs2 oeffs1 oeffs2 ts1 ts2 )
  => HandlerC effs1 oeffs1 ts1 a1 a2 -- ^ @h1@
  -> HandlerC effs2 oeffs2 ts2 a2 a3 -- ^ @h2@
  -> HandlerC (effs1 `Union` effs2)
              ((oeffs1 :\\ effs2) `Union` oeffs2)
              (ts1 :++ ts2)
              a1 a3
fuseC (HandlerC run1 malg1) (HandlerC run2 malg2)
  = HandlerC (weakenRCSCMonad (fuseRC malg2 run1 run2)) (weakenCSCMonad (fuseATC malg1 malg2))

(|>$) = fuseC

-- | A variant of `fuse` that works with @:++@ instead of @Union@.
infixr 9 `fuseApp`, ++>
{-# INLINE fuseApp #-}
fuseApp, (++>)
  :: forall effs1 effs2 oeffs1 oeffs2 ts1 ts2 a1 a2 a3.
     ( forall m. Monad m => MonadApply ts2 m
     , CompAT# ts1 ts2, KnownEffs oeffs1
     , ForwardsM effs2 ts1, ForwardsM oeffs1 ts2 )
  => Handler effs1 oeffs1 ts1 a1 a2   -- ^ @h1@
  -> Handler effs2 oeffs2 ts2 a2 a3   -- ^ @h2@
  -> Handler (effs1 :++ effs2)
             (oeffs1 :++ oeffs2)
             (ts1 :++ ts2)
             a1 a3
fuseApp (Handler run1 malg1) (Handler run2 malg2)
  = Handler (weakenRCSMonad (fuseAppR malg2 run1 run2)) (weakenCSMonad (fuseAppAT malg1 malg2))

(++>) = fuseApp

-- | Staged version of `fuseApp`.
infixr 9 `fuseAppC`, ++>$
fuseAppC, (++>$)
  :: forall effs1 effs2 oeffs1 oeffs2 ts1 ts2 a1 a2 a3.
     ( forall m. Monad m => MonadApply ts2 m
     , CompAT# ts1 ts2
     , ForwardsM effs2 ts1, ForwardsM oeffs1 ts2
     , KnownEffs oeffs1 )
  => HandlerC effs1 oeffs1 ts1 a1 a2   -- ^ @h1@
  -> HandlerC effs2 oeffs2 ts2 a2 a3   -- ^ @h2@
  -> HandlerC (effs1 :++ effs2)
              (oeffs1 :++ oeffs2)
              (ts1 :++ ts2)
              a1 a3
fuseAppC (HandlerC run1 malg1) (HandlerC run2 malg2)
  = HandlerC (weakenRCSCMonad (fuseAppRC run1 run2)) (weakenCSCMonad (fuseAppATC malg1 malg2))

(++>$) = fuseAppC

-- | Piping two handlers @h1@ and @h2@ is like 'subtraction of handlers': @h2@ handles
-- the effects produced by @h1@, but it does not handle any 'upstream effects'. For this reason
-- the operator @\\@ is left associated.
infixl 9 `pipe`
{-# INLINE pipe #-}
{-# INLINE (\\) #-}
pipe, (\\)
  :: forall effs1 effs2 oeffs1 oeffs2 ts1 ts2 a1 a2 a3.
     ( forall m. Monad m => MonadApply ts2 m
     , PipeAT# effs2 oeffs1 oeffs2 ts1 ts2
     , FuseR# effs2 oeffs1 oeffs2 ts1 ts2
     , ForwardsM (oeffs1 :\\ effs2) ts2 )
  => Handler effs1 oeffs1 ts1 a1 a2    -- ^ @h1@
  -> Handler effs2 oeffs2 ts2 a2 a3    -- ^ @h2@
  -> Handler effs1
             ((oeffs1 :\\ effs2) `Union` oeffs2)
             (ts1 :++ ts2)
             a1 a3
pipe (Handler run1 malg1)  (Handler run2 malg2)
  = Handler (weakenRCSMonad (fuseR malg2 run1 run2)) (weakenCSMonad (pipeAT malg1 malg2))

-- | A synonym for 'pipe'
(\\) = pipe

-- | Static version of `pipe`.
pipeC, (\\$)
  :: forall effs1 effs2 oeffs1 oeffs2 ts1 ts2 a1 a2 a3.
     ( forall m. Monad m => MonadApply ts2 m
     , PipeAT# effs2 oeffs1 oeffs2 ts1 ts2
     , FuseR# effs2 oeffs1 oeffs2 ts1 ts2
     , ForwardsM (oeffs1 :\\ effs2) ts2 )
  => HandlerC effs1 oeffs1 ts1 a1 a2   -- ^ @h1@
  -> HandlerC effs2 oeffs2 ts2 a2 a3   -- ^ @h2@
  -> HandlerC effs1
              ((oeffs1 :\\ effs2) `Union` oeffs2)
              (ts1 :++ ts2)
              a1 a3
pipeC (HandlerC run1 malg1) (HandlerC run2 malg2)
  = HandlerC (weakenRCSCMonad (fuseRC malg2 run1 run2)) (weakenCSCMonad (pipeATC malg1 malg2))

-- | A synonym for 'pipe'
(\\$) = pipeC

type Pass# effs1 effs2 oeffs1 oeffs2 ts1 ts2 =
  ( PassAT# effs1 effs2 oeffs1 oeffs2 ts1 ts2 Monad
  , FuseR# effs2 oeffs1 oeffs2 ts1 ts2
  , Members (oeffs1 `Union` oeffs2) (oeffs1 `Union` oeffs2))

-- | @pass h1 h2@ results in a handler that handles all the effects handled by
-- @h1@ and @h2@, but unlike @fuse@, @pass@ doesn't use @h2@ to handle the
-- effects produced by @h1@.
pass
  :: forall effs1 effs2 oeffs1 oeffs2 ts1 ts2 a1 a2 a3.
     ( forall m. Monad m => MonadApply ts2 m
     , ForwardsM  effs2 ts1
     , ForwardsM oeffs1 ts2
     , Pass# effs1 effs2 oeffs1 oeffs2 ts1 ts2 )
  => Handler effs1 oeffs1 ts1 a1 a2         -- ^ @h1@
  -> Handler effs2 oeffs2 ts2 a2 a3         -- ^ @h2@
  -> Handler (effs1 `Union` effs2)
             (oeffs1 `Union` oeffs2)
             (ts1 :++ ts2)
             a1 a3
pass (Handler r1 a1) (Handler r2 a2)
  = Handler (weakenRCSMonad (passR r1 r2)) (weakenCSMonad (passAT a1 a2))

-- | `generalFuse` subsumes @fuse@, @pass@, and @pipe@ by having two type arguments
-- @feffs@ and @ieffs@ such that
--   1. @feffs@ is a subset of @effs2@ and it specifies the effects that we want to be
--      forwarded along @ts1@ and exposed by the resulting handler;
--   2. @ieffs@ is a subset of @effs2@ and it specifies the effects that we want to
--      use to intercept the effects produced by @h1@.
-- Therefore @generalFuse@ instantiates to
--   1. `fuse` with @feffs ~ effs2@ and @ieffs ~ effs2@,
--   2. `pipe` with @feffs ~ []@    and @ieffs ~ effs2@,
--   3. `pass` with @feffs ~ effs2@ and @ieffs ~ []@.
-- (When both @feffs@ and @ieffs@ are empty, @generalFuse@ becomes useless so there
-- isn't this case defined specially.)

{-# INLINE generalFuse #-}
generalFuse
  :: forall feffs ieffs effs1 effs2 oeffs1 oeffs2 ts1 ts2 a1 a2 a3.
     ( forall m. Monad m => MonadApply ts2 m
     , Members feffs effs2
     , Members ieffs effs2
     , ForwardsM feffs ts1
     , ForwardsM (oeffs1 :\\ ieffs) ts2
     , GeneralFuseAT# feffs ieffs effs1 effs2 oeffs1 oeffs2 ts1 ts2 )
  => Proxy feffs
     -- ^ Effects to be forwarded
  -> Proxy ieffs
     -- ^ Intercepted effects
  -> Handler effs1 oeffs1 ts1 a1 a2
     -- ^ The first handler
  -> Handler effs2 oeffs2 ts2 a2 a3
     -- ^ The second handler
  -> Handler (effs1 `Union` feffs)
             ((oeffs1 :\\ ieffs) `Union` oeffs2)
             (ts1 :++ ts2)
             a1 a3
generalFuse p1 p2 (Handler r1 a1) (Handler r2 a2)
  = Handler (weakenRCSMonad (fuseR (weakenIEffs @ieffs a2) r1 r2))
            (weakenCSMonad (generalFuseAT p1 p2 a1 a2))

-- * Applying Handlers

-- | @handle h p@ uses the handler @h@ to evaluate the program @p@. All of the
-- effects @effs@ in the program must be handled by the handler, and the handler
-- must produce no effects.

{-# INLINE handle #-}
handle
  :: forall effs ts a b.
     (Monad (Apply ts Identity))
  => Handler effs '[] ts a b      -- ^ Handler @h@ with no output effects
  -> Prog effs a                  -- ^ Program @p@ with effects @effs@
  -> b
handle (Handler run halg)
  = runIdentity . getR run emptyAlg. eval (getAT halg (emptyAlg @Identity))

-- | Static version of `handle`
handleC
  :: forall effs ts a b.
     (Monad (Apply ts Identity))
  => HandlerC effs '[] ts a b     -- ^ Handler with no output effects
  -> CodeQ (Prog effs a)          -- ^ Program to be handled
  -> CodeQ b
handleC (HandlerC (RunnerC r) (AlgTransC a)) p =
  [||
      let alg = $$(genAlgebra (a @Identity emptyAlgC))
      in runIdentity ($$(r emptyAlgC) (eval' alg $$p))
  ||]

type HandleM# effs xeffs =
  ( Members (xeffs :\\ effs) xeffs )

-- | @handleM xalg h p@ uses the handler @h@ to evaluate the program @p@ into some
-- monad @m@ (e.g. the @IO@ monad). The monad @m@ may come with some effects @xeffs@
-- and the program can make use of these effects, in addition to the effects @effs@
-- handled by the handler @h@. The effects @xeffs@ on @m@ must be forwardable by
-- the transformer stack @ts@.
-- (When an effect is both in @effs@ and @xeffs@, it is handled by @h@).
handleM
  :: forall effs oeffs xeffs m ts a b.
     ( Monad m
     , Monad (Apply ts m)
     , ForwardsM xeffs ts
     , Members oeffs xeffs
     , HandleM# effs xeffs )
  => Algebra xeffs m                 -- ^ Algebra @xalg@ for external effects @xeffs@
  -> Handler effs oeffs ts a b       -- ^ Handler @h@
  -> Prog (effs `Union` xeffs) a     -- ^ Program @p@ that contains @xeffs@
  -> m b
handleM xalg (Handler run halg)
  = getR run @m (weakenAlg xalg)
  . eval (unionAlg @effs @xeffs (getAT halg (weakenAlg xalg)) (getAT (fwds @_ @ts) xalg))

-- | Staged version of `handleM`.
handleMC
  :: forall effs oeffs xeffs m ts a b.
     ( Monad m
     , Monad (Apply ts m)
     , ForwardsM xeffs ts
     , Members oeffs xeffs
     , HandleM# effs xeffs )
  => AlgebraC xeffs m
     -- ^ Staged algebra for external effects
  -> HandlerC effs oeffs ts a b
     -- ^ Staged handler
  -> CodeQ (Prog (effs `Union` xeffs) a)
     -- ^ Program to be handled
  -> CodeQ (m b)
handleMC xalgC (HandlerC (RunnerC r) (AlgTransC a)) p =
  [||
      let xalg = $$(genAlgebra xalgC)
          alg = $$(genAlgebra (a (weakenAlgC xalgC) `unionAlgC` getATC (fwdsC @_ @ts) xalgC))
      in $$(r (weakenAlgC xalgC)) (eval alg $$p)
  ||]

-- | A variant of @handleM@ where the program doesn't explicitly use the effect
-- @xeffs@ on the monad @m@, but may output some effects @oeffs@ ⊆ @xeffs@. Therefore
-- the transformer stack @ts@ doesn't have to forward the effects @xeffs@.
handleM'
  :: forall effs oeffs xeffs m ts a b.
     ( Monad m
     , Monad (Apply ts m)
     , Members oeffs xeffs )
  => Algebra xeffs m                 -- ^ Algebra @xalg@ for external effects @xeffs@
  -> Handler effs oeffs ts a b       -- ^ Handler @h@
  -> Prog effs a                     -- ^ Program to be handled
  -> m b
handleM' xalg (Handler run halg)
  = getR run @m (weakenAlg xalg) . eval (getAT halg (weakenAlg xalg))

-- | A staged version of `handleM'`.
handleMC'
  :: forall effs oeffs xeffs m ts a b.
     ( Monad m
     , Monad (Apply ts m)
     , Members oeffs xeffs )
  => AlgebraC xeffs m
     -- ^ Staged algebra for external effects
  -> HandlerC effs oeffs ts a b
     -- ^ Staged handler
  -> CodeQ (Prog effs a)
     -- ^ Program to be handled
  -> CodeQ (m b)
handleMC' xalgC (HandlerC (RunnerC r) (AlgTransC a)) p =
  [||
      let xalg = $$(genAlgebra xalgC)
          alg = $$(genAlgebra (a (weakenAlgC xalgC)))
      in $$(r (weakenAlgC xalgC)) (eval alg $$p)
  ||]

-- | @handleMFwds@ sits in the middle of `handleM` and `handleM'` by having an explicit
-- argument @yeffs@ for the effects that should be forwarded to the program.
handleMFwds
  :: forall yeffs effs oeffs xeffs m ts a b.
     ( Monad m
     , Monad (Apply ts m)
     , Members oeffs xeffs
     , Members yeffs xeffs
     , ForwardsM yeffs ts
     , HandleM# effs yeffs )
  => Proxy yeffs                    -- ^ @yeffs@ can't be inferred, so it must be given explicitly
  -> Algebra xeffs m                -- ^ Algebra @xalg@ for external effects @xeffs@
  -> Handler effs oeffs ts a b      -- ^ Handler @h@
  -> Prog (effs `Union` yeffs) a    -- ^ Program to be handled
  -> m b
handleMFwds _ xalg (Handler run halg)
  = getR run @m (weakenAlg xalg)
  . eval (unionAlg @effs @yeffs (getAT halg (weakenAlg xalg))
                              (getAT (fwds @_ @ts) (weakenAlg xalg)))

-- | Staged version of @handleMFwdsC@.
handleMFwdsC
  :: forall yeffs effs oeffs xeffs m ts a b.
     ( Monad m
     , Monad (Apply ts m)
     , Members oeffs xeffs
     , Members yeffs xeffs
     , ForwardsM yeffs ts
     , HandleM# effs yeffs )
  => Proxy yeffs
     -- ^ Effects to be forwarded
  -> AlgebraC xeffs m
     -- ^ Staged algebra for external effects
  -> HandlerC effs oeffs ts a b
     -- ^ Staged handler
  -> CodeQ (Prog (effs `Union` yeffs) a)
     -- ^ Program to be handled
  -> CodeQ (m b)
handleMFwdsC _ yalg (HandlerC (RunnerC r) (AlgTransC a)) p =
  [||
      let alg = $$(genAlgebra (a @m (weakenAlgC yalg)
                                 `unionAlgC`
                                  getATC (fwdsC @_ @ts) (weakenAlgC @yeffs yalg)))
      in ($$(r (weakenAlgC yalg)) (eval' alg $$p))
  ||]

-- | @handleMApp xalg h p@ is a variant of `handleM` where @effs `Union` xeffs@
-- is replaced by '(:++)'. In most cases, `handleM` should be used, but sometimes
-- limitations regarding class constraints in GHC necessitate the use of
-- @handleMApp@ (for example, in `Control.Effect.HStore.Safe.handleHSM`).

handleMApp
  :: forall effs oeffs xeffs m ts a b.
     ( Monad m
     , Monad (Apply ts m)
     , ForwardsM xeffs ts
     , Members oeffs xeffs )
  => Algebra xeffs m                -- ^ Algebra @xalg@ for external effects @xeffs@
  -> Handler effs oeffs ts a b      -- ^ Handler @h@
  -> Prog (effs :++ xeffs) a        -- ^ Program @p@ that contains @xeffs@
  -> m b
handleMApp xalg (Handler run halg)
  = getR run @m (weakenAlg xalg)
  . eval (appendAlg @effs @xeffs (getAT halg (weakenAlg xalg)) (getAT (fwds @_ @ts) xalg))

type HandleP# effs xeffs =
  ( HandleM# effs xeffs
  , Monad (Prog xeffs)
  , ProgAlg# xeffs )

-- | @handleP h p@ uses the handler @h@ to evaluate the program @p@, resulting
-- in a program with effects @xeffs@ that are not recognised by @h@.
-- If an effect is both in @effs@ and @xeffs@, it is handled by @h@.
handleP
  :: forall effs oeffs xeffs ts a b.
     ( Monad (Apply ts (Prog xeffs))
     , ForwardsM xeffs ts
     , Members oeffs xeffs
     , HandleP# effs xeffs )
  => Handler effs oeffs ts a b        -- ^ Handler @h@
  -> Prog (effs `Union` xeffs) a      -- ^ Program @p@ that contains @xeffs@
  -> Prog xeffs b
handleP = handleM progAlg

-- | A variant of @handleP'@ where the program only uses the effects provided
-- by the handler @h@.
handleP'
  :: forall effs oeffs xeffs ts a b.
     ( Monad (Apply ts (Prog xeffs))
     , Members oeffs xeffs
     , ProgAlg# xeffs )
  => Handler effs oeffs ts a b       -- ^ Handler @h@
  -> Prog effs a                     -- ^ Program @p@ that contains @xeffs@
  -> Prog xeffs b

handleP' = handleM' progAlg

-- | @handlePApp h p@ is a variant of `handleP` where @effs `Union` xeffs@ is
-- replaced by simply '(:++)'.  In most cases, you should just use `handleP` but
-- sometimes limitations regarding class constraints in GHC necessitate the use
-- of @handleP'@ (for example, in `Control.Effect.HStore.Safe.handleHSM`.)
handlePApp
  :: forall effs oeffs xeffs ts a b.
     ( ForwardsM xeffs ts
     , Monad (Apply ts (Prog xeffs))
     , Members oeffs xeffs
     , ProgAlg# xeffs )
  => Handler effs oeffs ts a b        -- ^ Handler @h@
  -> Prog (effs :++ xeffs) a          -- ^ Program @p@ that contains @xeffs@
  -> Prog xeffs b
handlePApp = handleMApp progAlg