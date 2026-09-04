{-|
Module      : Control.Effect.Alternative
Description : Effects for alternatives with choose and empty
License     : BSD-3-Clause
Maintainer  : Nicolas Wu
Stability   : experimental

This module provides operations corresponding to the `Alternative` typeclass of
Haskell. Two operations t`Empty` and t`Choose` are defined, corresponding to
`Ap.empty` and `Ap.<|>` of `Alternative` respectively. The monad `Prog effs`
also instantiates `Alternative`.

In this library there is another module "Control.Effect.Nondet" that provides
some additional operations for nondeterminism. See the documentation in
"Control.Effect.Nondet" for more explanation.
-}

{-# LANGUAGE QuantifiedConstraints #-}

module Control.Effect.Nondet.Alternative (
  -- * Syntax
  -- ** Operations

  -- | The operations for alternatives use 'empty' and '<|>' directly
  -- from the 'Control.Applicative.Alternative' type class.
  --
  -- 'empty' is an algebraic operation:
  --
  -- > empty >>= k = empty
  --
  -- '<|>' is a scoped operation.
  Ap.empty, emptyP, emptyM,
  (<|>), chooseP, chooseM,
#if MIN_VERSION_GLASGOW_HASKELL(9,10,1,0)
  emptyN, chooseN,
#endif
  select, selects,

  -- ** Signatures
  Empty, Empty_(..), pattern Empty,
  Choose, Choose_(..), pattern Choose,

  -- * Semantics
  -- ** Handlers
  alternative, alternativeC,
  list, listC,
  logic, logicC,
  chooseByNondet,
  nondetByChoose,

  -- ** Algebras
  alternativeAT, alternativeATC,

  -- ** Re-exported carriers
  Li.ListT (..),
  Lo.LogicT (..)
) where

import Control.Effect hiding (emptyAlg)
import Control.Effect.Nondet.Operations

import Control.Applicative ((<|>), Alternative)
import Control.Applicative qualified as Ap

import qualified Control.Monad.Logic as Lo
import qualified Control.Monad.Trans.List as Li

-- | The 'alternative' handler makes use of an 'Alternative' functor @f@
-- as well as a transformer @t@ that produces an 'Alternative' functor @t m@
-- for any monad @m@ to provide semantics.
{-# INLINE alternative #-}
alternative
  :: forall t f a.
     (forall m. Monad m => Alternative (t m))
  => (forall m. Monad m => (forall a. t m a -> m (f a)))
  -> Handler '[Empty, Choose] '[] '[t] a (f a)
alternative run = Handler (runner' run) alternativeAT

-- | The algebra transformer underlying the 'alternative' handler. This uses an
-- underlying 'Alternative' instance for @t m@ given by a transformer @t@.
alternativeAT
  :: forall t.
     (forall m. Monad m => Alternative (t m))
  => AlgTrans '[Empty, Choose] '[] '[t] Monad
alternativeAT = algTrans' (emptyAlg :#. chooseAlg)

-- | Staged version of `alternativeAT`.
alternativeATC
  :: forall t.
     (forall m. Monad m => Alternative (t m))
  => AlgTransC '[Empty, Choose] '[] '[t] Monad
alternativeATC = AlgTransC $ \_ ->
  [|| NT emptyAlg ||] :#$ [|| NT chooseAlg ||] :#$ emptyAlgC

{-# INLINE emptyAlg #-}
emptyAlg :: Alternative (t m) => Empty (t m) x -> t m x
emptyAlg Empty = Ap.empty

{-# INLINE chooseAlg #-}
chooseAlg :: Alternative (t m) => Choose (t m) x -> t m x
chooseAlg (Choose xs ys) = xs <|> ys

-- | A specialisation of `alternative` to @ListT@
list :: Handler [Empty, Choose] '[] '[Li.ListT] a [a]
list = alternative Li.runListT'

-- | A specialisation of `alternative` to @LogicT@.
logic :: Handler [Empty, Choose] '[] '[Lo.LogicT] a [a]
logic = alternative Lo.observeAllT

-- | Staged version of `alternative`.
alternativeC
  :: forall t f a.
     (forall m. Monad m => Alternative (t m))
  => (forall m x. Monad m => CodeQ (t m x -> m (f x)))
  -> HandlerC '[Empty, Choose] '[] '[t] a (f a)
alternativeC run = HandlerC
  (RunnerC $ \_ -> run)
  alternativeATC

-- | Staged version of `list`
listC :: HandlerC [Empty, Choose] '[] '[Li.ListT] a [a]
listC = alternativeC [|| Li.runListT' ||]

-- | Staged version of `logic`
logicC :: HandlerC [Empty, Choose] '[] '[Lo.LogicT] a [a]
logicC = alternativeC [|| Lo.observeAllT ||]


-- | Translate (scoped) `Choose` operations to (algebraic) `Nondet` operations.
-- The scopes delimited by `Choose` are ignored.
chooseByNondet :: Handler '[Choose] '[NondetOr] '[] a a
chooseByNondet = interpretM1 (\oalg (Choose p q) -> nondetOrM oalg p q)

-- | Translate (algebraic) `Nondet` operations to (scoped) `Choose` operations.
nondetByChoose :: Handler '[NondetOr] '[Choose] '[] a a
nondetByChoose = interpretM1 (\oalg (NondetOr p q) -> chooseM oalg (return p) (return q))
