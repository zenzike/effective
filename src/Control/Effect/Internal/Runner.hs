{-|
Module      : Control.Effect.Internal.Runner
Description :
License     : BSD-3-Clause
Maintainer  : Nicolas Wu, Zhixuan Yang
Stability   : experimental
-}
{-# LANGUAGE ImpredicativeTypes, QuantifiedConstraints, UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses, MonoLocalBinds, LambdaCase, BlockArguments #-}
{-# LANGUAGE PartialTypeSignatures, MagicHash #-}
{-# OPTIONS_GHC -Wno-partial-type-signatures #-}

module Control.Effect.Internal.Runner where

import Data.List.Kind
import Data.Kind


import Control.Effect.Internal.Effs
import Control.Effect.Internal.AlgTrans.Type
import Control.Effect.Internal.Forward


-- * The primitive types for modular effect handlers

-- | Running a computation @ts m a@, resulting in a value @m b@
type Runner
  :: [Effect]                             -- ^ oeffs : output effects
  -> [(Type -> Type) -> (Type -> Type)]   -- ^ ts    : carrier transformer
  -> Type                                 -- ^ a     : input type
  -> Type                                 -- ^ b     : output type
  -> ((Type -> Type) -> Constraint)       -- ^ cs    : carrier constraint
  -> Type
newtype Runner oeffs ts a b cs = Runner {
  getR :: forall m . cs m => Algebra oeffs m -> Apply ts m a -> m b }


-- * Building runners

-- | Runners that don't need any output effects.
{-# INLINE runner' #-}
runner' :: (forall m x . cs m => Apply ts m a -> m b)
        -> Runner oeffs ts a b cs
runner' run = Runner (\(_ :: Algebra _ m) -> run @m)

{-# INLINE idRunner #-}
idRunner :: forall effs cs a.
            Runner effs '[] a a cs
idRunner = Runner \_ x -> x


type CompRunner# ts1 ts2 =
   ( forall m. Assoc ts1 ts2 m :: Constraint )

{-# INLINE compRunner #-}
compRunner :: forall effs1 effs2 ts1 ts2 a1 a2 a3 cs1 cs2.
              CompRunner# ts1 ts2
           => AlgTrans effs1 effs2 ts2 cs2
           -> Runner effs1 ts1 a1 a2 cs1
           -> Runner effs2 ts2 a2 a3 cs2
           -> Runner effs2 (ts1 :++ ts2)
                           a1 a3
                           (CompC ts2 cs1 cs2)
compRunner at r1 r2 = Runner \(oalg :: Algebra _ m) ->
    getR r2 oalg .  getR r1 (getAT at @m oalg)

type FuseR# effs2 oeffs1 oeffs2 ts1 ts2 =
  ( Injects (oeffs1 :\\ effs2) ((oeffs1 :\\ effs2) `Union` oeffs2)
  , Injects oeffs2 ((oeffs1 :\\ effs2) `Union` oeffs2)
  , Injects oeffs1 ((oeffs1 :\\ effs2) :++ effs2)
  , Append (oeffs1 :\\ effs2) effs2
  , CompRunner# ts1 ts2 )

{-# INLINE fuseR #-}
fuseR :: forall effs2 oeffs1 oeffs2 ts1 ts2 a1 a2 a3 cs1 cs2.
          ( ForwardsC cs2 (oeffs1 :\\ effs2) ts2
          , FuseR# effs2 oeffs1 oeffs2 ts1 ts2 )
       => AlgTrans effs2 oeffs2 ts2 cs2
       -> Runner oeffs1 ts1 a1 a2 cs1
       -> Runner oeffs2 ts2 a2 a3 cs2
       -> Runner ((oeffs1 :\\ effs2) `Union` oeffs2)
                 (ts1 :++ ts2)
                 a1 a3
                 (CompC ts2 cs1 cs2)
fuseR at2 r1 r2 = Runner \(oalg :: Algebra _ m)  ->
      getR r2 (oalg . injs)
    . getR r1 (weakenAlg @oeffs1 @((oeffs1 :\\ effs2) :++ effs2) $
        heither @(oeffs1 :\\ effs2) @effs2
          (getAT (fwds @(oeffs1 :\\ effs2) @(ts2))
            (weakenAlg @(oeffs1 :\\ effs2) @_ oalg))
          (getAT at2 (weakenAlg @oeffs2 @_ oalg)))

type PassR# effs2 oeffs1 oeffs2 ts1 ts2 a1 a2 a3 =
   ( Injects oeffs1 (oeffs1 `Union` oeffs2)
   , Injects oeffs2 (oeffs1 `Union` oeffs2)
   , CompRunner# ts1 ts2)

{-# INLINE passR #-}
passR :: forall effs2 oeffs1 oeffs2 ts1 ts2 a1 a2 a3 cs1 cs2.
      ( ForwardsC cs2 oeffs1 ts2
      , PassR# effs2 oeffs1 oeffs2 ts1 ts2 a1 a2 a3)
      => AlgTrans effs2 oeffs2 ts2 cs2
      -> Runner oeffs1 ts1 a1 a2 cs1
      -> Runner oeffs2 ts2 a2 a3 cs2
      -> Runner (oeffs1 `Union` oeffs2)
                (ts1 :++ ts2)
                a1 a3
                (CompC ts2 cs1 cs2)
passR at2 r1 r2 = Runner \(oalg :: Algebra _ m)  ->
      getR r2 (oalg . injs)
    . getR r1 (getAT (fwds @oeffs1 @ts2) (oalg . injs))

{-# INLINE weakenR #-}
weakenR :: forall cs' effs' cs effs ts a b.
           (forall m. cs' m => cs m, Injects effs effs')
        => Runner effs ts a b cs
        -> Runner effs' ts  a b cs'
weakenR r1 = Runner \oalg -> getR r1 (oalg . injs)

{-# INLINE weakenREffs #-}
weakenREffs :: forall effs' cs effs ts a b.
           (Injects effs effs')
        => Runner effs ts a b cs
        -> Runner effs' ts a b cs
weakenREffs r1 = Runner \oalg -> getR r1 (oalg . injs)

{-# INLINE weakenRC #-}
weakenRC :: forall cs' cs effs ts a b.
           (forall m. cs' m => cs m)
        => Runner effs ts a b cs
        -> Runner effs ts a b cs'
weakenRC r1 = Runner \oalg -> getR r1 oalg
