{-|
Module      : Control.Effect.Internal.Runner
Description : 
License     : BSD-3-Clause
Maintainer  : Nicolas Wu, Zhixuan Yang
Stability   : experimental
-}
{-# LANGUAGE ImpredicativeTypes, QuantifiedConstraints, UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses, MonoLocalBinds, LambdaCase, BlockArguments #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# OPTIONS_GHC -Wno-partial-type-signatures #-}

module Control.Effect.Internal.Runner where

import Data.List.Kind 
import Data.Kind


import Control.Effect.Internal.Effs
import Control.Effect.Internal.AlgTrans.Type
import Control.Effect.Internal.AlgTrans
import Control.Effect.Internal.Forward.ForwardC


-- * The primitive types for modular effect handlers

-- | Running a carrier transformer @ts@, resulting in a functor @fs@.
type Runner
  :: [Effect]                             -- ^ oeffs : output effects
  -> [(Type -> Type) -> (Type -> Type)]   -- ^ ts    : carrier transformer
  -> [Type -> Type]                       -- ^ fs    : result functor
  -> ((Type -> Type) -> Constraint)       -- ^ cs    : carrier constraint
  -> Type
newtype Runner oeffs ts fs cs = Runner {
  getR :: forall m . cs m => Algebra oeffs m -> (forall x . Apply ts m x -> m (Apply fs x)) }

-- | Runners for monads.
type RunnerM oeffs ts fs = Runner oeffs ts fs Monad 

{-# INLINE run #-}
run :: forall oeffs ts fs cs m x.
       cs m 
    => Runner oeffs ts fs cs 
    -> Algebra oeffs m 
    -> Apply ts m x -> m (Apply fs x)
run r oalg t = getR r oalg t 

-- * Building runners

{-# INLINE idRunner #-}
idRunner :: forall effs cs. 
            Runner effs '[] '[] cs
idRunner = Runner \_ x -> x


type AutoCompRunner ts1 ts2 fs1 fs2 = 
   ( forall m . Assoc ts1 ts2 m :: Constraint
   , forall x. Assoc fs2 fs1 x )

{-# INLINE compRunner #-}
compRunner :: forall effs1 effs2 ts1 ts2 fs1 fs2 cs1 cs2.
              AutoCompRunner ts1 ts2 fs1 fs2
           => AlgTrans effs1 effs2 ts2 cs2
           -> Runner effs1 ts1 fs1 cs1
           -> Runner effs2 ts2 fs2 cs2
           -> Runner effs2 (ts1 :++ ts2)
                           (fs2 :++ fs1)
                           (CompC ts2 cs1 cs2)
compRunner at r1 r2 = Runner \(oalg :: Algebra _ m) ->
    getR r2 oalg .  getR r1 (getAT at @m oalg)

type AutoFuseR effs2 oeffs1 oeffs2 ts1 ts2 fs1 fs2 =
  ( Injects (oeffs1 :\\ effs2) ((oeffs1 :\\ effs2) `Union` oeffs2)
  , Injects oeffs2 ((oeffs1 :\\ effs2) `Union` oeffs2)
  , Injects oeffs1 ((oeffs1 :\\ effs2) :++ effs2)
  , Append (oeffs1 :\\ effs2) effs2
  , AutoCompRunner ts1 ts2 fs1 fs2 )

{-# INLINE fuseR #-}
fuseR :: forall effs2 oeffs1 oeffs2 ts1 ts2 fs1 fs2 cs1 cs2.
          ( ForwardsC cs2 (oeffs1 :\\ effs2) ts2
          , AutoFuseR effs2 oeffs1 oeffs2 ts1 ts2 fs1 fs2 )
       => AlgTrans effs2 oeffs2 ts2 cs2
       -> Runner oeffs1 ts1 fs1 cs1 
       -> Runner oeffs2 ts2 fs2 cs2
       -> Runner ((oeffs1 :\\ effs2) `Union` oeffs2) 
                 (ts1 :++ ts2)
                 (fs2 :++ fs1)
                 (CompC ts2 cs1 cs2)
fuseR at2 r1 r2 = Runner \(oalg :: Algebra _ m)  ->
      getR r2 (oalg . injs)
    . getR r1 (weakenAlg @oeffs1 @((oeffs1 :\\ effs2) :++ effs2) $
        heither @(oeffs1 :\\ effs2) @effs2
          (getAT (fwdsC @cs2 @(oeffs1 :\\ effs2) @(ts2))
            (weakenAlg @(oeffs1 :\\ effs2) @_ oalg))
          (getAT at2 (weakenAlg @oeffs2 @_ oalg)))

type AutoPassR effs2 oeffs1 oeffs2 ts1 ts2 fs1 fs2 = 
   ( Injects oeffs1 (oeffs1 `Union` oeffs2)
   , Injects oeffs2 (oeffs1 `Union` oeffs2)
   , AutoCompRunner ts1 ts2 fs1 fs2 )

{-# INLINE passR #-}
passR :: forall effs2 oeffs1 oeffs2 ts1 ts2 fs1 fs2 cs1 cs2.
      ( ForwardsC cs2 oeffs1 ts2
      , AutoPassR effs2 oeffs1 oeffs2 ts1 ts2 fs1 fs2)
      => AlgTrans effs2 oeffs2 ts2 cs2
      -> Runner oeffs1 ts1 fs1 cs1 
      -> Runner oeffs2 ts2 fs2 cs2
      -> Runner (oeffs1 `Union` oeffs2) 
                (ts1 :++ ts2)
                (fs2 :++ fs1)
                (CompC ts2 cs1 cs2)
passR at2 r1 r2 = Runner \(oalg :: Algebra _ m)  ->
      getR r2 (oalg . injs)
    . getR r1 (getAT (fwdsC @cs2 @oeffs1 @ts2) (oalg . injs))

{-# INLINE weakenR #-}
weakenR :: forall cs' cs effs' effs ts fs. 
           (forall m. cs' m => cs m, Injects effs effs')
        => Runner effs ts fs cs
        -> Runner effs' ts fs cs'
weakenR r1 = Runner \oalg -> getR r1 (oalg . injs)

{-# INLINE weakenRC #-}
weakenRC :: forall cs' cs effs ts fs. 
           (forall m. cs' m => cs m)
        => Runner effs ts fs cs
        -> Runner effs ts fs cs'
weakenRC r1 = Runner \oalg -> getR r1 oalg