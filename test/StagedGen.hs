{-# LANGUAGE BlockArguments, TemplateHaskell, ImpredicativeTypes, PartialTypeSignatures #-}
module StagedGen where

import Control.Effect
import Control.Effect.CodeGen
import Control.Effect.State.Strict
import Control.Effect.Except 
import Control.Effect.Alternative
import Control.Monad.Trans.Push
import Control.Monad.Trans.List
import Data.Functor.Identity
import Control.Effect.Internal.Forward.ForwardC
import Data.Iso
import Control.Monad (ap)

import Control.Monad.Trans.Maybe

countdownGen :: Members '[CodeGen, UpOp m, Put (Up Int), Get (Up Int)] sig 
             => Up (m ()) -> Prog sig (Up ())
countdownGen self = 
  do cs <- get @(Up Int)
     b <- split [|| $$cs > 0 ||]
     if b then do put [|| $$cs - 1 ||]; up self
          else return [|| () ||]

catchGen :: forall sig m. Members '[CodeGen, UpOp m, Catch (Up ()), Throw (Up ())] sig 
         => Up Int -> Up (Int -> m ()) -> Prog sig (Up ())
catchGen cN self = 
  do b <- split [|| $$cN > 0 ||]
     if b 
      then catch (up [|| $$self ($$cN - 1)||]) (\(_ :: Up ()) -> throw @(Up ()) [||()||])
      else throw @(Up ()) [|| () ||]

choiceGen :: forall sig m. Members '[CodeGen, UpOp m, Choose, Empty] sig 
          => Up Int -> Up (Int -> m Int) -> Prog sig (Up Int)
choiceGen cN self = 
  do b <- split [|| $$cN > 0 ||]
     if b 
      then up [|| $$self ($$cN - 1) ||] <|> return cN
      else empty


mergeMb :: MaybeT Gen (Up a) -> MaybeT Gen (Up a)
mergeMb ma = shiftMb \kj kn -> runGen $ 
  do kN <- genLet_ [|| $$kn ||]
     kJ <- genLet_ [|| \a -> $$(kj ([||a||])) ||]
     m <- runMaybeT ma
     case m of 
       Nothing -> return kN 
       Just a  -> return ([|| $$kJ $$a ||])

shiftMb :: (forall r. (a -> Up r) -> Up r -> Up r) 
        -> MaybeT Gen a
shiftMb f = MaybeT $ shift \k -> return (f (k . Just) (k Nothing))

resetMb :: forall a. MaybeT Gen (Up a) -> MaybeT Gen (Up a)
resetMb g = 
  let act :: Up (MaybeT Identity a)
      act = down g
  in MaybeT do genSplit [|| runIdentity (runMaybeT $$act) ||]
 
{-
shift :: (forall r. (a -> Up r) -> Gen (Up r)) -> Gen a
shift f = Gen $ runGen . f
-}

mergeST :: StateT (Up s) Gen (Up a) -> StateT (Up s) Gen (Up a)
mergeST ma = StateT \s -> shift \k -> 
  do k' <- genLet_ [|| \a s -> $$(k ([||a||], [||s||])) ||] 
     (a, s) <- runStateT ma s
     return [|| $$k' $$a $$s ||]


mergePS :: PushT Gen (Up a) -> PushT Gen (Up a)
mergePS ma = PushT \kc kn -> 
  do kn' <- genLet_ [|| runIdentity $$(down kn) ||] 
     kc' <- genLet_ [|| \a t -> runIdentity $$(down (kc [||a||] (return [||runIdentity t||]))) ||]
     runPushT ma (\ca mas -> return [|| $$kc' $$ca $$(down mas) ||]) (return kn')


upList :: forall a. Up (ListT Identity a) -> ListT Gen (Up a)
upList ma = ListT $ shift \(k :: _ -> Up r) ->
  let kNil :: Up r
      kNil = k Nothing

      kCons :: (Up a, ListT Gen (Up a)) -> Up r
      kCons = k . Just

      tmp = [|| runIdentity $ 
        foldListT (\a as -> Identity $$(kCons ([||a||], _)))
                  (Identity $$kNil) 
                  $$ma ||]
  in return tmp