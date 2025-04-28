{-# LANGUAGE BlockArguments, TemplateHaskell, ImpredicativeTypes #-}
module StagedGen where

import Control.Effect
import Control.Effect.CodeGen
import Control.Effect.State.Strict
import Control.Effect.Except 
import Control.Effect.Alternative
import Control.Monad.Trans.Push
import Control.Monad.Trans.List
import Data.Functor.Identity
import Language.Haskell.TH
import Control.Effect.Internal.Forward.ForwardC
import Data.Iso

countdownGen :: Members '[CodeGen, UpOp m, Put (Up Int), Get (Up Int)] sig 
             => Up (m ()) -> Prog sig (Up ())
countdownGen self = 
  do cs <- get @(Up Int)
     b <- split [|| $$cs > 0 ||]
     if b then do put [|| $$cs + 1 ||]; up self
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