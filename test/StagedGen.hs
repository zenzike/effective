{-# LANGUAGE BlockArguments, TemplateHaskell #-}
module StagedGen where

import Control.Effect
import Control.Effect.CodeGen
import Control.Effect.State.Strict
import Control.Effect.Except 

import Language.Haskell.TH

countdownGen :: Members '[LiftGen, UpOp m, Put (Up Int), Get (Up Int)] sig 
             => Up (m ()) -> Prog sig (Up ())
countdownGen self = 
  do cs <- get @(Up Int)
     b <- split [|| $$cs > 0 ||]
     if b then do put [|| $$cs + 1 ||]; up self
          else return [|| () ||]


catchGen :: forall sig m. Members '[LiftGen, UpOp m, Catch (Up ()), Throw (Up ())] sig 
             => Up Int -> Up (Int -> m ()) -> Prog sig (Up ())
catchGen cN self = 
  do b <- split [|| $$cN > 0 ||]
     if b 
      then catch @(Up ()) (up [|| $$self ($$cN - 1)||]) (\_ -> throw @(Up ()) [||()||])
      else throw @(Up ()) [|| () ||]