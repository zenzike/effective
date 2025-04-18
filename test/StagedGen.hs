{-# LANGUAGE BlockArguments, TemplateHaskell #-}
module StagedGen where

import Control.Effect
import Control.Effect.CodeGen
import Control.Effect.State.Strict

import Language.Haskell.TH

countdownGen :: Members '[LiftGen, UpOp m, Put (Up Int), Get (Up Int)] sig 
             => Up (m ()) -> Prog sig (Up ())
countdownGen recCall = 
  do cs <- get @(Up Int)
     b <- split [|| $$cs > 0 ||]
     if b then do put [|| $$cs + 1 ||]; up recCall
          else return [|| () ||]