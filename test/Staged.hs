{-# LANGUAGE BlockArguments, TemplateHaskell #-}
module Main where

import Control.Effect
import Control.Effect.CodeGen
import Control.Effect.State.Strict

import Language.Haskell.TH
import StagedGen
import Control.Effect.Except

{-
Generated code: 
    StateT
      (\ s_a4dv
         -> Identity
              (if (s_a4dv > 0) then
                   let x_a4dw = (s_a4dv + 1)
                   in
                     case runIdentity (runStateT countdown x_a4dw) of
                       (a_a4dx, b_a4dy) -> (a_a4dx, b_a4dy)
               else
                   ((), s_a4dv)))

-}

countdown :: StateT Int Identity ()
countdown = $$(down $ StateT \cs -> fmap (\(s,a) -> (a,s)) $ 
  handleM genAlg 
    (letPut @Int |> upStateStrict @Int @Identity |> state @(Up Int) cs) 
    (countdownGen [|| countdown ||]))

{-
Generated code:
    ExceptT
      (Identity
         (if (n_a4nE > 0) then
              case runIdentity (runExceptT (catchProgram (n_a4nE - 1))) of
                Left a_a4Uc -> Left ()
                Right b_a4Ud -> Right b_a4Ud
          else
              Left ()))
-}

catchProgram :: Int -> ExceptT () Identity ()
catchProgram n = $$(down $ ExceptT $ 
  handleM genAlg 
          (upExcept @() @Identity |> except) 
          (catchGen [||n||] [||catchProgram||]))

main = return ()