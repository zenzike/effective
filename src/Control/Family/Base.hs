{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
module Control.Family.Base 
  (module Control.Family.Base
  , Effect
  , Type
  , Constraint
  ) where

import Data.Kind ( Type, Constraint )
import Control.Effects

type Family = Effect -> Constraint
