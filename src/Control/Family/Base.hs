{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
module Control.Family.Base 
  (module Control.Family.Base
  , Effect
  , Type
  , Constraint
  ) where

import Data.Kind ( Type, Constraint )
import Control.Effect

type Family = Effect -> Constraint
