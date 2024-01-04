{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
module Control.Family
  ( module Control.Family
  , Effect
  , Type
  , Constraint
  ) where

import Data.Kind ( Type, Constraint )
import Control.Effect

type Family = Effect -> Constraint
