{-|
Module      : Control.Effect.Internal.Effs
Description : The union type for effect operations
License     : BSD-3-Clause
Maintainer  : Nicolas Wu
Stability   : experimental
-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

module Control.Effect.Internal.Effs
  ( Member
  , Members
  , Effect
  , Effs (Effs, Eff)
  , Algebra
  , Injects (..)
  , Append
  , absurdEffs
  , inj
  , prj
  , weakenAlg
  , heither
  , hunion
  , (#)
  )
  where

-- import Control.Effect.Internal.Effs.Sum
import Control.Effect.Internal.Effs.Indexed