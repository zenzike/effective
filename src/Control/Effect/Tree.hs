{-# LANGUAGE DataKinds #-}

module Control.Effect.Tree where

import Control.Effect
import Control.Effect.Algebraic
import Control.Effect.Alternative
import Control.Effect.Scoped

import Control.Applicative
import Control.Monad.Trans.Tree

nondetTreeAlg
  :: Monad m
  => (forall x . oeff m  x -> m x)
  -> (forall x . Effs '[Empty, Choose] (TreeT m) x -> TreeT m x)
nondetTreeAlg oalg op
  | Just (Alg Empty)          <- prj op = empty
  | Just (Scp (Choose xs ys)) <- prj op = xs <|> ys

nondetTree :: Handler [Empty, Choose] '[] (TreeT) []
nondetTree = handler' runTreeA nondetTreeAlg
