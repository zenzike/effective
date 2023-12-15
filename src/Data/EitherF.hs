module Data.EitherF where

data VoidF a

data EitherF f g a = InlF (f a) | InrF (g a)
