module Data.EitherF where

data VoidF a

absurdVoidF :: VoidF a -> b
absurdVoidF x = case x of {}

instance Functor VoidF where
  fmap x = absurdVoidF

data EitherF f g a = InlF (f a) | InrF (g a)

instance (Functor f, Functor g) => Functor (EitherF f g) where
  fmap h (InlF x) = InlF (fmap h x)
  fmap h (InrF x) = InrF (fmap h x)
