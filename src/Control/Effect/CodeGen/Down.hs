{-|
Module      : Control.Effect.CodeGen.Down
Description : Transforming meta-level types to object-level types 
License     : BSD-3-Clause
Maintainer  : Zhixuan Yang
Stability   : experimental

This module contains type classes and instances for lowering meta-level
datatypes to object-level datatypes.
-}
{-# LANGUAGE TemplateHaskell, UndecidableInstances #-}
{-# LANGUAGE BlockArguments, MonoLocalBinds #-}

module Control.Effect.CodeGen.Down where

import Control.Effect
import Control.Effect.Family.Algebraic
import Control.Effect.Family.Scoped
import Control.Effect.CodeGen.Type
import Control.Effect.CodeGen.Gen

import Data.Functor.Identity

import qualified Control.Monad.Trans.State.Strict as SS
import qualified Control.Monad.Trans.State.Lazy as LS
import Control.Monad.Trans.Maybe
import Control.Monad.Trans.Except
import Control.Monad.Trans.Reader
import Control.Monad.Trans.List
import Control.Monad.Trans.Resump
import Control.Monad.Trans.ResumpUp
import Control.Monad.Trans.CRes 
import Control.Monad.Trans.YRes
import Control.Monad.Trans.Push
import Control.Effect.Alternative ( (<|>) )

-- | @n $~> m@ iff the type constructor @n@ at compile time lowers to the type
-- constructor @m@ at runtime. For example, the functor (Up a ->) lowers to (a ->).
-- 
-- The instances of this type class are rather mechanical, and in the future we may
-- try to derive them generically.
class n $~> m where
  down :: n (Up x) -> Up (m x)

-- | Monads that can be lowered to @m@.
class    (Monad n, n $~> m) => MonadDown m n where
instance (Monad n, n $~> m) => MonadDown m n where

-- * Lowering instances for some basic functors

instance (->) (Up a)  $~>  (->) a where
  down f = [|| \x -> $$(f [||x||]) ||]

instance Maybe $~> Maybe where
  down Nothing = [||Nothing||]
  down (Just x) = [|| Just $$x ||]

instance (,) (Up a)  $~>  (,) a where
  down (ua, ux) = [|| ($$ua, $$ux) ||] 

instance Either (Up e)  $~>  Either e where
  down (Left e)  = [|| Left $$e ||]
  down (Right a) = [|| Right $$a ||]

instance [] $~> [] where
  down []     = [|| [] ||]
  down (a:as) = [|| $$a : $$(down as) ||]

instance (ms $~> os) => Alg ms n $~> Alg os m where
  down (Alg metaop) = [|| Alg $$(down @ms @os  metaop) ||]

instance (Functor ms, ms $~> os, n $~> m) => Scp ms n $~> Scp os m where
  down (Scp metaop) = [|| Scp $$(down @ms @os (fmap (down @n @m) metaop)) ||]

instance CStep (Up a)  $~>  CStep a where
  down FailS = [|| FailS ||]
  down (ChoiceS cx cy) = [|| ChoiceS $$cx $$cy ||]
  down (ActS ca cx) = [|| ActS $$ca $$cx ||]

instance YStep (Up a) (Up b)  $~>  YStep a b where
  down (YieldS ca ck) = [|| YieldS $$ca $$(down ck) ||]

-- * Lowering instances for some basic monad transformers. 
--
-- It's basically recursively lowering down using the down functions for basic functors.
-- If these instances look cryptic, try working out one of them explicitly without using
-- `down` recursively.

instance Gen $~> Identity where
  down g = [|| Identity $$(runGen g) ||]

instance Monad m => GenM m $~> m where
  down = runGenM

instance (Monad n, n $~> m) => SS.StateT (Up s) n $~> SS.StateT s m where
  down (SS.StateT g) = [|| SS.StateT \s -> $$(down (fmap down (g [||s||])))||]

instance (Monad n, n $~> m) => LS.StateT (Up s) n $~> LS.StateT s m where
  down (LS.StateT g) = [|| LS.StateT \s -> $$(down (fmap down (g [||s||]))) ||]

instance (Monad n, n $~> m) => ReaderT (Up r) n $~> ReaderT r m where
  down (ReaderT g) = [|| ReaderT \r -> $$(down (g [||r||])) ||]

instance (Monad n, n $~> m) => MaybeT n $~> MaybeT m where 
  down (MaybeT nMb) = [|| MaybeT $$(down (fmap down nMb))||]

instance (Monad n, n $~> m) => ExceptT (Up e) n $~> ExceptT e m where
  down (ExceptT nEx) = [|| ExceptT $$(down (fmap down nEx)) ||]

instance (Monad n, n $~> m) => ListT n $~> ListT m where
  down g = [|| ListT $$((down . fmap (down . fmap (down . fmap down))) (runListT g)) ||]

instance (Functor s, Monad n, n $~> m, s $~> t) => ResT s n $~> ResT t m where 
  down g = [|| ResT $$((down . fmap (down . fmap (down . fmap down))) (unResT g)) ||]

-- | @ListT Identity a@ is the same as @[a]@, but @[a]@ is of course preferable.
instance PushT Gen $~> [] where
  down p = runGen $ runPushT p (\ca -> fmap (\cas -> [|| ($$ca : $$cas) ||])) 
                               (return [|| [] ||])

pushMatch ::(Monad n, Monad m, n $~> m) => PushT n (Up x) -> n (Up (Maybe (x, ListT m x)))
pushMatch p = runPushT p (\ca -> fmap (\cas -> [|| Just ($$ca, ListT (return $$cas)) ||])) 
                         (return [|| Nothing ||])

instance (Monad n, Monad m, n $~> m) => PushT n $~> ListT m where
  down :: forall x. PushT n (Up x) -> Up (ListT m x)
  down p = [|| ListT $$(down (pushMatch p)) ||]

resUpMatch :: forall n m s l x. (Monad n, Functor l, n $~> m, l $~> s) 
           => ResUpT l n (Up x) -> n (Up (Either x (s (ResT s m x))))
resUpMatch p = runResUpT p 
                 (\cx -> return [|| Left $$cx ||]) 
                 (\ln -> return [|| Right $$(down @l @s 
                   (fmap (\c -> [|| ResT $$c ||]) (fmap (down @n @m) ln))) ||])

instance (Monad n, Functor l, Functor s, n $~> m, l $~> s) => ResUpT l n $~> ResT s m where
  down :: forall x. ResUpT l n (Up x) -> Up (ResT s m x)
  down p = [|| ResT $$(down (resUpMatch p)) ||]

-- * Generating tail-recursive code.

-- | The class $n $~>> m$ provides functions `downTail` and `downJoin` that are variations
-- of the function `down :: n (Up a) -> Up (m a)` for generating better code with tail recursion. 
-- When using the @CodeGen@ effect to generate a tail-recursive program, for example, 
-- @
--   ioExample :: StateT Int IO ()
--   ioExample = $$(down $
--      evalGenM @IO (upState @Int @IO `fuseAT` stateAT @(Up Int))
--        (do up [|| putStrLn "Hello" ||]
--            s <- get @(Up Int)
--            b <- split [|| $$s > 0 ||]
--            if b then put [|| $$s - 1||] >> up [|| ioExample ||] 
--                 else return [||()||]))
-- @
-- The final `up`-operation for the tail-recursive call @up [|| ioExample ||]@ generates
-- an unneeded case split of the result of the recursive call, making the generated
-- code no longer tail-recursive. We can solve this problem by replacing @up [|| ioExample ||]@
-- with @return [|| ioExample ||]@ in the meta-program and using instead the function
-- @`downJoin` :: n (Up (m x)) -> Up (m x)@. So the example above becomes
--
-- @
--   ioExample2 :: StateT Int IO ()
--   ioExample2 = $$(downJoin $
--     evalGenM @IO (upState @Int @IO `fuseAT` stateAT @(Up Int))
--       (do up [|| putStrLn "Hello" ||]
--           s <- get @(Up Int)
--           b <- split [|| $$s > 0 ||]
--           if b then put [|| $$s - 1||] >> return [|| ioExample ||] 
--                else return [||return ()||]))
-- @
-- 
-- A limitation of the function `downJoin` is that it forces all branches to return 
-- a piece of object-level monadic code, even for those branches that could return a pure
-- value, like the branch that returns a unit () above. This makes the generated code
-- suboptimal and we solve this by introducing `downTail`, which is the common generalisation
-- of `downJoin` and `down`.
-- 
-- The functions `downTail` and `downJoin` can be mutually defined, but the default 
-- `downTail` in terms of `downJoin` is not optimal. Moreover, there is an instance
-- of @n $~>> m@ from @n $~> m@, which solves the problem of tail recursion but the
-- generated code is not optimal.
--
-- Finally, you don't need to call @downTail@ or @downJoin@ manually. There is an 
-- algebra transformer "Control.Effect.CodeGen.Up.upCache" that deals with tail recursion
-- in a transparent way (by invoking `downTail` under the hood).

class (Functor n, Monad m) => n $~>> m where
  downTail :: n (Either (Up x) (Up (m x))) -> Up (m x)
  downTail = downJoin . fmap (\case 
    Left x  -> [|| return $$x ||]
    Right y -> y)

  downJoin :: n (Up (m x)) -> Up (m x)
  downJoin = downTail . fmap Right

-- | Default implementation of `downTail`/`downJoin` using `down`. The generated
-- code is not optimal but it /does/ solve the problem of tail recursion.
instance {-# OVERLAPPABLE #-} (Monad m, Functor n, n $~> m) => n $~>> m where
  downTail p = [|| $$(down p') >>= id ||] where
    p' = fmap (either (\x -> [|| return $$x ||]) id) p

instance Gen $~>> Identity where
  downTail g = unGen g \case 
    Left x  -> [|| Identity $$x ||]
    Right m -> m

instance Monad m => GenM m $~>> m where
  downTail g = unGenM g \case 
    Left x  -> [|| return $$x ||]
    Right m -> m

instance (Monad n, n $~>> m) => SS.StateT (Up s) n $~>> SS.StateT s m where
  downTail (SS.StateT g) = [|| SS.StateT \s -> $$(downTail (fmap f (g [||s||]))) ||] where
    f :: (Either (Up x) (Up (SS.StateT s m x)), Up s) -> Either (Up (x, s)) (Up (m (x, s)))
    f (Left x, cs)   = Left  [||($$x, $$cs)||]
    f (Right cm, cs) = Right [|| SS.runStateT $$cm $$cs ||]

instance (Monad n, n $~>> m) => LS.StateT (Up s) n $~>> LS.StateT s m where
  downTail (LS.StateT g) = [|| LS.StateT \s -> $$(downTail (fmap f (g [||s||]))) ||] where
    f :: (Either (Up x) (Up (LS.StateT s m x)), Up s) -> Either (Up (x, s)) (Up (m (x, s)))
    f (Left x, cs)   = Left  [||($$x, $$cs)||]
    f (Right cm, cs) = Right [|| LS.runStateT $$cm $$cs ||]

instance (Monad n, n $~>> m) => ReaderT (Up r) n $~>> ReaderT r m where
  downTail (ReaderT g) = [|| ReaderT \r -> $$(downTail (fmap (f [||r||]) (g [||r||]))) ||] where
    f cr (Left x)   = Left x
    f cr (Right cm) = Right [|| runReaderT $$cm $$cr ||]

instance (Monad n, n $~>> m) => ExceptT (Up e) n $~>> ExceptT e m where
  downTail (ExceptT g) = [|| ExceptT $$(downTail (fmap f g))||] where
    f :: Either (Up e) (Either (Up x) (Up (ExceptT e m x)))
      -> Either (Up (Either e x)) (Up (m (Either e x)))
    f (Left e) = Left [|| Left $$e ||]
    f (Right (Left x)) = Left [||Right $$x||]
    f (Right (Right m)) = Right [||runExceptT $$m||]

instance (Monad n, n $~>> m) => MaybeT n $~>> MaybeT m where
  downTail (MaybeT g) = [|| MaybeT $$(downTail (fmap f g)) ||] where
    f :: Maybe (Either (Up x) (Up (MaybeT m x)))
      -> Either (Up (Maybe x)) (Up (m (Maybe x)))
    f Nothing = Left [|| Nothing ||]
    f (Just (Left x)) = Left [|| Just $$x ||]
    f (Just (Right m)) = Right [|| runMaybeT $$m ||]

instance PushT Gen $~>> [] where
  downTail p = runGen $ runPushT p f (return [|| [] ||]) where
    f :: Either (Up x) (Up [x]) -> Gen (Up [x]) -> Gen (Up [x]) 
    f (Left cx)  gxs = do xs <- gxs; return [||$$cx : $$xs||]
    f (Right cl) gxs = do xs <- gxs; return (codeApp cl xs)

-- | Here we are being suboptimal by defining `downJoin` instead of
-- `downTail`. This is because the monad transformer `PushT` is defined to be
--
-- > forall t. (a -> n (Up t) -> n (Up t)) -> n (Up t) -> n (Up t)
-- 
-- so we aren't able to define @tmp@ below to have type
-- 
-- > p' :: n (Either (Up (Maybe (x, ListT m x))) 
-- >                 (Up (m (Maybe (x, ListT m x)))))
--
-- We can fix this problem if we generalise `PushT` to be 
--
-- > forall t. isSOP t => (a -> n t -> n t) -> n t -> n t
--
-- But this seems a bit over-engineering so it is not done, at least for now. 

instance (Monad n, Monad m, n $~>> m) => PushT n $~>> ListT m where
  downJoin :: forall x. PushT n (Up (ListT m x)) -> Up (ListT m x)
  downJoin p = let p' :: n (Up (m (Maybe (x, ListT m x))))
                   p' = runPushT p (\cxs -> fmap (\cys -> [|| runListT ($$cxs <|> ListT $$cys) ||])) 
                                    (return [|| return Nothing ||])
               in [|| ListT $$(downJoin p') ||]

instance (Monad n, Monad m, Functor s, Functor l, n $~>> m, l $~> s)
  => ResUpT l n $~>> ResT s m where
  downJoin :: forall x. ResUpT l n (Up (ResT s m x)) -> Up (ResT s m x)
  downJoin p = [|| ResT $$(downJoin @n @m p') ||] where
    p' :: n (Up (m (Either x (s (ResT s m x)))))
    p' = runResUpT p 
            (\cr -> return [|| unResT $$cr ||])
            (\ln -> let g = down @l @s (fmap (\c -> [||ResT $$c||]) (fmap (downJoin @n @m) ln))
                    in return [|| return (Right $$g) ||])