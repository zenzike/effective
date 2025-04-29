{-# LANGUAGE FunctionalDependencies, TemplateHaskell, UndecidableInstances, BlockArguments #-}

module Control.Effect.CodeGen.Down where

import Control.Effect.CodeGen.Type
import Control.Effect.CodeGen.Gen
import Control.Effect.CodeGen.GenM
import Data.Functor.Identity
import qualified Control.Monad.Trans.State.Strict as SS
import qualified Control.Monad.Trans.State.Lazy as LS
import Control.Monad.Trans.Maybe
import Control.Monad.Trans.Except
import Control.Monad.Trans.Reader
import Control.Monad.Trans.List
import Control.Monad.Trans.Resump
import Control.Monad.Trans.CRes 
import Control.Monad.Trans.YRes
import Control.Monad.Trans.Push
import Control.Applicative ( Alternative(empty, (<|>)) )

-- | The type constructor @n@ at compile time lowers to the monad @m@ at runtime.
-- For example, the functor (Up a ->) lowers to (a ->).
-- The instances of this type class are rather mechanical, and in the future we may
-- try to derive them generically.
class n $~> m where
  down :: n (Up x) -> Up (m x)

-- | This class provides a function `downJoin` that is a special case of `down` and 
-- is used for generating better code for tail recursion. When using the @CodeGen@
-- effect to generate a tail-recursive program, for example, 
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
-- code no longer tail-recursive. We solve this problem by replacing @up [|| ioExample ||]@
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
-- The function @downJoin@ has a defualt implementation @downJoin p = [|| $$(down p) >>= id ||]@
-- and it /does/ solve the problem of tail recursion, but it may be overridden to 
-- generate more compact code.

class Monad m => n $~>> m where
  downJoin :: n (Up (m x)) -> Up (m x)

-- | Default implementation of `downJoin` using `down`.
instance {-# OVERLAPS #-} (Monad m, n $~> m) => n $~>> m where
  downJoin p = [|| $$(down p) >>= id ||]




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

instance CStep (Up a)  $~>  CStep a where
  down FailS = [|| FailS ||]
  down (ChoiceS cx cy) = [|| ChoiceS $$cx $$cy ||]
  down (ActS ca cx) = [|| ActS $$ca $$cx ||]

instance YStep (Up a) (Up b)  $~>  YStep a b where
  down (YieldS ca ck) = [|| YieldS $$ca $$(down ck) ||]

-- * Lowering instances for some basic monad transformers. 
-- 
-- It's basically recursively lowering down using the down functions for basic functors.
-- If these instances look cryptic, try working out one of them explictly without using
-- `down` recursively (except the one for the monad @n@).

instance Gen $~> Identity where
  down g = [|| Identity $$(runGen g) ||]

instance {-# OVERLAPS #-} Gen $~>> Identity where
  downJoin = runGen

instance Monad m => GenM m $~> m where
  down = runGenM

instance {-# OVERLAPS #-} Monad m => GenM m $~>> m where
  downJoin g = unGenM g id 

instance (Monad n, n $~> m) => SS.StateT (Up s) n $~> SS.StateT s m where
  down (SS.StateT g) = [|| SS.StateT \s -> $$(down (fmap down (g [||s||])))||]

instance (Monad n, n $~>> m) => SS.StateT (Up s) n $~>> SS.StateT s m where
  downJoin (SS.StateT g) = [|| SS.StateT \s -> $$(downJoin (fmap f (g [|| s ||]))) ||] where
    f :: (Up (SS.StateT s m x), Up s) -> Up (m (x, s))
    f (cm, cs) = [|| SS.runStateT $$cm $$cs ||]

instance (Monad n, n $~> m) => LS.StateT (Up s) n $~> LS.StateT s m where
  down (LS.StateT g) = [|| LS.StateT \s -> $$(down (fmap down (g [||s||]))) ||]

instance (Monad n, n $~>> m) => LS.StateT (Up s) n $~>> LS.StateT s m where
  downJoin (LS.StateT g) = [|| LS.StateT \s -> $$(downJoin (fmap f (g [|| s ||]))) ||] where
    f :: (Up (LS.StateT s m x), Up s) -> Up (m (x, s))
    f (cm, cs) = [|| LS.runStateT $$cm $$cs ||]

instance (Monad n, n $~> m) => ReaderT (Up r) n $~> ReaderT r m where
  down (ReaderT g) = [|| ReaderT \r -> $$(down (g [||r||])) ||]

instance (Monad n, n $~>> m) => ReaderT (Up r) n $~>> ReaderT r m where
  downJoin (ReaderT g) = [|| ReaderT \r -> $$(downJoin
    (fmap (\cm -> [|| runReaderT $$cm r ||]) (g [|| r ||]))) ||]

instance (Monad n, n $~> m) => MaybeT n $~> MaybeT m where 
  down (MaybeT nMb) = [|| MaybeT $$(down (fmap down nMb))||]

instance (Monad n, n $~>> m) => MaybeT n $~>> MaybeT m where
  downJoin (MaybeT g) = [|| MaybeT $$(downJoin (fmap f g)) ||] where
    f :: Maybe (Up (MaybeT m x)) -> Up (m (Maybe x))
    f Nothing   = [|| return Nothing ||]
    f (Just cm) = [|| runMaybeT $$cm ||]

instance (Monad n, n $~> m) => ExceptT (Up e) n $~> ExceptT e m where
  down (ExceptT nEx) = [|| ExceptT $$(down (fmap down nEx)) ||]

instance (Monad n, n $~>> m) => ExceptT (Up e) n $~>> ExceptT e m where
  downJoin (ExceptT g) = [|| ExceptT $$(downJoin (fmap f g)) ||] where
    f :: Either (Up e) (Up (ExceptT e m x)) -> Up (m (Either e x))
    f (Left ce)  = [|| return (Left $$ce) ||]
    f (Right cm) = [|| runExceptT $$cm    ||]

instance (Monad n, n $~> m) => ListT n $~> ListT m where
  down g = [|| ListT $$((down . fmap (down . fmap (down . fmap down))) (runListT g)) ||]

instance (Functor s, Monad n, n $~> m, s $~> t) => ResT s n $~> ResT t m where 
  down g = [|| ResT $$((down . fmap (down . fmap (down . fmap down))) (unResT g)) ||]

-- | @ListT Identity a@ is the same as @[a]@, but presumably most people prefer seeing the latter.
instance PushT Gen $~> [] where
  down :: forall x. PushT Gen (Up x) -> Up [x]
  down p = runGen $ runPushT p (\ca -> fmap (\cas -> [|| ($$ca : $$cas) ||])) 
                               (return [|| [] ||])

instance (Monad n, Monad m, n $~> m) => PushT n $~> ListT m where
  down :: forall x. (Monad n, Monad m, n $~> m) => PushT n (Up x) -> Up (ListT m x)
  down p = let tmp :: n (Up (Maybe (x, ListT m x)))
               tmp = runPushT p (\ca -> fmap (\cas -> [|| Just ($$ca, ListT (return $$cas)) ||])) 
                                (return [|| Nothing ||])
           in [|| ListT $$(down tmp) ||]

instance PushT Gen $~>> [] where
  downJoin :: PushT Gen (Up [x]) -> Up [x]
  downJoin p = runGen $ runPushT p (\cxs -> fmap (\cys -> codeApp cxs cys ))
                                   (return [|| [] ||])

instance (Monad n, Monad m, n $~>> m ) => PushT n $~>> ListT m where
  downJoin :: forall x. PushT n (Up (ListT m x)) -> Up (ListT m x)
  downJoin p = let tmp :: n (Up (m (Maybe (x, ListT m x))))
                   tmp = runPushT p (\cxs -> fmap (\cys -> [|| runListT ($$cxs <|> ListT $$cys) ||])) 
                                    (return [|| return Nothing ||])
               in [|| ListT $$(downJoin tmp) ||]