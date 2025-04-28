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


-- | The type constructor @n@ at compile time lowers to the monad @m@ at runtime.
-- For example, the functor (Up a ->) lowers to (a ->).
-- The instances of this type class are rather mechanical, and in the future we may
-- try to derive them generically.
class n $~> m where
  down :: n (Up x) -> Up (m x)

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

instance {-#OVERLAPS#-} PushT Gen $~> [] where
  down :: forall x. PushT Gen (Up x) -> Up [x]
  down p = runGen $ runPushT p (\ca -> fmap (\cas -> [|| ($$ca : $$cas) ||])) 
                               (return [|| [] ||])


instance (Monad n, Monad m, n $~> m) => PushT n $~> ListT m where
  down :: forall x. (Monad n, Monad m, n $~> m) => PushT n (Up x) -> Up (ListT m x)
  down p = let tmp :: n (Up (Maybe (x, ListT m x)))
               tmp = runPushT p (\ca -> fmap (\cas -> [|| Just ($$ca, ListT (return $$cas)) ||])) 
                                (return [|| Nothing ||])
           in [|| ListT $$(down tmp) ||]