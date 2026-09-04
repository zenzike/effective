{-# LANGUAGE GADTs  #-}
module ConcurStaged where

import Prelude hiding (log )
import Control.Effect
import Control.Effect.IO
import Control.Effect.Writer
import Control.Effect.Concurrency
import Control.Effect.Reader
import Control.Effect.CodeGen
import qualified Control.Effect.Reader as R
import qualified Control.Effect.Except as E
import qualified Control.Concurrent.QSem as QSem
import Control.Concurrent ( forkIO, QSem )
import qualified Data.Map as M

type IOPar = '[Alg IO, Par, JPar]

data ActNames = Handshake | Raisehand deriving (Show, Eq, Ord)
type HR = CCSAction ActNames

bohem :: () ! [Act HR, Res HR, Par, Tell String]
bohem = par (resHS $ par (do tell "I am just a poor boy"; handshake)
                         (do shakehand; tell "I need no sympathy"))
            (tell "Oh poor boy")

handshake :: Member (Act HR) effs => Prog effs ()
handshake = act (Action Handshake)

shakehand :: Member (Act HR) effs => Prog effs ()
shakehand = act (CoAction Handshake)

resHS :: Member (Res HR) effs => Prog effs x -> Prog effs x
resHS x = res (Action Handshake) x


ioParC :: AlgebraC IOPar IO
ioParC = ioAlgC #$ parIOAlgC #$ jparIOAlgC

tellWithLockC :: HandlerC '[Tell String] '[Tell String, Act HR, Par, Res HR] '[] a a
tellWithLockC = HandlerC
  (RunnerC $ \oalg -> [|| \p ->
    let daemon =
          do $$(callMC oalg) (Act (CoAction Raisehand) ())
             $$(callMC oalg) (Act (Action Raisehand) ())
             daemon
    in do $$(callMC oalg) (Res (Action Raisehand) $
            $$(callMC oalg) (Par p daemon))
  ||])
  (algTrans1C $ \(oalg@(a :#$ _)) -> [|| NT $ \(Tell s k) ->
    do $$(callMC oalg) (Act (Action Raisehand) ())
       -- I don't know why in GHC 9.8.4 and 9.10.1 the following causes an error of
       -- overlapping instances.
       -- $$(callMC oalg) (Tell s ())
       at $$a (Tell s ())
       $$(callMC oalg) (Act (CoAction Raisehand) ())
       return k
  ||])


askMC :: Ask s `Member` effs => AlgebraC effs m -> CodeQ (m s)
askMC alg = [|| $$(dispatchC alg) `at` (Ask id) ||]

tellMC :: Tell w `Member` effs => AlgebraC effs m -> CodeQ (w -> m ())
tellMC alg = [|| \w -> $$(dispatchC alg) `at` (Tell w ()) ||]

tellWithIdC :: HandlerC '[Tell String] '[Tell String, Ask String] '[] a a
tellWithIdC= interpretM1C $ \alg -> [|| NT $ \(Tell s k) ->
  do id <- $$(askMC alg)
     $$(tellMC alg) (id ++ ": " ++ s ++ ". ")
     return k
  ||]


parMC :: Member Par effs => AlgebraC effs m -> CodeQ (m x) -> CodeQ (m x) -> CodeQ (m x)
parMC alg p q = [|| $$(callMC alg) (Par $$p $$q) ||]

localMC :: Member (Local s) effs => AlgebraC effs m -> CodeQ (s -> s) -> CodeQ (m x) -> CodeQ (m x)
localMC alg f p = [|| $$(callMC alg) (Local $$f $$p) ||]

threadIdC :: HandlerC '[Par] '[Par, Local String] '[] a a
threadIdC = interpretM1C $ \alg -> [|| NT $ \(Par a b) ->
  $$(parMC alg (localMC alg [|| (++ "L")||] [||a||])
               (localMC alg [|| (++ "R")||] [||b||])) ||]


-- Fully staged version of bohem

type QSemMapS a = M.Map a (CodeQ QSem, CodeQ QSem)

ccsByQSemS :: forall n a . Ord n =>
  Handler '[Act (CCSAction n), Res (CCSAction n)]
          '[ R.Ask (QSemMapS n), R.Local (QSemMapS n)
           , E.Throw (CodeQ String), CodeGenM IO ]
          '[]
          a
          a
ccsByQSemS = interpretM $ \oalg ->
  (\(Act n k) -> do
    m <- R.askM @(QSemMapS n) oalg
    case M.lookup (getActionName n) m of
      Nothing -> E.throwM oalg ([||"Channel used before creation!"||] :: CodeQ String)
      Just (cs1, cs2) ->
        case n of
          Action   _ -> do genDoM oalg [||QSem.waitQSem $$cs1||]; genDoM oalg [||QSem.signalQSem $$cs2||]
          CoAction _ -> do genDoM oalg [||QSem.signalQSem $$cs1||]; genDoM oalg [||QSem.waitQSem $$cs2||]
    return k
  ) :#.
  (\(Res a p) -> do
    m <- R.askM @(QSemMapS n) oalg
    cs1 <- genDoM oalg [||QSem.newQSem 0||];
    cs2 <- genDoM oalg [||QSem.newQSem 0||];
    let m' = M.insert (getActionName a) (cs1, cs2) m
    R.localM oalg (const m') p)

writerGenIO :: Handler '[Tell String] '[CodeGenM IO] '[] a a
writerGenIO = interpret1 $ \(Tell s k) -> do genDo [|| putStrLn s ||]; return k