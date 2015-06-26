module Main where

import Data.IntMap
import Control.Monad
import Control.Monad.Trans.Class
import Control.Monad.Trans.Writer.Lazy
import Control.Monad.Trans.State.Lazy

main ∷ IO ()
main = do
    o1 ← getInitialOscarState
    print o1
    let (oses, o2) = runState (execWriterT think) o1
    printOscarEvents oses
    print o2

getInitialOscarState ∷ IO OscarState
getInitialOscarState = return OscarState { _osCycle = 0 }

data OscarStateEvent
    = OSE_Initialized
    | OSE_CycleEq Int
    | OSE_BeginLabel OscarStateEventLabel
    | OSE_EndLabel OscarStateEventLabel
  deriving (Eq, Read, Show)

data OscarStateEventLabel
    = OSEL_Think
    | OSEL_Sleep
  deriving (Eq, Read, Show)

printOscarEvents ∷ [OscarStateEvent] → IO ()
printOscarEvents oses = forM_ oses print

osel ∷ OscarStateEventLabel → WriterT [OscarStateEvent] (State OscarState) () → WriterT [OscarStateEvent] (State OscarState) ()
osel l m = tell [OSE_BeginLabel l] >> m <* tell [OSE_EndLabel l]

think ∷ WriterT [OscarStateEvent] (State OscarState) ()
think = osel OSEL_Think $ do
    c ← lift $ gets _osCycle
    tell [OSE_CycleEq c]
    lift (modify os) <* do
        c ← lift $ gets _osCycle
        tell [OSE_CycleEq c]
  where
    os OscarState {..} = OscarState { _osCycle = _osCycle + 1 }

data OscarState = OscarState
    { _osCycle ∷ Int
    }
  deriving (Eq, Read, Show)
