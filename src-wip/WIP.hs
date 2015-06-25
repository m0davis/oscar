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
    | OSE_ThinkStarted
    | OSE_ThinkEnded
  deriving (Eq, Read, Show)

printOscarEvents ∷ [OscarStateEvent] → IO ()
printOscarEvents oses = forM_ oses print

think ∷ WriterT [OscarStateEvent] (State OscarState) ()
think = do
    tell [OSE_ThinkStarted]
    c ← lift $ gets _osCycle
    tell [OSE_CycleEq c]
    lift (modify os) <* do
        c ← lift $ gets _osCycle
        tell [OSE_CycleEq c]
        tell [OSE_ThinkEnded]
  where
    os OscarState {..} = OscarState { _osCycle = _osCycle + 1 }

data OscarState = OscarState
    { _osCycle ∷ Int
    }
  deriving (Eq, Read, Show)
