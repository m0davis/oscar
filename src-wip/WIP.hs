module Main where

import Data.IntMap
import Control.Monad

main ∷ IO ()
main = do
    o1 ← getInitialOscarState
    print o1
    let (o2, oses) = think o1
    printOscarEvents oses
    print o2

getInitialOscarState ∷ IO OscarState
getInitialOscarState = return OscarState { _osCycle = 0 }

data OscarStateEvent
    = OSE_Initialized
    | OSE_IncreasedCycle Int
    | OSE_ThinkStarted
  deriving (Eq, Read, Show)

printOscarEvents ∷ [OscarStateEvent] → IO ()
printOscarEvents oses = forM_ oses print

think ∷ OscarState → (OscarState, [OscarStateEvent])
think OscarState {..} = (os, oses)
  where
    oses = [OSE_IncreasedCycle $ Main._osCycle os]
    os = OscarState { _osCycle = _osCycle + 1 }

data OscarState = OscarState
    { _osCycle ∷ Int
    }
  deriving (Eq, Read, Show)
