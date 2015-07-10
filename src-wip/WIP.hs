{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE FlexibleContexts #-}

module Main where

import qualified Data.Map.Lazy as Map
import Data.Functor.Identity
--import Data.IntMap
import Control.Monad
import Control.Monad.Trans.Class
import Control.Monad.Trans.Writer.Lazy
import Control.Monad.Trans.State.Lazy

import Match ()

main ∷ IO ()
main = do
    o1 ← getInitialOscarState
    print o1
    let (oses, o2) = runIdentity (runStateT (execWriterT $ evalStateT think 0) o1)
    printOscarEvents oses
    print o2

data OscarState = OscarState
    { _osCycle ∷ Int
    }
  deriving (Eq, Read, Show)

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

printOscarEvents ∷ [(Depth, OscarStateEvent)] → IO ()
printOscarEvents oses = forM_ oses print


type Depth = Int
type TLog = WriterT [(Depth, OscarStateEvent)]
type TDepth = StateT Depth
type TOscar = StateT OscarState

type TDepthLogOscar m = (TDepth (TLog (TOscar m)))

type OscarApplicationM = TDepthLogOscar Identity

tellLog ∷ OscarStateEvent → OscarApplicationM ()
tellLog ose = do
    depth ← getDepth
    lift . tell $ [(depth, ose)]

getDepth ∷ OscarApplicationM Depth
getDepth = get

withIncDepth ∷ OscarApplicationM a → OscarApplicationM a
withIncDepth m = do
    modify succ
    m <* modify pred

logLabel ∷ OscarStateEventLabel → OscarApplicationM a → OscarApplicationM a
logLabel l m = do
    tellLog $ OSE_BeginLabel l
    withIncDepth m <* do
        tellLog $ OSE_EndLabel l

getOscar ∷ OscarApplicationM OscarState
getOscar = lift . lift $ get

modifyOscar ∷ (OscarState → OscarState) → OscarApplicationM ()
modifyOscar = lift . lift . modify

think ∷ OscarApplicationM ()
think = logLabel OSEL_Think $ do
    c ← _osCycle <$> getOscar
    tellLog $ OSE_CycleEq c
    modifyOscar os <* do
        c ← _osCycle <$> getOscar
        tellLog $ OSE_CycleEq c
  where
    os OscarState {..} = OscarState { _osCycle = _osCycle + 1 }

iListFor ∷ Formula → [InterestVariable] → IList
iListFor f ivs =



-- Apparently [Variable] is always empty
interestsFor ∷ Free [] a → [a] → Maybe (NonEmptyList Interest, Map Variable Variable)
interestsFor ∷ Free [] a → [a] → Maybe (Interest, [Interest], Map a a)

[FormulaTerm] → Free [] a
formulaCode ∷ UFormula → ([Discriminator], [FormulaTerm])
