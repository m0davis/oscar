{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE UnicodeSyntax #-}

module Oscar.Oscar where

import Oscar.Main.Prelude

import qualified Oscar.Formula as F
import qualified Oscar.FormulaCode as FC
import qualified Oscar.Problem as P

import Oscar.Problem (Problem(Problem))
import Oscar.Formula (Symbol(Symbol))
import Oscar.FormulaCode (SFormula)

type FormulaTerm = FC.FormulaTerm
type Discriminator = FC.Discriminator

testOscar ∷ Problem → IO ()
testOscar problem@(Problem {..}) = do
    print "TEST: STARTING"
    print "Problem:"
    ppPrint problem
    print "TEST: ENDING"
    return ()

