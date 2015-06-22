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
import Oscar.FormulaCode (Formula)

type FormulaTerm = FC.FormulaTerm
type Discriminator = FC.Discriminator


type Tree a = Free [] a

-- formulaToFree ∷ Formula → Free [] Text
-- formulaToFree () =

{-
match ∷ (Eq a) ⇒ Tree a → Tree a → Set a → Maybe (Map a (Tree a))
match p e vs = match' p e vs []

-- Nothing = failed to match
-- Just [] = matches without any additional bindings
-- Just [(p1, e1), ...] = matches with
match' ∷ (Eq a) ⇒ Tree a → Tree a → Set a → Map a (Tree a) → Maybe (Map a (Tree a))
match' (Pure p) e vs bs =
    if p `elem` vs then
        case lookup p bs of
            Just q → -- a pattern variable was found and it already has been bound, so it had better be equal to the pre-existing binding to be a match.
              if q == e
                 then Just []
                 else Nothing
            Nothing → -- a pattern variable was found and it lacks a binding, so we give it one
              Just [(p, e)]
    else
        -- the pattern is non-variable, so the expression must be equal to be a match
        if p == e
           then Just []
           else Nothing
match' (Free (p:ps)) (Free (e:es)) vs bs =
    let m = match' p e vs bs in
        case m of
            Just b →
                let m' = match' ps es vs (b `union` bs) in
                    case m' of
                        Just b' → Just (b `union` b')
                        Nothing → Nothing
            Nothing → Nothing
match' (Free _) (Pure _) _ _ = Nothing
-}

testOscar ∷ Problem → IO ()
testOscar problem@(Problem {..}) = do
    print "TEST: STARTING"
    print "Problem:"
    ppPrint problem
    print "TEST: ENDING"
    return ()

