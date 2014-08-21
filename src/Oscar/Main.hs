{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PatternSynonyms #-}
-- {-# LANGUAGE DataKinds #-}

module Oscar.Main where

import Oscar.Main.Prelude

import Oscar.Main.ProblemBase

import Oscar.Problem

combinedProblems ∷ FilePath ⁞ [Problem]
combinedProblems = ƭ $ fpFromString "combined-problems"

getBaseProblem ∷ Problem → Problem
getBaseProblem bp'@(BaseProblem _ _ _ _ _ _) = bp'
getBaseProblem _ = error "impossible? Problem does not match BaseProblem"
