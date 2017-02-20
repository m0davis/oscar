{-# OPTIONS --allow-unsolved-metas #-}
module IsLiteralProblem where

open import OscarPrelude
open import IsLiteralSequent
open import Problem

record IsLiteralProblem (𝔓 : Problem) : Set
 where
  constructor _¶_
  field
    {problem} : Problem
    isLiteralInferences : All IsLiteralSequent (inferences 𝔓)
    isLiteralInterest : IsLiteralSequent (interest 𝔓)

open IsLiteralProblem public

instance EqIsLiteralProblem : ∀ {𝔓} → Eq (IsLiteralProblem 𝔓)
EqIsLiteralProblem = {!!}
