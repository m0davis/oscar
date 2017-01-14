
module LiteralProblem where

open import OscarPrelude
open import Problem
open import IsLiteralProblem

record LiteralProblem : Set
 where
  constructor ⟨_⟩
  field
    {problem} : Problem
    isLiteralProblem : IsLiteralProblem problem

open LiteralProblem public

instance EqLiteralProblem : Eq LiteralProblem
EqLiteralProblem = {!!}

open import 𝓐ssertion

instance 𝓐ssertionLiteralProblem : 𝓐ssertion LiteralProblem
𝓐ssertionLiteralProblem = record {}

open import HasSatisfaction

instance HasSatisfactionLiteralProblem : HasSatisfaction LiteralProblem
HasSatisfaction._⊨_ HasSatisfactionLiteralProblem I 𝔓 = I ⊨ problem 𝔓

open import HasDecidableValidation

instance HasDecidableValidationLiteralProblem : HasDecidableValidation LiteralProblem
HasDecidableValidationLiteralProblem = {!!}
