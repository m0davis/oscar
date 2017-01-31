{-# OPTIONS --allow-unsolved-metas #-}
module Problem where

open import OscarPrelude
open import Sequent

infix 13 _¶_
record Problem : Set
 where
  constructor _¶_
  field
    inferences : List Sequent
    interest : Sequent

open Problem public

instance EqProblem : Eq Problem
EqProblem = {!!}

open import 𝓐ssertion

instance 𝓐ssertionProblem : 𝓐ssertion Problem
𝓐ssertionProblem = record {}

open import HasSatisfaction

instance HasSatisfactionProblem : HasSatisfaction Problem
HasSatisfaction._⊨_ HasSatisfactionProblem I (Φ⁺s ¶ Φ⁻) = I ⊨ Φ⁺s → I ⊨ Φ⁻

open import HasDecidableValidation

instance HasDecidableValidationProblem : HasDecidableValidation Problem
HasDecidableValidationProblem = {!!}

open import HasSubstantiveDischarge

instance HasSubstantiveDischargeProblemProblem : HasSubstantiveDischarge Problem Problem
HasSubstantiveDischarge._≽_ HasSubstantiveDischargeProblemProblem (+s ¶ +) (-s ¶ -) = {!!} -- + ≽ - × +s ≽ -s

open import HasDecidableSubstantiveDischarge

instance HasDecidableSubstantiveDischargeProblemProblem : HasDecidableSubstantiveDischarge Problem Problem
HasDecidableSubstantiveDischarge._≽?_ HasDecidableSubstantiveDischargeProblemProblem = {!!}
