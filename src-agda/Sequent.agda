
module Sequent where

open import OscarPrelude
open import Formula

infix 15 _╱_
record Sequent : Set
 where
  constructor _╱_
  field
    statement : Formula
    suppositions : List Formula

open Sequent public

instance EqSequent : Eq Sequent
Eq._==_ EqSequent ( φᵗ₁ ╱ φˢs₁ ) ( φᵗ₂ ╱ φˢs₂ ) = decEq₂ (cong statement) (cong suppositions) (φᵗ₁ ≟ φᵗ₂) (φˢs₁ ≟ φˢs₂)

open import HasNegation

instance HasNegationSequent : HasNegation Sequent
HasNegation.~ HasNegationSequent ( φᵗ ╱ φˢs ) = ~ φᵗ ╱ φˢs

open import 𝓐ssertion

instance 𝓐ssertionSequent : 𝓐ssertion Sequent
𝓐ssertionSequent = record {}

open import HasSatisfaction

instance HasSatisfactionSequent : HasSatisfaction Sequent
HasSatisfaction._⊨_ HasSatisfactionSequent I (φᵗ ╱ φˢs) = I ⊨ φˢs → I ⊨ φᵗ

open import HasDecidableValidation

instance HasDecidableValidationSequent : HasDecidableValidation Sequent
HasDecidableValidationSequent = {!!}
