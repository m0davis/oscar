
module 𝑱udgement where

open import OscarPrelude
open import 𝓐ssertion

infix 15 _⊢_
record 𝑱udgement (A : Set) ⦃ _ : 𝓐ssertion A ⦄ : Set
 where
  constructor _⊢_
  field
    antecedents : List A
    consequent : A

open 𝑱udgement ⦃ … ⦄

instance Eq𝑱udgement : {A : Set} ⦃ _ : Eq A ⦄ ⦃ _ : 𝓐ssertion A ⦄ → Eq (𝑱udgement A)
Eq._==_ Eq𝑱udgement (antecedents₁ ⊢ consequents₁) (antecedents₂ ⊢ consequents₂) = {!antecedents₁ ≟ antecedents₂!}

instance 𝓐ssertion𝑱udgement : {A : Set} ⦃ _ : 𝓐ssertion A ⦄ → 𝓐ssertion (𝑱udgement A)
𝓐ssertion𝑱udgement = record {}

open import HasSatisfaction

instance HasSatisfaction𝑱udgement : {A : Set} ⦃ _ : 𝓐ssertion A ⦄ ⦃ _ : HasSatisfaction A ⦄ → HasSatisfaction (𝑱udgement A)
HasSatisfaction._⊨_ HasSatisfaction𝑱udgement I (antecedents ⊢ consequent) = I ⊨ antecedents → I ⊨ consequent

open import HasSalvation
open import HasSubstantiveDischarge
open import HasNegation
open import HasVacuousDischarge

instance HasNegation𝑱udgement : {A : Set} ⦃ _ : 𝓐ssertion A ⦄ ⦃ _ : HasNegation A ⦄ → HasNegation $ 𝑱udgement A
HasNegation𝑱udgement = {!!}

instance HasSubstantiveDischarge𝑱udgement : {A : Set} ⦃ _ : 𝓐ssertion A ⦄ ⦃ _ : HasSubstantiveDischarge A A ⦄ → HasSubstantiveDischarge (𝑱udgement A) (𝑱udgement A)
HasSubstantiveDischarge𝑱udgement = {!!}

instance HasVacuousDischarge𝑱udgement : {A : Set} ⦃ _ : 𝓐ssertion A ⦄ ⦃ _ : HasNegation A ⦄ ⦃ _ : HasSubstantiveDischarge A A ⦄ → HasVacuousDischarge (𝑱udgement A)
HasVacuousDischarge𝑱udgement = {!!}

instance HasSalvation𝑱udgement : {A : Set} ⦃ _ : 𝓐ssertion A ⦄ ⦃ _ : HasSubstantiveDischarge A A ⦄ ⦃ _ : HasNegation A ⦄ ⦃ _ : HasVacuousDischarge A ⦄ → HasSalvation $ 𝑱udgement A
HasSalvation.▷_ HasSalvation𝑱udgement (φᵖs ⊢ φᵗ) = (◁ φᵖs) ⊎ (φᵖs ≽ φᵗ)
