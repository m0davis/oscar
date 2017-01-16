
module 𝓢equent where

open import OscarPrelude
open import 𝓐ssertion

infix 15 _⊢_
record 𝓢equent (A : Set) ⦃ _ : 𝓐ssertion A ⦄ : Set
 where
  constructor _⊢_
  field
    antecedents : List A
    consequents : List A

open 𝓢equent ⦃ … ⦄

instance Eq𝓢equent : {A : Set} ⦃ _ : Eq A ⦄ ⦃ _ : 𝓐ssertion A ⦄ → Eq (𝓢equent A)
Eq._==_ Eq𝓢equent (antecedents₁ ⊢ consequents₁) (antecedents₂ ⊢ consequents₂) = {!antecedents₁ ≟ antecedents₂!}

instance 𝓐ssertion𝓢equent : {A : Set} ⦃ _ : 𝓐ssertion A ⦄ → 𝓐ssertion (𝓢equent A)
𝓐ssertion𝓢equent = record {}

open import HasSalvation
open import HasSubstantiveDischarge
open import HasNegation
open import HasVacuousDischarge

instance HasSalvation𝓢equent : {A : Set} ⦃ _ : 𝓐ssertion A ⦄ ⦃ _ : HasSubstantiveDischarge A A ⦄ ⦃ _ : HasNegation A ⦄ ⦃ _ : HasVacuousDischarge A ⦄ → HasSalvation $ 𝓢equent A
HasSalvation.▷_ HasSalvation𝓢equent (φᵖs ⊢ φᵗs) = (◁ φᵖs) ⊎ (φᵖs ≽ φᵗs)

open import HasDecidableVacuousDischarge

instance HasDecidableVacuousDischarge𝓢equent : {A : Set} ⦃ _ : 𝓐ssertion A ⦄ ⦃ _ : Eq A ⦄ ⦃ _ : HasNegation (𝓢equent A) ⦄ ⦃ _ : HasSubstantiveDischarge (𝓢equent A) (𝓢equent A) ⦄ ⦃ _ : HasVacuousDischarge (𝓢equent A) ⦄ → HasDecidableVacuousDischarge (𝓢equent A)
HasDecidableVacuousDischarge𝓢equent = {!!}
