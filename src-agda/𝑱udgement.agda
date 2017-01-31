{-# OPTIONS --allow-unsolved-metas #-}
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

--infix 15 _⊢_
record 𝑱udgement' (A : Set) : Set
 where
  constructor _⊢_
  field
    ⦃ assertion ⦄ : 𝓐ssertion A
    antecedents : List A
    consequent : A

open 𝑱udgement' ⦃ … ⦄

instance Eq𝑱udgement : {A : Set} ⦃ _ : Eq A ⦄ ⦃ _ : 𝓐ssertion A ⦄ → Eq (𝑱udgement A)
Eq._==_ Eq𝑱udgement (antecedents₁ ⊢ consequents₁) (antecedents₂ ⊢ consequents₂) = {!antecedents₁ ≟ antecedents₂!}

instance 𝓐ssertion𝑱udgement : {A : Set} ⦃ _ : 𝓐ssertion A ⦄ → 𝓐ssertion (𝑱udgement A)
𝓐ssertion𝑱udgement = record {}

instance 𝓐ssertion𝑱udgement' : {A : Set} ⦃ _ : 𝓐ssertion A ⦄ → 𝓐ssertion (𝑱udgement' A)
𝓐ssertion𝑱udgement' = record {}

open import HasSatisfaction

instance HasSatisfaction𝑱udgement : {A : Set} ⦃ _ : 𝓐ssertion A ⦄ ⦃ _ : HasSatisfaction A ⦄ → HasSatisfaction (𝑱udgement A)
HasSatisfaction._⊨_ HasSatisfaction𝑱udgement I (antecedents ⊢ consequent) = I ⊨ antecedents → I ⊨ consequent

instance HasSatisfaction𝑱udgement' : {A : Set} ⦃ _ : HasSatisfaction' A ⦄ → HasSatisfaction' (𝑱udgement' A)
HasSatisfaction'._⊨'_ HasSatisfaction𝑱udgement' I (antecedents ⊢ consequent) = I ⊨' antecedents → I ⊨' consequent

open import HasSalvation
open import HasSubstantiveDischarge
open import HasNegation
open import HasVacuousDischarge

instance HasNegation𝑱udgement : {A : Set} ⦃ _ : 𝓐ssertion A ⦄ ⦃ _ : HasNegation A ⦄ → HasNegation $ 𝑱udgement A
HasNegation𝑱udgement = {!!}

instance HasNegation𝑱udgement' : {A : Set} ⦃ _ : HasNegation A ⦄ → HasNegation $ 𝑱udgement' A
HasNegation.~ HasNegation𝑱udgement' (antecedents₁ ⊢ consequent₁) = antecedents₁ ⊢ ~ consequent₁

instance HasSubstantiveDischarge𝑱udgement : {A : Set} ⦃ _ : 𝓐ssertion A ⦄ ⦃ _ : HasSubstantiveDischarge A A ⦄ → HasSubstantiveDischarge (𝑱udgement A) (𝑱udgement A)
HasSubstantiveDischarge𝑱udgement = {!!}

instance HasSubstantiveDischarge𝑱udgement' : {A : Set} ⦃ _ : HasSubstantiveDischarge A A ⦄ → HasSubstantiveDischarge (𝑱udgement' A) (𝑱udgement' A)
(HasSubstantiveDischarge𝑱udgement' HasSubstantiveDischarge.≽ (antecedents₁ ⊢ consequent₁)) (antecedents₂ ⊢ consequent₂) = antecedents₂ ≽ antecedents₁ × consequent₁ ≽ consequent₂

instance HasVacuousDischarge𝑱udgement : {A : Set} ⦃ _ : 𝓐ssertion A ⦄ ⦃ _ : HasNegation A ⦄ ⦃ _ : HasSubstantiveDischarge A A ⦄ → HasVacuousDischarge (𝑱udgement A)
HasVacuousDischarge𝑱udgement = {!!}

instance HasVacuousDischarge𝑱udgement' : {A : Set} ⦃ _ : HasNegation A ⦄ ⦃ _ : HasSubstantiveDischarge A A ⦄ → HasVacuousDischarge' (𝑱udgement' A)
HasVacuousDischarge'.hasSubstantiveDischarge HasVacuousDischarge𝑱udgement' = {!!}

instance HasSalvation𝑱udgement : {A : Set} ⦃ _ : 𝓐ssertion A ⦄ ⦃ _ : HasSubstantiveDischarge A A ⦄ ⦃ _ : HasNegation A ⦄ ⦃ _ : HasVacuousDischarge A ⦄ → HasSalvation $ 𝑱udgement A
HasSalvation.▷_ HasSalvation𝑱udgement (φᵖs ⊢ φᵗ) = (◁ φᵖs) ⊎ (φᵖs ≽ φᵗ)

instance HasSalvation𝑱udgement' : {A : Set} ⦃ _ : HasVacuousDischarge' A ⦄ → HasSalvation $ 𝑱udgement' A
HasSalvation.▷_ HasSalvation𝑱udgement' (φᵖs ⊢ φᵗ) = (◁ φᵖs) ⊎ (φᵖs ≽ φᵗ)

open import HasDecidableSalvation

instance HasDecidableSalvation'𝑱udgement' : {A : Set} ⦃ _ : HasVacuousDischarge' A ⦄ → HasDecidableSalvation' $ 𝑱udgement' A
(HasDecidableSalvation'.▷'? HasDecidableSalvation'𝑱udgement') (antecedents₁ ⊢ consequent₁) = {!!}
