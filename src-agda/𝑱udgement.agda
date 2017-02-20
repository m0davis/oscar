{-# OPTIONS --allow-unsolved-metas #-}
module 𝑱udgement where

open import OscarPrelude

infix 15 _⊢_
record 𝑱udgement (A : Set) : Set
 where
  constructor _⊢_
  field
    antecedents : List A
    consequent : A

open 𝑱udgement ⦃ … ⦄

instance Eq𝑱udgement : {A : Set} ⦃ _ : Eq A ⦄ → Eq (𝑱udgement A)
Eq._==_ Eq𝑱udgement (antecedents₁ ⊢ consequents₁) (antecedents₂ ⊢ consequents₂) = {!antecedents₁ ≟ antecedents₂!}

module _ where

  open import HasSatisfaction

  instance HasSatisfaction𝑱udgement : {A : Set} ⦃ _ : HasSatisfaction A ⦄ → HasSatisfaction (𝑱udgement A)
  HasSatisfaction._⊨_ HasSatisfaction𝑱udgement I (antecedents ⊢ consequent) = I ⊨ antecedents → I ⊨ consequent

  instance HasDecidableSatisfaction𝑱udgement : {A : Set} ⦃ _ : HasSatisfaction A ⦄ ⦃ _ : HasDecidableSatisfaction A ⦄ → HasDecidableSatisfaction (𝑱udgement A)
  HasDecidableSatisfaction._⊨?_ HasDecidableSatisfaction𝑱udgement I ([] ⊢ ι) with I ⊨? ι
  … | yes I⊨ι = yes (const I⊨ι)
  … | no I⊭ι = no (λ x → I⊭ι (x tt))
  HasDecidableSatisfaction._⊨?_ HasDecidableSatisfaction𝑱udgement I ((χ ∷ χs) ⊢ ι) with I ⊨? χ
  … | no I⊭χ = yes (λ { (I⊨χ , _) → ⊥-elim (I⊭χ I⊨χ)})
  … | yes I⊨χ with I ⊨? (χs ⊢ ι)
  … | yes I⊨χs⊢ι = yes λ { (I⊨χ , I⊨χs) → I⊨χs⊢ι I⊨χs}
  … | no I⊭χs⊢ι = no λ {I⊨χ∷χs⊢ι → I⊭χs⊢ι (λ I⊨χs → I⊨χ∷χs⊢ι (I⊨χ , I⊨χs))}

module _ where

  open import HasNegation

  instance HasNegation𝑱udgement : {A : Set} ⦃ hn' : HasNegation A ⦄ → HasNegation $ 𝑱udgement A
  HasNegation.~ HasNegation𝑱udgement (antecedents ⊢ consequent) = antecedents ⊢ ~ consequent

module _ where

  open import HasSubstantiveDischarge
  open import Membership

  instance HasSubstantiveDischarge𝑱udgement : {A : Set} ⦃ hsd : HasSubstantiveDischarge A ⦄ → HasSubstantiveDischarge (𝑱udgement A)
  HasSubstantiveDischarge.hasNegation HasSubstantiveDischarge𝑱udgement = it
  HasSubstantiveDischarge._o≽o_ HasSubstantiveDischarge𝑱udgement (antecedents₁ ⊢ consequent₁) (antecedents₂ ⊢ consequent₂) =
    ∃ λ sa₁ → sa₁ ⊆ antecedents₁ × ((consequent₁ ∷ sa₁) ≽ (consequent₂ ∷ antecedents₂))
    -- antecedents₂ ≽ antecedents₁ × consequent₁ ≽ consequent₂
  HasSubstantiveDischarge.≽-reflexive HasSubstantiveDischarge𝑱udgement (antecedents ⊢ consequent) = {!!} -- ⋆≽⋆-reflexive antecedents , ≽-reflexive consequent
  HasSubstantiveDischarge.≽-consistent HasSubstantiveDischarge𝑱udgement (a₁+ ⊢ c₁+) _ (_ , c+≽c-) (_ , c₁+≽~cx) = {!!} -- ≽-consistent c₁+ _ c+≽c- {!c₁+≽~cx!}
  HasSubstantiveDischarge.≽-contrapositive HasSubstantiveDischarge𝑱udgement = {!!}

  instance HasDecidableSubstantiveDischarge𝑱udgement : {A : Set} ⦃ _ : HasDecidableSubstantiveDischarge A ⦄ → HasDecidableSubstantiveDischarge $ 𝑱udgement A
  HasDecidableSubstantiveDischarge.hasSubstantiveDischarge HasDecidableSubstantiveDischarge𝑱udgement = it
  HasDecidableSubstantiveDischarge._≽?_ HasDecidableSubstantiveDischarge𝑱udgement (antecedents₁ ⊢ consequent₁) (antecedents₂ ⊢ consequent₂) = {!!}

module _ where

  open import HasSubstantiveDischarge
  open import HasSalvation

  instance HasSalvation𝑱udgement : {A : Set} ⦃ _ : HasSubstantiveDischarge A ⦄ → HasSalvation $ 𝑱udgement A
  HasSalvation.▷_ HasSalvation𝑱udgement (φᵖs ⊢ φᵗ) = (◁ φᵖs) ⊎ (φᵖs ≽ φᵗ)

  instance HasDecidableSalvation𝑱udgement : {A : Set} ⦃ _ : HasDecidableSubstantiveDischarge A ⦄ → HasDecidableSalvation $ 𝑱udgement A
  HasDecidableSalvation.hasSalvation HasDecidableSalvation𝑱udgement = it
  HasDecidableSalvation.▷?_ HasDecidableSalvation𝑱udgement (antecedents ⊢ consequent) with ◁? antecedents
  … | yes ◁antecedents = yes $ left ◁antecedents
  … | no ⋪antecedents with antecedents ⋆≽? consequent
  … | yes (_ , a∈antecedents , a≽consequent) = yes ∘ right $ _ , a∈antecedents , a≽consequent
  … | no antecedents⋡consequent = no (λ { (left ◁antecedents) → ⋪antecedents ◁antecedents ; (right antecedents≽consequent) → antecedents⋡consequent antecedents≽consequent})
