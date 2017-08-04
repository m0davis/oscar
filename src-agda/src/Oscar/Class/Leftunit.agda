
open import Oscar.Prelude
open import Oscar.Data.Constraint

module Oscar.Class.Leftunit where

private

  module _
    {𝔞} {𝔄 : Ø 𝔞} {𝔢} {𝔈 : Ø 𝔢} {ℓ}
    where
    module Main
      (_↦_ : 𝔄 → 𝔄 → Ø ℓ)
      (ε : 𝔈)
      (_◃_ : 𝔈 → 𝔄 → 𝔄)
      where
      𝓵eftunit = λ x → (ε ◃ x) ↦ x
      𝓁eftunit = ∀ {x} → 𝓵eftunit x
      record 𝓛eftunit
        ⦃ _ : Constraint _↦_ ⦄
        ⦃ _ : Constraint ε ⦄
        ⦃ _ : Constraint _◃_ ⦄
        : Ø 𝔞 ∙̂ ℓ
        where
        field ⋆ : 𝓁eftunit
      Leftunit : Ø _
      Leftunit = 𝓛eftunit
      leftunit⟦_/_⟧ : ⦃ _ : Leftunit ⦄ → 𝓁eftunit
      leftunit⟦_/_⟧ ⦃ ⌶ ⦄ = 𝓛eftunit.⋆ ⌶
    module Hidden
      {_↦_ : 𝔄 → 𝔄 → Ø ℓ}
      {ε : 𝔈}
      {_◃_ : 𝔈 → 𝔄 → 𝔄}
      where
      open Main _↦_ ε _◃_
      leftunit : ⦃ _ : Leftunit ⦄ → 𝓁eftunit
      leftunit = leftunit⟦_/_⟧

module LeftunitMain = Main
open Main public
open Hidden public
