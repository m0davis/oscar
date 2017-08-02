
open import Oscar.Prelude
open import Oscar.Data.Proposequality

module Oscar.Class.Leftunit where

private

  module _
    {𝔞} {𝔄 : Ø 𝔞} {ℓ}
    where
    module Main
      (_↦_ : 𝔄 → 𝔄 → Ø ℓ)
      (ε : 𝔄)
      (_◃_ : 𝔄 → 𝔄 → 𝔄)
      where
      𝓵eftunit = λ x → (ε ◃ x) ↦ x
      𝓁eftunit = ∀ {x} → 𝓵eftunit x
      record 𝓛eftunit
        {𝓛 : 𝔄 → Ø ℓ}
        ⦃ _ : 𝓛 ≡ 𝓵eftunit ⦄
        : Ø 𝔞 ∙̂ ℓ
        where
        field factsurj3 : 𝓁eftunit
      Leftunit : Ø _
      Leftunit = 𝓛eftunit ⦃ ∅ ⦄
      leftunit⟦_/_⟧ : ⦃ _ : Leftunit ⦄ → 𝓁eftunit
      leftunit⟦_/_⟧ = 𝓛eftunit.factsurj3 ⦃ ∅ ⦄ !
    module Hidden
      {_↦_ : 𝔄 → 𝔄 → Ø ℓ}
      {ε : 𝔄}
      {_◃_ : 𝔄 → 𝔄 → 𝔄}
      where
      open Main _↦_ ε _◃_
      leftunit : ⦃ _ : Leftunit ⦄ → 𝓁eftunit
      leftunit = leftunit⟦_/_⟧

module LeftunitMain = Main
open Main public
open Hidden public
