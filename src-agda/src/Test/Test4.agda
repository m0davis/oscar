
open import Oscar.Prelude
open import Oscar.Class.Surjectextensivity
open import Oscar.Class.Transitivity
import Oscar.Class.Surjectivity.TransitiveExtensionLeftṖroperty
import Oscar.Class.Surjectextensivity.SurjectivityExtension

module Test.Test4
  {𝔵} {𝔛 : Ø 𝔵}
  {𝔞} {𝔒₁ : 𝔛 → Ø 𝔞}
  {𝔟} {𝔒₂ : 𝔛 → Ø 𝔟}
  {ℓ : Ł}
  ⦃ _ : 𝓣ransitivity (Arrow 𝔒₁ 𝔒₂) ⦄
  -- ⦃ _ : [𝓢urjectivity] (Arrow 𝔒₁ 𝔒₂) (Extension $ ArrowṖroperty ℓ 𝔒₁ 𝔒₂) ⦄
  where
  test[∙] : ∀ {x y} → ArrowṖroperty ℓ 𝔒₁ 𝔒₂ x → Arrow 𝔒₁ 𝔒₂ x y → ArrowṖroperty ℓ 𝔒₁ 𝔒₂ y
  test[∙] P f .π₀ g = (f ◃ P) .π₀ g
