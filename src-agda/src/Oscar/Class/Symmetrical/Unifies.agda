
open import Oscar.Prelude
open import Oscar.Class.HasEquivalence
open import Oscar.Class.Surjectivity
open import Oscar.Class.Symmetry
open import Oscar.Class.Symmetrical
open import Oscar.Data.Unifies
import Oscar.Class.Surjection
import Oscar.Property.Setoid.ṖropertyEquivalence

module Oscar.Class.Symmetrical.Unifies where

instance

  𝓢ymmetricalUnifies₀ : ∀
    {𝔵} {𝔛 : Ø 𝔵}
    {𝔞} {𝔄 : 𝔛 → 𝔛 → Ø 𝔞}
    {𝔠} {ℭ : 𝔛 → Ø 𝔠}
    ⦃ _ : [𝓢urjectivity] 𝔄 (Extension ℭ) ⦄
    ⦃ _ : 𝓢urjectivity 𝔄 (Extension ℭ) ⦄
    {ℓ} {_≈'_ : ∀ {y} → ℭ y → ℭ y → Ø ℓ}
    ⦃ _ : ∀ {y} → 𝓢ymmetry (_≈'_ {y}) ⦄
    → ∀ {m} → 𝓢ymmetrical (ℭ m) (λ s t t' s' → Unifies₀⟦ 𝔄 ⟧ _≈'_ s t ≈ Unifies₀ _≈'_ t' s')
  𝓢ymmetricalUnifies₀ .𝓢ymmetrical.symmetrical x y .π₀ = symmetry , symmetry
