
open import Oscar.Prelude
open import Oscar.Class.HasEquivalence
open import Oscar.Class.Surjectivity
open import Oscar.Class.Symmetry
open import Oscar.Class.Symmetrical
open import Oscar.Data.Surjcollation
import Oscar.Class.HasEquivalence.Ṗroperty
import Oscar.Class.Surjection.⋆

module Oscar.Class.Symmetrical.Unifies where

module _
  {𝔵} {𝔛 : Ø 𝔵}
  {𝔞} {𝔄 : 𝔛 → 𝔛 → Ø 𝔞}
  {𝔠} {ℭ : 𝔛 → Ø 𝔠}
  ⦃ _ : [𝓢urjectivity] 𝔄 (Extension ℭ) ⦄
  ⦃ _ : 𝓢urjectivity 𝔄 (Extension ℭ) ⦄
  {ℓ} {_≈'_ : ∀ {y} → ℭ y → ℭ y → Ø ℓ}
  ⦃ _ : ∀ {y} → 𝓢ymmetry (_≈'_ {y}) ⦄
  where

  instance

    [𝓢ymmetrical]Unifies₀ : ∀ {m} → [𝓢ymmetrical] (ℭ m) (Ṗroperty ℓ (𝔄 m)) _≈_
    [𝓢ymmetrical]Unifies₀ .[𝓢ymmetrical]._∼_ = surjcollation⟦ _ / ∁ _≈'_ ⟧

    𝓢ymmetricalUnifies₀ : ∀ {m} → 𝓢ymmetrical (ℭ m) (Ṗroperty ℓ (𝔄 m)) _≈_
    𝓢ymmetricalUnifies₀ .𝓢ymmetrical.symmetrical x y .π₀ = symmetry , symmetry
