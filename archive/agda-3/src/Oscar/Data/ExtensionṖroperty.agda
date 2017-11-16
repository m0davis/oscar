
open import Oscar.Prelude
open import Oscar.Data.Proposequality

module Oscar.Data.ExtensionṖroperty where

≡-ExtensionṖroperty : ∀
  {𝔵} {𝔛 : Ø 𝔵}
  {𝔬₁} ℓ (𝔒₁ : 𝔛 → Ø 𝔬₁)
  {𝔬₂} (𝔒₂ : 𝔛 → Ø 𝔬₂)
  → 𝔛
  → Ø 𝔵 ∙̂ 𝔬₁ ∙̂ 𝔬₂ ∙̂ ↑̂ ℓ
≡-ExtensionṖroperty ℓ 𝔒₁ 𝔒₂ x = ArrowExtensionṖroperty ℓ 𝔒₁ 𝔒₂ _≡_ x
