
open import Oscar.Prelude
open import Oscar.Data
open import Oscar.Class
open import Oscar.Data.ProductIndexEquivalence
import Oscar.Property.Setoid.ProductIndexEquivalence
import Oscar.Property.Setoid.ṖropertyEquivalence

module Oscar.Data.ExtensionṖroperty where

≡-ExtensionṖroperty : ∀
  {𝔵} {𝔛 : Ø 𝔵}
  {𝔬₁} ℓ (𝔒₁ : 𝔛 → Ø 𝔬₁)
  {𝔬₂} (𝔒₂ : 𝔛 → Ø 𝔬₂)
  → 𝔛
  → Ø 𝔵 ∙̂ 𝔬₁ ∙̂ 𝔬₂ ∙̂ ↑̂ ℓ
≡-ExtensionṖroperty ℓ 𝔒₁ 𝔒₂ x = ArrowExtensionṖroperty ℓ 𝔒₁ 𝔒₂ _≡_ x

module _
  {𝔵} {𝔛 : Ø 𝔵}
  {𝔬} {𝔒 : 𝔛 → Ø 𝔬}
  {ℓ}
  {ℓ̇} {_↦_ : ∀ {x} → 𝔒 x → 𝔒 x → Ø ℓ̇}
  where

  instance

    HasEquivalenceExtendedProperty : HasEquivalence (ExtensionṖroperty ℓ 𝔒 _↦_) (𝔵 ∙̂ 𝔬 ∙̂ ℓ)
    HasEquivalenceExtendedProperty .HasEquivalence.Equivalence = _≈₀_
