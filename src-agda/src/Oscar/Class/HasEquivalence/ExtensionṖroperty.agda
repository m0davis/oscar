
open import Oscar.Prelude
open import Oscar.Class
open import Oscar.Data.ProductIndexEquivalence
import Oscar.Property.Setoid.ProductIndexEquivalence
import Oscar.Property.Setoid.ṖropertyEquivalence

module Oscar.Class.HasEquivalence.ExtensionṖroperty where

module _
  {𝔵} {𝔛 : Ø 𝔵}
  {𝔬} {𝔒 : 𝔛 → Ø 𝔬}
  {ℓ}
  {ℓ̇} {_↦_ : ∀ {x} → 𝔒 x → 𝔒 x → Ø ℓ̇}
  where

  instance

    HasEquivalenceExtendedProperty : HasEquivalence (ExtensionṖroperty ℓ 𝔒 _↦_) (𝔵 ∙̂ 𝔬 ∙̂ ℓ)
    HasEquivalenceExtendedProperty .HasEquivalence.Equivalence = _≈₀_
