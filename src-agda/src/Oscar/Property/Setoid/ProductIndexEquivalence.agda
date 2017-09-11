
open import Oscar.Prelude
open import Oscar.Class
open import Oscar.Class.HasEquivalence
open import Oscar.Class.Reflexivity
open import Oscar.Class.Symmetry
open import Oscar.Class.Transitivity
open import Oscar.Class.IsEquivalence
open import Oscar.Data.ProductIndexEquivalence
import Oscar.Data.Constraint

module Oscar.Property.Setoid.ProductIndexEquivalence where

module _ {𝔬} {𝔒 : Ø 𝔬} {𝔭} {𝔓 : 𝔒 → Ø 𝔭} {ℓ} ⦃ _ : HasEquivalence 𝔒 ℓ ⦄ where

  instance

    𝓡eflexivityExtensionṖropertyEquivalence : Reflexivity.class ProductIndexEquivalence⟦ 𝔒 / 𝔓 ⟧
    𝓡eflexivityExtensionṖropertyEquivalence .⋆ .π₀ = reflexivity

    𝓢ymmetryExtensionṖropertyEquivalence : 𝓢ymmetry ProductIndexEquivalence⟦ 𝔒 / 𝔓 ⟧
    𝓢ymmetryExtensionṖropertyEquivalence {x∼y = ∁ P≈Q} .⋆ .π₀ = symmetry P≈Q

    𝓣ransitivityExtensionṖropertyEquivalence : Transitivity.class ProductIndexEquivalence⟦ 𝔒 / 𝔓 ⟧
    𝓣ransitivityExtensionṖropertyEquivalence .⋆ (∁ P≈Q) (∁ Q≈R) .π₀ = transitivity P≈Q Q≈R

    IsEquivalenceExtensionṖroperty : IsEquivalence ProductIndexEquivalence⟦ 𝔒 / 𝔓 ⟧
    IsEquivalenceExtensionṖroperty = ∁
