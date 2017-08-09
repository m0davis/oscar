
open import Oscar.Prelude
open import Oscar.Class
open import Oscar.Class.Reflexivity
open import Oscar.Class.Symmetry
open import Oscar.Class.Transitivity
open import Oscar.Class.IsEquivalence
open import Oscar.Data.ṖropertyEquivalence

module Oscar.Property.Setoid.ṖropertyEquivalence where

module _
  {𝔵} {𝔛 : Ø 𝔵}
  {𝔬} {𝔒 : 𝔛 → Ø 𝔬}
  {ℓ : Ł}
  where

  instance

    𝓡eflexivityṖroperty : 𝓡eflexivity ṖropertyEquivalence⟦ 𝔒 / ℓ ⟧
    𝓡eflexivityṖroperty .⋆ .π₀ = ¡ , ¡

    𝓢ymmetryṖroperty : 𝓢ymmetry ṖropertyEquivalence⟦ 𝔒 / ℓ ⟧
    𝓢ymmetryṖroperty {x∼y = ∁ P⇔Q} .⋆ .π₀ = π₁ P⇔Q , π₀ P⇔Q

    𝓣ransitivityṖroperty : 𝓣ransitivity ṖropertyEquivalence⟦ 𝔒 / ℓ ⟧
    𝓣ransitivityṖroperty .𝓣ransitivity.transitivity (∁ P⇔Q) (∁ Q⇔R) .π₀ = π₀ Q⇔R ∘ π₀ P⇔Q , π₁ P⇔Q ∘ π₁ Q⇔R

    IsEquivalenceṖroperty : IsEquivalence ṖropertyEquivalence⟦ 𝔒 / ℓ ⟧
    IsEquivalenceṖroperty = ∁
