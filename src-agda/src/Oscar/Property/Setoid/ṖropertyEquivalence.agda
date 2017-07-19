
open import Oscar.Prelude
open import Oscar.Class
open import Oscar.Data

module Oscar.Property.Setoid.ṖropertyEquivalence where

module _
  {𝔵} {𝔛 : Ø 𝔵}
  {𝔬} {𝔒 : 𝔛 → Ø 𝔬}
  {ℓ : Ł}
  where

  instance

    𝓡eflexivityṖroperty : 𝓡eflexivity ṖropertyEquivalence⟦ 𝔒 / ℓ ⟧
    𝓡eflexivityṖroperty .𝓡eflexivity.reflexivity .π₀ = ¡ , ¡

    𝓢ymmetryṖroperty : 𝓢ymmetry ṖropertyEquivalence⟦ 𝔒 / ℓ ⟧
    𝓢ymmetryṖroperty .𝓢ymmetry.symmetry (∁ P⇔Q) .π₀ = π₁ P⇔Q , π₀ P⇔Q

    𝓣ransitivityṖroperty : 𝓣ransitivity ṖropertyEquivalence⟦ 𝔒 / ℓ ⟧
    𝓣ransitivityṖroperty .𝓣ransitivity.transitivity (∁ P⇔Q) (∁ Q⇔R) .π₀ = π₀ Q⇔R ∘ π₀ P⇔Q , π₁ P⇔Q ∘ π₁ Q⇔R

    IsEquivalenceṖroperty : IsEquivalence ṖropertyEquivalence⟦ 𝔒 / ℓ ⟧
    IsEquivalenceṖroperty = ∁

instance

  HasEquivalenceṖroperty : ∀
    {𝔵} {𝔛 : Ø 𝔵}
    {𝔬} {𝔒 : 𝔛 → Ø 𝔬}
    {ℓ}
    → HasEquivalence (Ṗroperty ℓ 𝔒) (𝔵 ∙̂ 𝔬 ∙̂ ℓ)
  HasEquivalenceṖroperty .HasEquivalence.Equivalence P Q = ṖropertyEquivalence P Q
