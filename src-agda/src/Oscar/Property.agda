--{-# OPTIONS --show-implicit #-}
{-# OPTIONS --postfix-projections #-}
module Oscar.Property where

open import Oscar.Prelude
open import Oscar.Class

module _
  {𝔵} {𝔛 : Ø 𝔵}
  {𝔬} {𝔒 : 𝔛 → Ø 𝔬}
  {ℓ : Ł}
  where

  ṖropertyEquivalence : Ṗroperty ℓ 𝔒 → Ṗroperty ℓ 𝔒 → Ø 𝔵 ∙̂ 𝔬 ∙̂ ℓ
  ṖropertyEquivalence (∁ P) (∁ Q) = V (∀ {n f} → (P {n} f → Q f) × (Q f → P f))

  instance

    𝓡eflexivityṖroperty : 𝓡eflexivity ṖropertyEquivalence
    𝓡eflexivityṖroperty .𝓡eflexivity.reflexivity .π₀ = ¡ , ¡

    𝓢ymmetryṖroperty : 𝓢ymmetry ṖropertyEquivalence
    𝓢ymmetryṖroperty .𝓢ymmetry.symmetry (∁ P⇔Q) .π₀ = π₁ P⇔Q , π₀ P⇔Q

    𝓣ransitivityṖroperty : 𝓣ransitivity ṖropertyEquivalence
    𝓣ransitivityṖroperty .𝓣ransitivity.transitivity (∁ P⇔Q) (∁ Q⇔R) .π₀ = π₀ Q⇔R ∘ π₀ P⇔Q , π₁ P⇔Q ∘ π₁ Q⇔R

    IsEquivalenceṖroperty : IsEquivalence ṖropertyEquivalence
    IsEquivalenceṖroperty = ∁

instance

  HasEquivalenceṖroperty : ∀
    {𝔵} {𝔛 : Ø 𝔵}
    {𝔬} {𝔒 : 𝔛 → Ø 𝔬}
    {ℓ}
    → HasEquivalence (Ṗroperty ℓ 𝔒) (𝔵 ∙̂ 𝔬 ∙̂ ℓ)
  HasEquivalenceṖroperty .HasEquivalence.Equivalence P Q = ṖropertyEquivalence P Q

module _
  {𝔵} {𝔛 : Ø 𝔵}
  {𝔬} {𝔒 : 𝔛 → Ø 𝔬}
  {ℓ}
  {ℓ̇} {_↦_ : ∀ {x} → 𝔒 x → 𝔒 x → Ø ℓ̇}
  where

  ExtensionṖropertyEquivalence : ExtensionṖroperty ℓ 𝔒 _↦_ → ExtensionṖroperty ℓ 𝔒 _↦_ → Ø 𝔵 ∙̂ 𝔬 ∙̂ ℓ
  ExtensionṖropertyEquivalence P Q = π₀ P ≈ π₀ Q

  instance

    𝓡eflexivityExtensionṖroperty : 𝓡eflexivity ExtensionṖropertyEquivalence
    𝓡eflexivityExtensionṖroperty .𝓡eflexivity.reflexivity .π₀ = ¡ , ¡

    𝓢ymmetryExtensionṖroperty : 𝓢ymmetry ExtensionṖropertyEquivalence
    𝓢ymmetryExtensionṖroperty .𝓢ymmetry.symmetry (∁ P⇔Q) .π₀ = π₁ P⇔Q , π₀ P⇔Q

  𝓣ransitivityExtensionṖroperty' : 𝓣ransitivity ExtensionṖropertyEquivalence
  𝓣ransitivityExtensionṖroperty' .𝓣ransitivity.transitivity P⇔Q Q⇔R = transitivity P⇔Q Q⇔R

  instance

    𝓣ransitivityExtensionṖroperty : 𝓣ransitivity ExtensionṖropertyEquivalence
    𝓣ransitivityExtensionṖroperty = 𝓣ransitivityExtensionṖroperty'

    IsEquivalenceExtensionṖroperty : IsEquivalence ExtensionṖropertyEquivalence
    IsEquivalenceExtensionṖroperty = ∁

  instance

    HasEquivalenceExtendedProperty : HasEquivalence (ExtensionṖroperty ℓ 𝔒 _↦_) (𝔵 ∙̂ 𝔬 ∙̂ ℓ)
    HasEquivalenceExtendedProperty .HasEquivalence.Equivalence P Q = ExtensionṖropertyEquivalence P Q
