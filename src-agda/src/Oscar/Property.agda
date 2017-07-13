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

  postulate
    ṖropertyEquivalence : Ṗroperty ℓ 𝔒 → Ṗroperty ℓ 𝔒 → Ø 𝔵 ∙̂ 𝔬 ∙̂ ℓ
    instance 𝓢ymmetryṖroperty : 𝓢ymmetry ṖropertyEquivalence

module _
  {𝔵} {𝔛 : Ø 𝔵}
  {𝔬} {𝔒 : 𝔛 → Ø 𝔬}
  {ℓ}
  {ℓ̇} {_↦_ : ∀ {x} → 𝔒 x → 𝔒 x → Ø ℓ̇}
  where

  ExtensionṖropertyEquivalence : ExtensionṖroperty ℓ 𝔒 _↦_ → ExtensionṖroperty ℓ 𝔒 _↦_ → Ø 𝔵 ∙̂ 𝔬 ∙̂ ℓ
  ExtensionṖropertyEquivalence P Q = ṖropertyEquivalence (π₀ P) (π₀ Q)

  postulate
    instance
      𝓢ymmetryExtensionṖroperty : 𝓢ymmetry ExtensionṖropertyEquivalence
      IsEquivalenceExtensionṖroperty : IsEquivalence ExtensionṖropertyEquivalence

  instance

    HasEquivalenceExtendedProperty : HasEquivalence (ExtensionṖroperty ℓ 𝔒 _↦_) (𝔵 ∙̂ 𝔬 ∙̂ ℓ)
    HasEquivalenceExtendedProperty .HasEquivalence.Equivalence P Q = ExtensionṖropertyEquivalence P Q
