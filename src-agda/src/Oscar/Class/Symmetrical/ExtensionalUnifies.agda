
open import Oscar.Prelude
open import Oscar.Class.HasEquivalence
open import Oscar.Class.Smap
open import Oscar.Class.Surjextensionality
open import Oscar.Class.Symmetry
open import Oscar.Class.Symmetrical
open import Oscar.Class.Transitivity
open import Oscar.Data.ProductIndexEquivalence
open import Oscar.Data.Surjextenscollation
import Oscar.Class.HasEquivalence.ExtensionṖroperty
import Oscar.Class.Surjection.⋆
import Oscar.Data.ExtensionṖroperty
import Oscar.Data.Proposequality

module Oscar.Class.Symmetrical.ExtensionalUnifies where

module _
    {𝔵} {𝔛 : Ø 𝔵}
    {𝔞} {𝔄 : 𝔛 → Ø 𝔞}
    {𝔟} {𝔅 : 𝔛 → Ø 𝔟}
    (let _↦_ = Arrow 𝔄 𝔅)
    {𝔠} {ℭ : 𝔛 → Ø 𝔠}
    {ℓ₁} {_↦̇_ : ∀ {x y} → x ↦ y → x ↦ y → Ø ℓ₁}
    {ℓ₂} {_∼₂_ : ∀ {y} → ℭ y → ℭ y → Ø ℓ₂}
    ⦃ _ : ∀ {y} → 𝓢ymmetry (_∼₂_ {y}) ⦄
    ⦃ _ : ∀ {y} → 𝓣ransitivity (_∼₂_ {y}) ⦄
    ⦃ _ : Surjectivity!.class _↦_ (Extension ℭ) ⦄
    ⦃ _ : Surjextensionality!.class _↦_ _↦̇_ (Extension ℭ) (Pointwise _∼₂_) ⦄
  where

  instance

    𝓢ymmetricalExtensionalUnifies : ∀ {m} → Symmetrical {𝔄 = (ℭ m)} {𝔅 = (LeftExtensionṖroperty ℓ₂ _↦_ _↦̇_ m)} surjextenscollation⟦ _↦̇_ ⟧ _≈_
    𝓢ymmetricalExtensionalUnifies .𝓢ymmetrical.symmetrical x y .π₀ = ∁ (symmetry , symmetry)
