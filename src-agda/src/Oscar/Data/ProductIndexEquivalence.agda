
open import Oscar.Prelude
open import Oscar.Class.HasEquivalence

module Oscar.Data.ProductIndexEquivalence where

module _ {𝔬} {𝔒 : Ø 𝔬} {𝔭} {𝔓 : 𝔒 → Ø 𝔭} {ℓ} ⦃ _ : HasEquivalence 𝔒 ℓ ⦄  where

  record _≈₀_ (P Q : Σ 𝔒 𝔓) : Ø ℓ where
    constructor ∁
    field
      π₀ : π₀ P ≈ π₀ Q

  open _≈₀_ public

module _ {𝔬} (𝔒 : Ø 𝔬) {𝔭} (𝔓 : 𝔒 → Ø 𝔭) {ℓ} ⦃ _ : HasEquivalence 𝔒 ℓ ⦄  where

  ProductIndexEquivalence⟦_/_⟧ : (P Q : Σ 𝔒 𝔓) → Ø ℓ
  ProductIndexEquivalence⟦_/_⟧ = _≈₀_
