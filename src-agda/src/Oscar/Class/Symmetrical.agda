
open import Oscar.Prelude
open import Oscar.Data.Proposequality

module Oscar.Class.Symmetrical where

module _
  {𝔞} {𝔄 : Ø 𝔞}
  {𝔟} {𝔅 : Ø 𝔟}
  where
  module _
    (_∼_ : 𝔄 → 𝔄 → 𝔅)
    {ℓ} (_↦_ : 𝔅 → 𝔅 → Ø ℓ)
    where
    record 𝓢ymmetrical
      {S : 𝔄 → 𝔄 → Ø ℓ}
      ⦃ _ : S ≡ (λ x y → (x ∼ y) ↦ (y ∼ x)) ⦄
      : Ø 𝔞 ∙̂ ℓ
      where
      field symmetrical : ∀ x y → S x y -- (x ∼ y) ↦ (y ∼ x)
      -- FIXME is there any reason to prefer (x ∼ y) ↦ (y ∼ x) to S x y (or vice-versa)?
    Symmetrical : Ø 𝔞 ∙̂ ℓ
    Symmetrical = 𝓢ymmetrical ⦃ ∅ ⦄
    symmetrical⟦_/_⟧ : ⦃ _ : Symmetrical ⦄ → ∀ x y → (x ∼ y) ↦ (y ∼ x)
    symmetrical⟦_/_⟧ ⦃ I ⦄ = 𝓢ymmetrical.symmetrical I
  module _
    {_∼_ : 𝔄 → 𝔄 → 𝔅}
    {ℓ} {_↦_ : 𝔅 → 𝔅 → Ø ℓ}
    where
    symmetrical : ⦃ _ : Symmetrical _∼_ _↦_ ⦄ → ∀ x y → (x ∼ y) ↦ (y ∼ x)
    symmetrical = symmetrical⟦ _ / _ ⟧
