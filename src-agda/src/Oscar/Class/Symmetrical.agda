
open import Oscar.Prelude

module Oscar.Class.Symmetrical where

module _
  {𝔞} (𝔄 : Ø 𝔞)
  {𝔟} (𝔅 : Ø 𝔟)
  {ℓ} (_↦_ : 𝔅 → 𝔅 → Ø ℓ) (let _↦_ = _↦_ ; infix 14 _↦_)
  where
  record [𝓢ymmetrical] : Ø 𝔞 ∙̂ 𝔟 where
    constructor ∁
    infix 18 _∼_
    field
      _∼_ : 𝔄 → 𝔄 → 𝔅

  module _
    ⦃ ⌶[𝓢ymmetrical] : [𝓢ymmetrical] ⦄
    where
    record 𝓢ymmetrical : Ø 𝔞 ∙̂ ℓ where
      open [𝓢ymmetrical] ⌶[𝓢ymmetrical]
      field
        symmetrical : ∀ x y → x ∼ y ↦ y ∼ x

open 𝓢ymmetrical ⦃ … ⦄ public

explicit-symmetrical : ∀
  {𝔞} {𝔄 : Ø 𝔞}
  {𝔟} {𝔅 : Ø 𝔟}
  {ℓ} (_↦_ : 𝔅 → 𝔅 → Ø ℓ)
  (_∼_ : 𝔄 → 𝔄 → 𝔅)
  -- ⦃ _ : [𝓢ymmetrical] 𝔄 𝔅 _↦_ ⦄
  ⦃ _ : 𝓢ymmetrical 𝔄 𝔅 _↦_ ⦃ ∁ _∼_ ⦄ ⦄
  → ∀ x y → (x ∼ y) ↦ (y ∼ x)
explicit-symmetrical _↦_ _∼_ ⦃ I ⦄ x₁ y = symmetrical ⦃ r = I ⦄ x₁ y
