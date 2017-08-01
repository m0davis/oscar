
open import Oscar.Prelude
open import Oscar.Data.Proposequality

module Oscar.Class.Symmetrical where

module _
  {𝔞} {𝔄 : Ø 𝔞}
  𝔟
  {ℓ} (Symmetrical : 𝔄 → 𝔄 → Ø ℓ)
  where
  record [𝒮ymmetrical] : Ø 𝔞 ∙̂ ↑̂ (𝔟 ∙̂ ℓ) where
    constructor ∁
    infix 18 _∼_
    infix 14 _↦_
    field
      {𝔅} : Ø 𝔟
      _∼_ : 𝔄 → 𝔄 → 𝔅
      _↦_ : 𝔅 → 𝔅 → Ø ℓ
      ⦃ ⌶CorrectSymmetrical ⦄ : (λ x y → x ∼ y ↦ y ∼ x) ≡ Symmetrical

  module _
    ⦃ ⌶[𝒮ymmetrical] : [𝒮ymmetrical] ⦄
    where
    record 𝒮ymmetrical : Ø 𝔞 ∙̂ ℓ where
      field
        symmetrical : ∀ x y → Symmetrical x y

open 𝒮ymmetrical ⦃ … ⦄ public

module _
  {𝔞} {𝔄 : Ø 𝔞}
  {𝔟} {𝔅 : Ø 𝔟}
  (_∼_ : 𝔄 → 𝔄 → 𝔅) (let infix 18 _∼_; _∼_ = _∼_)
  {ℓ} (_↦_ : 𝔅 → 𝔅 → Ø ℓ) (let infix 14 _↦_; _↦_ = _↦_)
  where
  [𝓢ymmetrical] : Ø 𝔞 ∙̂ ↑̂ (𝔟 ∙̂ ℓ)
  [𝓢ymmetrical] = [𝒮ymmetrical] 𝔟 (λ x y → x ∼ y ↦ y ∼ x)
  𝓢ymmetrical : ⦃ _ : [𝓢ymmetrical] ⦄ → Ø 𝔞 ∙̂ ℓ
  𝓢ymmetrical = 𝒮ymmetrical 𝔟 (λ x y → x ∼ y ↦ y ∼ x)

explicit-symmetrical : ∀
  {𝔞} {𝔄 : Ø 𝔞}
  {𝔟} {𝔅 : Ø 𝔟}
  (_∼_ : 𝔄 → 𝔄 → 𝔅)
  {ℓ} (_↦_ : 𝔅 → 𝔅 → Ø ℓ)
  ⦃ _ : [𝓢ymmetrical] _∼_ _↦_ ⦄
  ⦃ _ : 𝓢ymmetrical _∼_ _↦_ ⦄
  → ∀ x y → (x ∼ y) ↦ (y ∼ x)
explicit-symmetrical _ _ = symmetrical
