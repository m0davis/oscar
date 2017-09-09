
open import Oscar.Prelude
open import Oscar.Class.Transitivity
open import Oscar.Class.Transextensionality
open import Oscar.Class.Transassociativity

module Oscar.Class.IsPrecategory where

module _
  {𝔬} {𝔒 : Ø 𝔬}
  {𝔯} (_∼_ : 𝔒 → 𝔒 → Ø 𝔯)
  {ℓ} (_∼̇_ : ∀ {x y} → x ∼ y → x ∼ y → Ø ℓ) (let infix 4 _∼̇_ ; _∼̇_ = _∼̇_)
  (_↦_ : Transitivity.type _∼_)
  where
  record IsPrecategory : Ø 𝔬 ∙̂ 𝔯 ∙̂ ℓ where
    constructor ∁
    field
      ⦃ `𝓣ransextensionality ⦄ : Transextensionality.class _∼_ _∼̇_ _↦_
      ⦃ `𝓣ransassociativity ⦄ : Transassociativity.class _∼_ _∼̇_ _↦_
