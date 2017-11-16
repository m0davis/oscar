
open import Oscar.Prelude
open import Oscar.Class.IsPrecategory
open import Oscar.Class.Reflexivity
open import Oscar.Class.Transleftidentity
open import Oscar.Class.Transrightidentity
open import Oscar.Class.Transitivity

module Oscar.Class.IsCategory where

module _
  {𝔬} {𝔒 : Ø 𝔬}
  {𝔯} (_∼_ : 𝔒 → 𝔒 → Ø 𝔯)
  {ℓ} (_∼̇_ : ∀ {x y} → x ∼ y → x ∼ y → Ø ℓ) (let infix 4 _∼̇_ ; _∼̇_ = _∼̇_)
  (ε : Reflexivity.type _∼_)
  (_↦_ : Transitivity.type _∼_)
  where
  record IsCategory : Ø 𝔬 ∙̂ 𝔯 ∙̂ ℓ where
    constructor ∁
    field
      ⦃ `IsPrecategory ⦄ : IsPrecategory _∼_ _∼̇_ _↦_
      ⦃ `𝓣ransleftidentity ⦄ : Transleftidentity.class _∼_ _∼̇_ ε _↦_
      ⦃ `𝓣ransrightidentity ⦄ : Transrightidentity.class _∼_ _∼̇_ ε _↦_
