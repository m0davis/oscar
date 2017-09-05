
open import Oscar.Prelude
open import Oscar.Class.IsPrecategory
open import Oscar.Class.Reflexivity
open import Oscar.Class.Transleftidentity
open import Oscar.Class.Transrightidentity

module Oscar.Class.IsCategory where

module _
  {𝔬} {𝔒 : Ø 𝔬}
  {𝔯} (_∼_ : 𝔒 → 𝔒 → Ø 𝔯)
  {ℓ} (_∼̇_ : ∀ {x y} → x ∼ y → x ∼ y → Ø ℓ) (let infix 4 _∼̇_ ; _∼̇_ = _∼̇_)
  where
  record IsCategory : Ø 𝔬 ∙̂ 𝔯 ∙̂ ℓ where
    constructor ∁
    field
      ⦃ `IsPrecategory ⦄ : IsPrecategory _∼_ _∼̇_
      overlap ⦃ `[𝓣ransleftidentity] ⦄ : [𝓣ransleftidentity] _∼_ _∼̇_
      overlap ⦃ `[𝓣ransrightidentity] ⦄ : [𝓣ransrightidentity] _∼_ _∼̇_
      overlap ⦃ `𝓡eflexivity ⦄ : Reflexivity.class _∼_
      ⦃ `𝓣ransleftidentity ⦄ : 𝓣ransleftidentity _∼_ _∼̇_
      ⦃ `𝓣ransrightidentity ⦄ : 𝓣ransrightidentity _∼_ _∼̇_
