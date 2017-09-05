
open import Oscar.Prelude
open import Oscar.Class.Reflexivity
open import Oscar.Class.Transitivity

module Oscar.Class.Transrightidentity where

module _
  {𝔬} {𝔒 : Ø 𝔬}
  {𝔯} (_∼_ : 𝔒 → 𝔒 → Ø 𝔯)
  {ℓ} (_∼̇_ : ∀ {x y} → x ∼ y → x ∼ y → Ø ℓ) (let infix 4 _∼̇_ ; _∼̇_ = _∼̇_)
  where
  record [𝓣ransrightidentity] : Ø₀ where
    no-eta-equality
    constructor ∁
  module _
    ⦃ _ : 𝓡eflexivity _∼_ ⦄
    ⦃ _ : Transitivity.class _∼_ ⦄
    where
    𝓽ransrightidentity = ∀ {x y} {f : x ∼ y} → f ∙ ε ∼̇ f
    record 𝓣ransrightidentity ⦃ _ : [𝓣ransrightidentity] ⦄ : Ø 𝔬 ∙̂ 𝔯 ∙̂ ℓ where field transrightidentity : 𝓽ransrightidentity
open 𝓣ransrightidentity ⦃ … ⦄ public

transrightidentity[_] : ∀
  {𝔬} {𝔒 : Ø 𝔬}
  {𝔯} {_∼_ : 𝔒 → 𝔒 → Ø 𝔯}
  {ℓ} (_∼̇_ : ∀ {x y} → x ∼ y → x ∼ y → Ø ℓ)
  ⦃ _ : 𝓡eflexivity _∼_ ⦄
  ⦃ _ : Transitivity.class _∼_ ⦄
  ⦃ _ : [𝓣ransrightidentity] _∼_ _∼̇_ ⦄
  ⦃ _ : 𝓣ransrightidentity _∼_ _∼̇_ ⦄
  → 𝓽ransrightidentity _∼_ _∼̇_
transrightidentity[ _ ] = transrightidentity
