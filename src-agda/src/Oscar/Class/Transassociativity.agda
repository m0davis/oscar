
open import Oscar.Prelude
open import Oscar.Class.Transitivity

module Oscar.Class.Transassociativity where

module _
  {𝔬} {𝔒 : Ø 𝔬}
  {𝔯} (_∼_ : 𝔒 → 𝔒 → Ø 𝔯)
  {ℓ} (_∼̇_ : ∀ {x y} → x ∼ y → x ∼ y → Ø ℓ) (let infix 4 _∼̇_ ; _∼̇_ = _∼̇_)
  where
  record [𝓣ransassociativity] : Ø₀ where
    no-eta-equality
    constructor ∁
  module _
    ⦃ _ : 𝓣ransitivity _∼_ ⦄
    where
    𝓽ransassociativity = ∀ {w x y z} (f : w ∼ x) (g : x ∼ y) (h : y ∼ z) → (h ∙ g) ∙ f ∼̇ h ∙ g ∙ f
    record 𝓣ransassociativity ⦃ _ : [𝓣ransassociativity] ⦄ : Ø 𝔬 ∙̂ 𝔯 ∙̂ ℓ where
      field transassociativity : 𝓽ransassociativity
      syntax transassociativity f g h = h ⟨∙ g ⟨∙ f
open 𝓣ransassociativity ⦃ … ⦄ public

transassociativity[_] : ∀
  {𝔬} {𝔒 : Ø 𝔬}
  {𝔯} {_∼_ : 𝔒 → 𝔒 → Ø 𝔯}
  {ℓ} (_∼̇_ : ∀ {x y} → x ∼ y → x ∼ y → Ø ℓ)
  ⦃ _ : 𝓣ransitivity _∼_ ⦄
  ⦃ _ : [𝓣ransassociativity] _∼_ _∼̇_ ⦄
  ⦃ _ : 𝓣ransassociativity _∼_ _∼̇_ ⦄
  → 𝓽ransassociativity _∼_ _∼̇_
transassociativity[ _ ] = transassociativity
