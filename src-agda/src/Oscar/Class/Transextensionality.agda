
open import Oscar.Prelude
open import Oscar.Class
open import Oscar.Class.Transitivity

module Oscar.Class.Transextensionality where

module Transextensionality
  {𝔬} {𝔒 : Ø 𝔬}
  {𝔯} (_∼_ : 𝔒 → 𝔒 → Ø 𝔯)
  {ℓ} (_∼̇_ : ∀ {x y} → x ∼ y → x ∼ y → Ø ℓ) (let infix 4 _∼̇_ ; _∼̇_ = _∼̇_)
  ⦃ tr : Transitivity.class _∼_ ⦄
  = ℭLASS ((λ {x y} → _∼̇_ {x} {y}) , λ {x y z x∼y y∼z} → tr {x} {y} {z} {x∼y} {y∼z}) -- FIXME what other possibilities work here?
          (∀ {x y z} {f₁ f₂ : x ∼ y} {g₁ g₂ : y ∼ z} → f₁ ∼̇ f₂ → g₁ ∼̇ g₂ → g₁ ∙ f₁ ∼̇ g₂ ∙ f₂)

module _
  {𝔬} {𝔒 : Ø 𝔬}
  {𝔯} {_∼_ : 𝔒 → 𝔒 → Ø 𝔯}
  {ℓ} {_∼̇_ : ∀ {x y} → x ∼ y → x ∼ y → Ø ℓ}
  ⦃ _ : Transitivity.class _∼_ ⦄
  where
  transextensionality = Transextensionality.method _∼_ _∼̇_ ⦃ ! ⦄
