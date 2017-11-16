
open import Oscar.Prelude
open import Oscar.Class
open import Oscar.Class.Transitivity

module Oscar.Class.Transextensionality where

module Transextensionality
  {𝔬} {𝔒 : Ø 𝔬}
  {𝔯} (_∼_ : 𝔒 → 𝔒 → Ø 𝔯)
  {ℓ} (_∼̇_ : ∀ {x y} → x ∼ y → x ∼ y → Ø ℓ) (let infix 4 _∼̇_ ; _∼̇_ = _∼̇_)
  (transitivity : Transitivity.type _∼_)
  (let _∙_ : FlipTransitivity.type _∼_
       _∙_ g f = transitivity f g)
  = ℭLASS ((λ {x y} → _∼̇_ {x} {y}) , λ {x y z} → transitivity {x} {y} {z}) -- FIXME what other possibilities work here?
          (∀ {x y z} {f₁ f₂ : x ∼ y} {g₁ g₂ : y ∼ z} → f₁ ∼̇ f₂ → g₁ ∼̇ g₂ → g₁ ∙ f₁ ∼̇ g₂ ∙ f₂)

module Transextensionality!
  {𝔬} {𝔒 : Ø 𝔬}
  {𝔯} (_∼_ : 𝔒 → 𝔒 → Ø 𝔯)
  {ℓ} (_∼̇_ : ∀ {x y} → x ∼ y → x ∼ y → Ø ℓ) (let infix 4 _∼̇_ ; _∼̇_ = _∼̇_)
  ⦃ tr : Transitivity.class _∼_ ⦄
  = Transextensionality (_∼_) (λ {x y} → _∼̇_ {x} {y}) transitivity

module _
  {𝔬} {𝔒 : Ø 𝔬}
  {𝔯} {_∼_ : 𝔒 → 𝔒 → Ø 𝔯}
  {ℓ} {_∼̇_ : ∀ {x y} → x ∼ y → x ∼ y → Ø ℓ}
  {transitivity : Transitivity.type _∼_}
  where
  transextensionality = Transextensionality.method _∼_ _∼̇_ transitivity
