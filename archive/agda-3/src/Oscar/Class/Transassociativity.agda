
open import Oscar.Prelude
open import Oscar.Class
open import Oscar.Class.Transitivity

module Oscar.Class.Transassociativity where

module Transassociativity
  {𝔬} {𝔒 : Ø 𝔬}
  {𝔯} (_∼_ : 𝔒 → 𝔒 → Ø 𝔯)
  {ℓ} (_∼̇_ : ∀ {x y} → x ∼ y → x ∼ y → Ø ℓ) (let infix 4 _∼̇_ ; _∼̇_ = _∼̇_)
  (transitivity : Transitivity.type _∼_) (let infixr 9 _∙_ ; _∙_ : FlipTransitivity.type _∼_; _∙_ g f = transitivity f g)
  = ℭLASS (λ {x y} → _∼̇_ {x} {y} , (λ {x y z} → transitivity {x} {y} {z}))
          (∀ {w x y z} (f : w ∼ x) (g : x ∼ y) (h : y ∼ z) → (h ∙ g) ∙ f ∼̇ h ∙ g ∙ f)

module _
  {𝔬} {𝔒 : Ø 𝔬}
  {𝔯} {_∼_ : 𝔒 → 𝔒 → Ø 𝔯}
  {ℓ} {_∼̇_ : ∀ {x y} → x ∼ y → x ∼ y → Ø ℓ}
  {transitivity : Transitivity.type _∼_}
  where
  transassociativity = Transassociativity.method _∼_ _∼̇_ transitivity
  syntax transassociativity f g h = h ⟨∙ g ⟨∙ f

module Transassociativity!
  {𝔬} {𝔒 : Ø 𝔬}
  {𝔯} (_∼_ : 𝔒 → 𝔒 → Ø 𝔯)
  {ℓ} (_∼̇_ : ∀ {x y} → x ∼ y → x ∼ y → Ø ℓ)
  ⦃ _ : Transitivity.class _∼_ ⦄
  = Transassociativity (_∼_) (_∼̇_) transitivity

module _
  {𝔬} {𝔒 : Ø 𝔬}
  {𝔯} {_∼_ : 𝔒 → 𝔒 → Ø 𝔯}
  {ℓ} (_∼̇_ : ∀ {x y} → x ∼ y → x ∼ y → Ø ℓ)
  ⦃ _ : Transitivity.class _∼_ ⦄
  where
  transassociativity![_] = Transassociativity.method _∼_ _∼̇_ transitivity
