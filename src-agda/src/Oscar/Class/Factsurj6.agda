
open import Oscar.Prelude
open import Oscar.Class.Surjectextensivity
import Oscar.Class.Surjection.⋆

module Oscar.Class.Factsurj6 where

module _
  {𝔬} {𝔒 : Ø 𝔬}
  {𝔭} (𝔓 : 𝔒 → Ø 𝔭)
  {𝔯} (_∼_ : 𝔒 → 𝔒 → Ø 𝔯)
  {ℓ∼} (_≈̈_ : ∀ {x y} → x ∼ y → x ∼ y → Ø ℓ∼) (let _≈̈_ = _≈̈_ ; infix 4 _≈̈_)
  {ℓ𝔭} (_≈̇_ : ∀ {x} → 𝔓 x → 𝔓 x → Ø ℓ𝔭) (let _≈̇_ = _≈̇_ ; infix 4 _≈̇_)
  where
  module _
    ⦃ _ : 𝓢urjectextensivity _∼_ 𝔓 ⦄
    where
    record 𝓕actsurj6 : Ø 𝔬 ∙̂ 𝔭 ∙̂ 𝔯 ∙̂ ℓ∼ ∙̂ ℓ𝔭 where
      field factsurj6 : ∀ {m n} {f g : m ∼ n} (P : 𝔓 m) → f ≈̈ g → f ◃ P ≈̇ g ◃ P

open 𝓕actsurj6 ⦃ … ⦄ public
