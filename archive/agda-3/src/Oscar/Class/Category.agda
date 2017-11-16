
open import Oscar.Prelude
open import Oscar.Class.IsCategory
open import Oscar.Class.Reflexivity
open import Oscar.Class.Transitivity

module Oscar.Class.Category where

record Category 𝔬 𝔯 ℓ : Ø ↑̂ (𝔬 ∙̂ 𝔯 ∙̂ ℓ) where
  constructor ∁
  infix 4 _∼̇_
  field
    {𝔒} : Ø 𝔬
    _∼_ : 𝔒 → 𝔒 → Ø 𝔯
    _∼̇_ : ∀ {x y} → x ∼ y → x ∼ y → Ø ℓ
    category-ε : Reflexivity.type _∼_
    _↦_ : Transitivity.type _∼_
    ⦃ `IsCategory ⦄ : IsCategory _∼_ _∼̇_ category-ε _↦_
