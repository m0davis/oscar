
open import Oscar.Prelude
open import Oscar.Class.IsPrecategory
open import Oscar.Class.Transitivity

module Oscar.Class.Precategory where

record Precategory 𝔬 𝔯 ℓ : Ø ↑̂ (𝔬 ∙̂ 𝔯 ∙̂ ℓ) where
  constructor ∁
  infix 4 _∼̇_
  field
    {𝔒} : Ø 𝔬
    _∼_ : 𝔒 → 𝔒 → Ø 𝔯
    _∼̇_ : ∀ {x y} → x ∼ y → x ∼ y → Ø ℓ
    _↦_ : Transitivity.type _∼_
    ⦃ `IsPrecategory ⦄ : IsPrecategory _∼_ _∼̇_ _↦_
