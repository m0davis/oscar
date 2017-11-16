
module Oscar.Category.Setoid where

open import Oscar.Builtin.Objectevel
open import Oscar.Property

record IsSetoid {𝔬} {𝔒 : Ø 𝔬} {𝔮} (_≋_ : 𝑴 1 𝔒 𝔮) : Ø 𝔬 ∙̂ 𝔮 where
  field
    reflexivity : ∀ x → x ≋ x
    symmetry : ∀ {x y} → x ≋ y → y ≋ x
    transitivity : ∀ {x y} → x ≋ y → ∀ {z} → y ≋ z → x ≋ z

open IsSetoid ⦃ … ⦄ public

record Setoid 𝔬 𝔮 : Ø ↑̂ (𝔬 ∙̂ 𝔮) where
  constructor ↑_
  infix 4 _≋_
  field
    {⋆} : Set 𝔬
    _≋_ : ⋆ → ⋆ → Set 𝔮
    ⦃ isSetoid ⦄ : IsSetoid _≋_
  open IsSetoid isSetoid public
