
module Oscar.Category.Setoid where

open import Oscar.Level

record IsEquivalence {𝔬} {⋆ : Set 𝔬} {𝔮} (_≋_ : ⋆ → ⋆ → Set 𝔮) : Set (𝔬 ⊔ 𝔮) where
  field
    reflexivity : ∀ x → x ≋ x
    symmetry : ∀ {x y} → x ≋ y → y ≋ x
    transitivity : ∀ {x y} → x ≋ y → ∀ {z} → y ≋ z → x ≋ z

open IsEquivalence ⦃ … ⦄ public

record IsSetoid {𝔬} (⋆ : Set 𝔬) 𝔮 : Set (𝔬 ⊔ lsuc 𝔮) where
  infix 4 _≋_
  field
    _≋_ : ⋆ → ⋆ → Set 𝔮
    ⦃ isEquivalence ⦄ : IsEquivalence _≋_

open IsSetoid ⦃ … ⦄ public
--{-# DISPLAY IsSetoid._≋_ _ = _≋_ #-}

record Setoid 𝔬 𝔮 : Set (lsuc (𝔬 ⊔ 𝔮)) where
  field
    ⋆ : Set 𝔬
    ⦃ isSetoid ⦄ : IsSetoid ⋆ 𝔮
  open IsSetoid isSetoid public
