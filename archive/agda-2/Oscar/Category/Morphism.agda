
module Oscar.Category.Morphism where

open import Oscar.Category.Setoid
open import Oscar.Level
open import Oscar.Property
open import Oscar.Data.Nat

record Morphism
  {𝔬} (⋆ : Set 𝔬) 𝔪 𝔮
  : Set (𝔬 ⊔ lsuc (𝔪 ⊔ 𝔮))
  where
  constructor #_

  field
    _⇒_ : ⋆ → ⋆ → Setoid 𝔪 𝔮

  _↦_ : ⋆ → ⋆ → Set 𝔪
  _↦_ x y = Setoid.⋆ (x ⇒ y)

  infix 4 _≞_
  _≞_ : ∀ {x y} → x ↦ y → x ↦ y → Set 𝔮
  _≞_ {x} {y} = Setoid._≋_ (x ⇒ y)

  instance IsSetoid↦ : ∀ {x y} → IsSetoid (_≞_ {x} {y})
  IsSetoid↦ {x} {y} = Setoid.isSetoid (x ⇒ y)

  -- IsSetoid↦ : ∀ {x y} → IsSetoid (x ↦ y) 𝔮
  -- IsSetoid↦ {x} {y} = Setoid.isSetoid (x ⇒ y)

  --   ⦃ isMorphism ⦄ : IsMorphism (λ {x} {y} → _≞_ {x} {y})

-- record Morphism 𝔬 𝔪 𝔮 : Set (lsuc (𝔬 ⊔ 𝔪 ⊔ 𝔮)) where
--   constructor ↑_
--   infix 4 _≞_
--   field
--     {⋆} : Set 𝔬
--     {_↦_} : ⋆ → ⋆ → Set 𝔪
--     _≞_ : ∀ {x y} → x ↦ y → x ↦ y → Set 𝔮
--     ⦃ isSetoid ⦄ : ∀ {x} {y} → IsSetoid (_≞_ {x} {y})

--   instance IsSetoid↦ : ∀ {x y} → IsSetoid (_≞_ {x} {y})
--   IsSetoid↦ {x} {y} = Setoid.isSetoid (x ⇒ y)

--   setoid : ∀ {x y} → Setoid 𝔪 𝔮
--   setoid {x} {y} = ↑ _≞_ {x} {y}
