
module Oscar.Category.Morphism where

open import Oscar.Category.Setoid
open import Oscar.Level

record Morphism
  {𝔬} (⋆ : Set 𝔬) 𝔪 𝔮
  : Set (𝔬 ⊔ lsuc (𝔪 ⊔ 𝔮))
  where

  field
    _⇒_ : ⋆ → ⋆ → Setoid 𝔪 𝔮

  _↦_ : ⋆ → ⋆ → Set 𝔪
  _↦_ x y = Setoid.⋆ (x ⇒ y)

  field
    ⦃ isSetoid ⦄ : ∀ {x y} → IsSetoid (Setoid.⋆ (x ⇒ y)) 𝔮
