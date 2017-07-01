
module Oscar.Property.Transitivity where

open import Oscar.Level

record Transitivity {𝔬} {⋆ : Set 𝔬} {𝔮} (_↦_ : ⋆ → ⋆ → Set 𝔮) : Set (𝔬 ⊔ 𝔮) where
  field
    transitivity : ∀ {x y} → x ↦ y → ∀ {z} → y ↦ z → x ↦ z

open Transitivity ⦃ … ⦄ public
