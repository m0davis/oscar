
module Oscar.Property.Symmetry where

open import Oscar.Level

record Symmetry {𝔬} {⋆ : Set 𝔬} {𝔮} (_≒_ : ⋆ → ⋆ → Set 𝔮) : Set (𝔬 ⊔ 𝔮) where
  field
    symmetry : ∀ {x y} → x ≒ y → y ≒ x

open Symmetry ⦃ … ⦄ public
