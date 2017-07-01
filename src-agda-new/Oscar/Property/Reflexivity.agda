
module Oscar.Property.Reflexivity where

open import Oscar.Level

record Reflexivity {𝔬} {⋆ : Set 𝔬} {ℓ} (_≣_ : ⋆ → ⋆ → Set ℓ) : Set (𝔬 ⊔ ℓ) where
  field
    reflexivity : ∀ x → x ≣ x

open Reflexivity ⦃ … ⦄ public
