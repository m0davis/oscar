
module Oscar.Property.IsReflexive where

open import Oscar.Level

record IsReflexive {𝔬} (⋆ : Set 𝔬) {ℓ} (_≣_ : ⋆ → ⋆ → Set ℓ) : Set (𝔬 ⊔ ℓ) where
  field
    reflexivity : ∀ x → x ≣ x
