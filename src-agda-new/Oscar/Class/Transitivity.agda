
module Oscar.Class.Transitivity where

open import Oscar.Level
open import Oscar.Relation

record Transitivity {a} {A : Set a} {ℓ} (_≤_ : A → A → Set ℓ) : Set (a ⊔ ℓ) where
  field
    transitivity : ∀ {x y} → x ≤ y → ∀ {z} → y ⟨ _≤ z ⟩→ x

open Transitivity ⦃ … ⦄ public
