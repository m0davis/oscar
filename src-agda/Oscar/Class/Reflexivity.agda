
module Oscar.Class.Reflexivity where

open import Oscar.Level

record Reflexivity {a} {A : Set a} {ℓ} (_≋_ : A → A → Set ℓ) : Set (a ⊔ ℓ) where
  field
    reflexivity : ∀ {x} → x ≋ x

open Reflexivity ⦃ … ⦄ public
