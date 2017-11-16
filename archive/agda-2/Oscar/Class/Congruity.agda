
module Oscar.Class.Congruity where

open import Oscar.Class.Extensionality
open import Oscar.Level

record Congruity {a} {A : Set a} {ℓ₁} (_≋₁_ : A → A → Set ℓ₁)
                 {b} {B : Set b} {ℓ₂} (_≋₂_ : B → B → Set ℓ₂)
       : Set (a ⊔ ℓ₁ ⊔ b ⊔ ℓ₂) where
  field
    congruity : ∀ (μ : A → B) {x y} → x ≋₁ y → μ x ≋₂ μ y

  instance ′extensionality : ∀ (μ : A → B) → Extensionality _≋₁_ (λ ⋆ → _≋₂_ ⋆) μ μ
  Extensionality.extensionality (′extensionality μ) = congruity μ

open Congruity ⦃ … ⦄ public -- hiding (′extensionality)
