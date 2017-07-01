
module Oscar.Class.Injectivity where

open import Oscar.Level

record Injectivity {a} {A : Set a} {b} {B : Set b} {ℓ₁} (_≋₁_ : A → B → Set ℓ₁)
                   {i} {I : Set i} {ℓ₂} (_≋₂_ : I → I → Set ℓ₂)
                   (f : I → A)
                   (g : I → B)
       : Set (a ⊔ b ⊔ ℓ₁ ⊔ i ⊔ ℓ₂) where
  field
    injectivity : ∀ {x y} → f x ≋₁ g y → x ≋₂ y

open Injectivity ⦃ … ⦄ public

record Injectivityoid a b ℓ₁ i ℓ₂ : Set (lsuc (a ⊔ b ⊔ ℓ₁ ⊔ i ⊔ ℓ₂)) where
  field
    {A} : Set a
    {B} : Set b
    _≋₁_ : A → B → Set ℓ₁
    I : Set i
    _≋₂_ : I → I → Set ℓ₂
    μₗ : I → A
    μᵣ : I → B
    `injectivity : ∀ {x y} → μₗ x ≋₁ μᵣ y → x ≋₂ y
