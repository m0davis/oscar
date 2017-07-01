
module Oscar.Class.Symmetry where

open import Oscar.Class.Extensionality
open import Oscar.Function
open import Oscar.Level

record Symmetry {a} {A : Set a} {ℓ} (_≤_ : A → A → Set ℓ) : Set (a ⊔ ℓ) where
  field
    ⦃ ′extensionality ⦄ : Extensionality _≤_ (λ ⋆ → flip _≤_ ⋆) id id

  symmetry : ∀ {x y} → x ≤ y → y ≤ x
  symmetry = extension (λ ⋆ → flip _≤_ ⋆)

open Symmetry ⦃ … ⦄ public hiding (′extensionality)

instance

  Symmetry⋆ : ∀
    {a} {A : Set a} {ℓ} {_≤_ : A → A → Set ℓ}
    ⦃ _ : Extensionality _≤_ (λ ⋆ → flip _≤_ ⋆) id id ⦄
    → Symmetry _≤_
  Symmetry.′extensionality Symmetry⋆ = it
