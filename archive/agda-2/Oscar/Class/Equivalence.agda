
module Oscar.Class.Equivalence where

open import Oscar.Class.Reflexivity
open import Oscar.Class.Symmetry
open import Oscar.Class.Transitivity
open import Oscar.Function
open import Oscar.Level

record Equivalence {a} {A : Set a} {ℓ} (_≋_ : A → A → Set ℓ) : Set (a ⊔ ℓ) where
  field
    ⦃ ′reflexivity ⦄ : Reflexivity _≋_
    ⦃ ′symmetry ⦄ : Symmetry _≋_
    ⦃ ′transitivity ⦄ : Transitivity _≋_

open Equivalence ⦃ … ⦄ public hiding (′reflexivity; ′symmetry; ′transitivity)

instance

  Equivalence⋆ : ∀
    {a} {A : Set a} {ℓ} {_≋_ : A → A → Set ℓ}
    ⦃ _ : Reflexivity _≋_ ⦄
    ⦃ _ : Symmetry _≋_ ⦄
    ⦃ _ : Transitivity _≋_ ⦄
    → Equivalence _≋_
  Equivalence.′reflexivity Equivalence⋆ = it
  Equivalence.′symmetry Equivalence⋆ = it
  Equivalence.′transitivity Equivalence⋆ = it
