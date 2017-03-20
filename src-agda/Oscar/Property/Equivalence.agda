
module Oscar.Property.Equivalence where

open import Oscar.Function
open import Oscar.Level
open import Oscar.Property.Reflexivity
open import Oscar.Property.Symmetry
open import Oscar.Property.Transitivity

record Equivalence {𝔬} {⋆ : Set 𝔬} {𝔮} (_≋_ : ⋆ → ⋆ → Set 𝔮) : Set (𝔬 ⊔ 𝔮) where
  field
    ⦃ ′reflexivity ⦄ : Reflexivity _≋_
    ⦃ ′symmetry ⦄ : Symmetry _≋_
    ⦃ ′transitivity ⦄ : Transitivity _≋_

open Equivalence ⦃ … ⦄ public

instance
  Equivalence⋆ : ∀
    {𝔬} {⋆ : Set 𝔬} {𝔮} {_≋_ : ⋆ → ⋆ → Set 𝔮}
    ⦃ _ : Reflexivity _≋_ ⦄
    ⦃ _ : Symmetry _≋_ ⦄
    ⦃ _ : Transitivity _≋_ ⦄
    → Equivalence _≋_
  Equivalence.′reflexivity Equivalence⋆ = it
  Equivalence.′symmetry Equivalence⋆ = it
  Equivalence.′transitivity Equivalence⋆ = it
