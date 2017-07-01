
module Oscar.Class.Reflexive where

open import Oscar.Level
open import Oscar.Property.IsReflexive

record Reflexive {𝔬} (⋆ : Set 𝔬) ℓ : Set (𝔬 ⊔ lsuc ℓ) where
  field
    _≣_ : ⋆ → ⋆ → Set ℓ
    isReflexive : IsReflexive ⋆ _≣_

  open IsReflexive isReflexive public
