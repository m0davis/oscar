
open import Oscar.Prelude
open import Oscar.Class.Reflexivity
open import Oscar.Class.Symmetry
open import Oscar.Class.Transitivity

module Oscar.Class.IsEquivalence where

record IsEquivalence
  {𝔬} {𝔒 : Ø 𝔬}
  {ℓ} (_≈_ : 𝔒 → 𝔒 → Ø ℓ)
  : Ø 𝔬 ∙̂ ℓ where
  constructor ∁
  field
    ⦃ `𝓡eflexivity ⦄ : 𝓡eflexivity _≈_
    ⦃ `𝓢ymmetry ⦄ : 𝓢ymmetry _≈_
    ⦃ `𝓣ransitivity ⦄ : 𝓣ransitivity _≈_
