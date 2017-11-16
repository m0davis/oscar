
open import Oscar.Prelude
open import Oscar.Class.IsEquivalence

module Oscar.Class.Setoid where

record Setoid 𝔬 ℓ : Ø ↑̂ (𝔬 ∙̂ ℓ) where
  constructor ∁
  field
    {Object} : Ø 𝔬
    ObjectEquivalence : Object → Object → Ø ℓ
    ⦃ `IsEquivalence ⦄ : IsEquivalence ObjectEquivalence
