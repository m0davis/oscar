
open import Oscar.Prelude
open import Oscar.Class
open import Oscar.Property
import Oscar.Class.Symmetrical.Symmetry

module Test.Symmetrical where

  test-𝓢ymmetrical𝓢ymmetry : ∀
    {𝔬} {𝔒 : Ø 𝔬}
    {ℓ} {_∼_ : 𝔒 → 𝔒 → Ø ℓ}
    ⦃ _ : 𝓢ymmetry _∼_ ⦄
    → 𝓼ymmetry _∼_
  test-𝓢ymmetrical𝓢ymmetry = symmetrical _ _
