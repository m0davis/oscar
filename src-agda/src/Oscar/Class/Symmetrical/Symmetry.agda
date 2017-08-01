
open import Oscar.Prelude
open import Oscar.Class.Symmetry
open import Oscar.Class.Symmetrical
import Oscar.Data.Proposequality

module Oscar.Class.Symmetrical.Symmetry where

module _
    {𝔬} {𝔒 : Ø 𝔬}
    {ℓ} {_∼_ : 𝔒 → 𝔒 → Ø ℓ}
    ⦃ _ : 𝓢ymmetry _∼_ ⦄
  where

  instance

    Symmetrical𝓢ymmetry : Symmetrical _∼_ (λ x∼y y∼x → x∼y → y∼x)
    Symmetrical𝓢ymmetry .𝓢ymmetrical.symmetrical _ _ = symmetry
