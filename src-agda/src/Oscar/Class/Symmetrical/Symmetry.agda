
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

    [𝓢ymmetrical]𝓢ymmetry : [𝓢ymmetrical] _∼_ (λ x∼y y∼x → x∼y → y∼x)
    [𝓢ymmetrical]𝓢ymmetry = ∁ _∼_ (λ x∼y y∼x → x∼y → y∼x)

    𝓢ymmetrical𝓢ymmetry : 𝓢ymmetrical _∼_ (λ x∼y y∼x → x∼y → y∼x)
    𝓢ymmetrical𝓢ymmetry .𝒮ymmetrical.symmetrical _ _ = symmetry
