
open import Oscar.Prelude
open import Oscar.Class.Symmetry
open import Oscar.Class.Symmetrical

module Oscar.Class.Symmetrical.Symmetry where

module _
    {𝔬} {𝔒 : Ø 𝔬}
    {ℓ} {_∼_ : 𝔒 → 𝔒 → Ø ℓ}
    ⦃ _ : 𝓢ymmetry _∼_ ⦄
  where

  instance

    SymmetricalContainer𝓢ymmetry : SymmetricalContainer 𝔒 (Ø ℓ) (λ x∼y y∼x → x∼y → y∼x)
    SymmetricalContainer𝓢ymmetry .SymmetricalContainer._∼_ = _∼_
    SymmetricalContainer𝓢ymmetry .SymmetricalContainer.symmetrical′ _ _ = symmetry

    [𝓢ymmetrical]𝓢ymmetry : [𝓢ymmetrical] 𝔒 (Ø ℓ) (λ x∼y y∼x → x∼y → y∼x)
    [𝓢ymmetrical]𝓢ymmetry .[𝓢ymmetrical]._∼_ = _∼_

    𝓢ymmetrical𝓢ymmetry : 𝓢ymmetrical 𝔒 (Ø ℓ) (λ x∼y y∼x → x∼y → y∼x)
    𝓢ymmetrical𝓢ymmetry .𝓢ymmetrical.symmetrical _ _ = symmetry
