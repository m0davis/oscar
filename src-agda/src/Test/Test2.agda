
open import Oscar.Prelude
open import Oscar.Class.IsFunctor
open import Oscar.Class.Transextensionality

module Test.Test2 where

  test-functor-transextensionality : ∀
    {𝔬₁} {𝔒₁ : Ø 𝔬₁}
    {𝔯₁} {_∼₁_ : 𝔒₁ → 𝔒₁ → Ø 𝔯₁}
    {ℓ₁} {_∼̇₁_ : ∀ {x y} → x ∼₁ y → x ∼₁ y → Ø ℓ₁}
    {𝔬₂} {𝔒₂ : Ø 𝔬₂}
    {𝔯₂} {_∼₂_ : 𝔒₂ → 𝔒₂ → Ø 𝔯₂}
    {ℓ₂} {_∼̇₂_ : ∀ {x y} → x ∼₂ y → x ∼₂ y → Ø ℓ₂}
    ⦃ _ : IsFunctor _∼₁_ _∼̇₁_ _∼₂_ _∼̇₂_ ⦄
    ⦃ _ : IsFunctor _∼₁_ _∼̇₁_ _∼₂_ _∼̇₂_ ⦄
    → Transextensionality!.type _∼₁_ _∼̇₁_
  test-functor-transextensionality = transextensionality
