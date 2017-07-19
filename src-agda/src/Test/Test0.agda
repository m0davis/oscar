
open import Oscar.Class

module Test.Test0 where

  test-functor-surjidentity : ∀
    {𝔬₁ 𝔯₁ ℓ₁ 𝔬₂ 𝔯₂ ℓ₂}
    ⦃ functor : Functor 𝔬₁ 𝔯₁ ℓ₁ 𝔬₂ 𝔯₂ ℓ₂ ⦄
    (open Functor functor)
    → 𝓼urjidentity _∼₁_ _∼₂_ _∼̇₂_
  test-functor-surjidentity = surjidentity

  -- test-functor-transextensionality ⦃ functor ⦄ = let open Functor ⦃ … ⦄ in transextensionality1
