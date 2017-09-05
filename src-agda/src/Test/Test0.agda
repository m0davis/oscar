
open import Oscar.Class.Functor
open import Oscar.Class.Surjidentity

module Test.Test0 where

  test-functor-surjidentity : ∀
    {𝔬₁ 𝔯₁ ℓ₁ 𝔬₂ 𝔯₂ ℓ₂}
    ⦃ functor : Functor 𝔬₁ 𝔯₁ ℓ₁ 𝔬₂ 𝔯₂ ℓ₂ ⦄
    (open Functor functor)
    → Surjidentity!.type _∼₁_ _∼₂_ _∼̇₂_
  test-functor-surjidentity = surjidentity

  -- test-functor-transextensionality ⦃ functor ⦄ = let open Functor ⦃ … ⦄ in transextensionality1
