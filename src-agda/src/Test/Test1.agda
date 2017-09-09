{-# OPTIONS --allow-unsolved-metas #-} -- FIXME

open import Oscar.Class.Functor
open import Oscar.Class.Transextensionality

module Test.Test1 where

  test-functor-transextensionality : ∀
    {𝔬₁ 𝔯₁ ℓ₁ 𝔬₂ 𝔯₂ ℓ₂}
    ⦃ functor : Functor 𝔬₁ 𝔯₁ ℓ₁ 𝔬₂ 𝔯₂ ℓ₂ ⦄
    (open Functor functor)
    → {!Transextensionality!.type _∼₁_ _∼̇₁_!}
  test-functor-transextensionality = transextensionality
  -- test-functor-transextensionality ⦃ functor ⦄ = let open Functor ⦃ … ⦄ in transextensionality1
