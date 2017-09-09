
open import Oscar.Prelude
open import Oscar.Class.Functor
open import Oscar.Class.Transextensionality

module Test.Test3 where

  module _
    {𝔬₁ 𝔯₁ ℓ₁ 𝔬₂ 𝔯₂ ℓ₂}
    where
    postulate instance functor : Functor 𝔬₁ 𝔯₁ ℓ₁ 𝔬₂ 𝔯₂ ℓ₂
    open Functor ⦃ … ⦄
    test : asInstance `IsFunctor $ Transextensionality!.type _∼₁_ _∼̇₁_
    test = asInstance `IsFunctor transextensionality
    -- -- Test1.test-functor-transextensionality
