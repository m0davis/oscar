
open import Test.ṖropertyFactsSubstitunction.imports

module Test.ṖropertyFactsSubstitunction.Fact3 {𝔭} (𝔓 : Ø 𝔭) (ℓ : Ł) where

  open Data 𝔓 ℓ

  fact3⋆ : ∀ {𝓃} {𝒫 : 𝑷⁰ 𝓃} → 𝒫 ≈ 𝒖 ◃ 𝒫
  fact3⋆ = ‼ -- 𝓕actsurj3.method 𝑷⁰ 𝑪 -- $MethodUnit.method -- leftunit.method

  fact3⋆''' : ∀ {𝓃} {𝒫 : 𝑷⁰ 𝓃} → 𝒫 ≈ 𝒖 ◃ 𝒫
  fact3⋆''' = leftunit

  fact3 : ∀ {𝓃} {𝒫 : 𝑷¹ 𝓃} → 𝒫 ≈ 𝒖 ◃ 𝒫
  fact3 = ‼ -- 𝓕actsurj3.method 𝑷¹ 𝑪 -- $MethodUnit.method -- factsurj3.method -- leftunit.method
