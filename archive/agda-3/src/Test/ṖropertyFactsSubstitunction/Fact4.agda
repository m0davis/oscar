
open import Test.ṖropertyFactsSubstitunction.imports

module Test.ṖropertyFactsSubstitunction.Fact4 {𝔭} (𝔓 : Ø 𝔭) (ℓ : Ł) where

  open Data 𝔓 ℓ

  fact4⋆ : ∀ {𝓂 𝓃} {𝒫 : 𝑷⁰ 𝓂} (𝒻 : 𝑪 _ 𝓃) → Nothing 𝒫 → Nothing (𝒻 ◃ 𝒫)
  fact4⋆ 𝒻 N𝒫 = leftstar 𝒻 N𝒫

  fact4 : ∀ {𝓂 𝓃} {𝒫 : 𝑷¹ 𝓂} (𝒻 : 𝑪 _ 𝓃) → Nothing 𝒫 → Nothing (𝒻 ◃ 𝒫)
  fact4 𝒻 N𝒫 = leftstar 𝒻 N𝒫
