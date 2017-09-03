
open import Test.ṖropertyFactsSubstitunction.imports

module Test.ṖropertyFactsSubstitunction.Fact6 {𝔭} (𝔓 : Ø 𝔭) (ℓ : Ł) where

  open Data 𝔓 ℓ

  fact6 : ∀ {𝓂 𝓃} {𝒻 ℊ : 𝑪 𝓂 𝓃} (𝒫 : 𝑷¹ 𝓂) → 𝒻 ≈ ℊ → 𝒻 ◃ 𝒫 ≈ ℊ ◃ 𝒫
  fact6 𝒫 𝒻≈ℊ = similarity 𝒫 𝒻≈ℊ

  fact6' : ∀ {𝓂 𝓃} {𝒻 ℊ : 𝑪 𝓂 𝓃} (𝒫 : 𝑷¹ 𝓂) → 𝒻 ≈ ℊ → 𝒻 ◃ 𝒫 ≈ ℊ ◃ 𝒫
  fact6' 𝒫 𝒻≈ℊ = similarityM 𝒫 𝒻≈ℊ

  -- fact6'' : ∀ {𝓂 𝓃} {𝒻 ℊ : 𝑪 𝓂 𝓃} (𝒫 : 𝑷¹ 𝓂) → 𝒻 ≈ ℊ → 𝒻 ◃ 𝒫 ≈ ℊ ◃ 𝒫
  -- fact6'' 𝒫 𝒻≈ℊ = similaritySingleton $ 𝒻≈ℊ -- FIXME internal error at src/full/Agda/TypeChecking/Substitute.hs:98
