
open import Test.ṖropertyFactsSubstitunction.imports

module Test.ṖropertyFactsSubstitunction.Epfs {𝔭} (𝔓 : Ø 𝔭) (ℓ : Ł) where

  open Data 𝔓 ℓ

  test-epfs⋆ : ∀ {𝓂 𝓃} → 𝑪 𝓂 𝓃 → 𝑷⁰ 𝓂 → 𝑷⁰ 𝓃
  test-epfs⋆ c p = smaparrow c p

  test-epfs : ∀ {𝓂 𝓃} → 𝑪 𝓂 𝓃 → 𝑷¹ 𝓂 → 𝑷¹ 𝓃
  test-epfs c p = smaparrow c p
