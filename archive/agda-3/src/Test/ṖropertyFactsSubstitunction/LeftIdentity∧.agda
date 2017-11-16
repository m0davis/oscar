
open import Test.ṖropertyFactsSubstitunction.imports

module Test.ṖropertyFactsSubstitunction.LeftIdentity∧ {𝔭} (𝔓 : Ø 𝔭) (ℓ : Ł) where

  open Data 𝔓 ℓ

  left-identity-∧ : ∀ {𝓃} (𝒫 : 𝑷⁰ 𝓃) → ➊ ∧ 𝒫 ≈ 𝒫
  left-identity-∧ 𝒫 = ∧-leftIdentity 𝒫

  left-identity-∧-ext : ∀ {𝓃} (𝒫 : 𝑷¹ 𝓃) → ➊ ∧ 𝒫 ≈ 𝒫
  left-identity-∧-ext 𝒫 = ∧-leftIdentity 𝒫
