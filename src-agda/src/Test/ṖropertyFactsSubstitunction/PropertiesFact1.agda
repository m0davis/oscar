
open import Test.ṖropertyFactsSubstitunction.imports

module Test.ṖropertyFactsSubstitunction.PropertiesFact1 {𝔭} (𝔓 : Ø 𝔭) (ℓ : Ł) where

  open Data 𝔓 ℓ

  Properties-fact1'⋆ : ∀ {𝓃} (𝓈₁ 𝓈₂ 𝓉₁ 𝓉₂ : 𝑩 𝓃) → 𝓈₁ ⊛ 𝓈₂ ∼⁰ 𝓉₁ ⊛ 𝓉₂ ≈ 𝓈₁ ∼⁰ 𝓉₁ ∧ 𝓈₂ ∼⁰ 𝓉₂
  Properties-fact1'⋆ 𝓈₁ 𝓈₂ 𝓉₁ 𝓉₂ = quadricity 𝓈₁ 𝓈₂ 𝓉₁ 𝓉₂

  Properties-fact1' : ∀ {𝓃} (𝓈₁ 𝓈₂ 𝓉₁ 𝓉₂ : 𝑩 𝓃) → 𝓈₁ ⊛ 𝓈₂ ∼¹ 𝓉₁ ⊛ 𝓉₂ ≈ 𝓈₁ ∼¹ 𝓉₁ ∧ 𝓈₂ ∼¹ 𝓉₂
  Properties-fact1' 𝓈₁ 𝓈₂ 𝓉₁ 𝓉₂ = quadricity 𝓈₁ 𝓈₂ 𝓉₁ 𝓉₂
