
open import Test.ṖropertyFactsSubstitunction.imports

module Test.ṖropertyFactsSubstitunction.PropId {𝔭} (𝔓 : Ø 𝔭) (ℓ : Ł) where

  open Data 𝔓 ℓ

  prop-id-extension-property : ∀ {𝓂 𝓃} {f : 𝑪 𝓂 𝓃} (P : LeftExtensionṖroperty ℓ 𝑪 _≈_ 𝓂) → P .π₀ .π₀ f → P .π₀ .π₀ (ε ∙ f)
  prop-id-extension-property = hmap _
