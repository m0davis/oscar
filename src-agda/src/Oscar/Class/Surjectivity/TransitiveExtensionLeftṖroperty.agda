
open import Oscar.Prelude
open import Oscar.Class
open import Oscar.Class.Surjectivity
open import Oscar.Class.Transitivity
import Oscar.Class.Surjection.⋆

module Oscar.Class.Surjectivity.TransitiveExtensionLeftṖroperty where

instance

  ṖropertySurjectivity : ∀
    {𝔵} {𝔛 : Ø 𝔵}
    {𝔯} {_↦_ : 𝔛 → 𝔛 → Ø 𝔯}
    {ℓ : Ł}
    ⦃ _ : 𝓣ransitivity _↦_ ⦄
    -- ⦃ _ : [𝓢urjectivity] _↦_ (Extension $ LeftṖroperty ℓ _↦_) ⦄
    -- FIXME, the above line is commented-out b/c Agda gets confused by the other [𝓢urjectivity] instance in Oscar.Class
    → Surjectivity!.class _↦_ (Extension $ LeftṖroperty ℓ _↦_)
  ṖropertySurjectivity .⋆ _ _ f (∁ P) .π₀ g = P (g ∙ f)
