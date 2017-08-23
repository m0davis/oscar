
open import Oscar.Prelude
open import Oscar.Class
open import Oscar.Class.[ExtensibleType]
open import Oscar.Class.Surjectivity
open import Oscar.Class.Surjextensionality
import Oscar.Class.Surjection.⋆

module Oscar.Class.Surjectivity.ExtensionṖroperty where

instance

  ExtensionṖropertySurjectivity : ∀
    {𝔵} {𝔛 : Ø 𝔵}
    {𝔞} {𝔒₁ : 𝔛 → Ø 𝔞}
    {𝔟} {𝔒₂ : 𝔛 → Ø 𝔟}
    (let _∼_ = Arrow 𝔒₁ 𝔒₂)
    {ℓ}
    {ℓ̇} {_↦_ : ∀̇ π̂² ℓ̇ 𝔒₂}
    ⦃ _ : [ExtensibleType] (λ {x} → _↦_ {x}) ⦄
    ⦃ _ : Surjectivity!.class _∼_ (Extension 𝔒₂) ⦄
    ⦃ _ : Surjextensionality!.class _∼_ (Pointwise _↦_) (Extension 𝔒₂) (Pointwise _↦_) ⦄
    → Surjectivity!.class _∼_ (Extension $ LeftExtensionṖroperty ℓ _∼_ (Pointwise _↦_))
  ExtensionṖropertySurjectivity .⋆ _ _ f P = ∁ (λ g → π₀ (π₀ P) (surjectivity g ∘ f)) , (λ f≐g Pf'◇f → π₁ P (surjextensionality f≐g ∘ f) Pf'◇f)
