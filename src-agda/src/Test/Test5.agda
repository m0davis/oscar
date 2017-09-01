
open import Oscar.Prelude
open import Oscar.Class.[ExtensibleType]
open import Oscar.Class.Smap
open import Oscar.Class.Surjextensionality
open import Oscar.Class.Surjectextensivity
import Oscar.Class.Surjection.⋆
import Oscar.Class.Smap.ExtensionṖroperty

module Test.Test5
  {𝔵} {𝔛 : Ø 𝔵}
  {𝔞} {𝔒₁ : 𝔛 → Ø 𝔞}
  {𝔟} {𝔒₂ : 𝔛 → Ø 𝔟}
  {ℓ}
  {ℓ̇} (_↦_ : ∀ {x} → 𝔒₂ x → 𝔒₂ x → Ø ℓ̇)
  ⦃ _ : [ExtensibleType] _↦_ ⦄
  ⦃ _ : Smap!.class (Arrow 𝔒₁ 𝔒₂) (Extension 𝔒₂) ⦄
  ⦃ _ : Surjextensionality!.class (Arrow 𝔒₁ 𝔒₂) (Pointwise _↦_) (Extension 𝔒₂) (Pointwise _↦_) ⦄
  -- ⦃ _ : [𝓢urjectivity] (Arrow 𝔒₁ 𝔒₂) (Extension $ ArrowExtensionṖroperty ℓ 𝔒₁ 𝔒₂ _↦_) ⦄
  where
  test[∙] : ∀ {x y} → ArrowExtensionṖroperty ℓ 𝔒₁ 𝔒₂ _↦_ x → Arrow 𝔒₁ 𝔒₂ x y → ArrowExtensionṖroperty ℓ 𝔒₁ 𝔒₂ _↦_ y
  test[∙] P f = f ◃ P
