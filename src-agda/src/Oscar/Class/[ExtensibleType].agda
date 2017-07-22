
open import Oscar.Prelude

module Oscar.Class.[ExtensibleType] where

record [ExtensibleType]
    {𝔵} {𝔛 : Ø 𝔵}
    {𝔟} {𝔒₂ : 𝔛 → Ø 𝔟}
    {ℓ̇} (_↦_ : ∀ {x} → 𝔒₂ x → 𝔒₂ x → Ø ℓ̇)
    : Ø₀ where
  constructor ∁
  no-eta-equality
