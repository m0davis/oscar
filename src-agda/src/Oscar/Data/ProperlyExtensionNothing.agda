
open import Oscar.Prelude
open import Oscar.Data.𝟘

module Oscar.Data.ProperlyExtensionNothing where

module _
  {𝔵} {𝔛 : Ø 𝔵}
  {𝔬} {𝔒 : 𝔛 → Ø 𝔬}
  {ℓ}
  {ℓ̇} {_↦_ : ∀ {x} → 𝔒 x → 𝔒 x → Ø ℓ̇}
  where

  record ProperlyExtensionNothing (P : ExtensionṖroperty ℓ 𝔒 _↦_) : Ø 𝔵 ∙̂ 𝔬 ∙̂ ℓ where
    constructor ∁
    field
      π₀ : ∀ {n} {f : 𝔒 n} → π₀ (π₀ P) f → 𝟘

open ProperlyExtensionNothing public
