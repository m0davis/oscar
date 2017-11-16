
open import Oscar.Prelude

module Oscar.Class.Apply where

module _
  (𝔉 : ∀ {𝔣} → Ø 𝔣 → Ø 𝔣)
  𝔬₁ 𝔬₂
  where
  𝓪pply = ∀ {𝔒₁ : Ø 𝔬₁} {𝔒₂ : Ø 𝔬₂} → 𝔉 (𝔒₁ → 𝔒₂) → 𝔉 𝔒₁ → 𝔉 𝔒₂
  record 𝓐pply : Ø ↑̂ (𝔬₁ ∙̂ 𝔬₂) where
    infixl 4 apply
    field apply : 𝓪pply
    syntax apply f x = f <*> x
open 𝓐pply ⦃ … ⦄ public

_<*>_ = apply
