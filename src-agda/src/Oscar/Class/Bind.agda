
open import Oscar.Prelude

module Oscar.Class.Bind where

module _
  (𝔉 : ∀ {𝔣} → Ø 𝔣 → Ø 𝔣)
  𝔬₁ 𝔬₂
  where
  𝓫ind = ∀ {𝔒₁ : Ø 𝔬₁} {𝔒₂ : Ø 𝔬₂} → 𝔉 𝔒₁ → (𝔒₁ → 𝔉 𝔒₂) → 𝔉 𝔒₂
  record 𝓑ind : Ø ↑̂ (𝔬₁ ∙̂ 𝔬₂) where
    infixl 6 bind
    field bind : 𝓫ind
    syntax bind m f = f =<< m
  open 𝓑ind ⦃ … ⦄ public
