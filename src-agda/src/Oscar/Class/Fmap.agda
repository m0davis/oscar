
open import Oscar.Prelude

module Oscar.Class.Fmap where

module _
  (𝔉 : ∀ {𝔣} → Ø 𝔣 → Ø 𝔣)
  𝔬₁ 𝔬₂
  where
  𝓯map = ∀ {𝔒₁ : Ø 𝔬₁} {𝔒₂ : Ø 𝔬₂} (f : 𝔒₁ → 𝔒₂) → 𝔉 𝔒₁ → 𝔉 𝔒₂
  record 𝓕map : Ø ↑̂ (𝔬₁ ∙̂ 𝔬₂) where field fmap : 𝓯map
open 𝓕map ⦃ … ⦄ public
