
open import Oscar.Prelude

module Oscar.Class.Map where

module _
  {𝔬₁} {𝔒₁ : Ø 𝔬₁}
  {ℓ₁} (_∼₁_ : 𝔒₁ → 𝔒₁ → Ø ℓ₁)
  {ℓ₂} (_∼₂_ : 𝔒₁ → 𝔒₁ → Ø ℓ₂)
  where
  𝓶ap = ∀ {x y} → x ∼₁ y → x ∼₂ y
  record 𝓜ap : Ø 𝔬₁ ∙̂ ℓ₁ ∙̂ ℓ₂ where field map : 𝓶ap
open 𝓜ap ⦃ … ⦄ public
