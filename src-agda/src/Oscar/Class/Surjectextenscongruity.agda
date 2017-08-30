
open import Oscar.Class.Similarity
open import Oscar.Class.Surjectextensivity
open import Oscar.Class.Surjection
open import Oscar.Prelude

module Oscar.Class.Surjectextenscongruity where

module _
  {𝔬₁} {𝔒₁ : Ø 𝔬₁}
  {𝔬₂} {𝔒₂ : Ø 𝔬₂}
  {𝔯} (_∼ᵣ_ : π̂² 𝔯 𝔒₁)
  {𝔭} (𝔓 : π̂ 𝔭 𝔒₂)
  ⦃ _ : Surjection.class 𝔒₁ 𝔒₂ ⦄
  {ℓ} (_∼ₚ_ : ∀̇ π̂² ℓ (𝔓 ∘ surjection))
  ⦃ _ : Surjectextensivity.class _∼ᵣ_ 𝔓 ⦄
  where
  𝓢urjectextenscongruity : Ø _
  𝓢urjectextenscongruity = ∀ {m n} → Similarity.class (_∼ₚ_ {m}) (_∼ₚ_ {n}) (surjectextensivity {x = m} {n})
