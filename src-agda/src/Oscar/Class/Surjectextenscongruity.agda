
open import Oscar.Prelude
open import Oscar.Class.Similarity
open import Oscar.Class.Surjectextensivity
open import Oscar.Data.Constraint
import Oscar.Class.Surjection.⋆

module Oscar.Class.Surjectextenscongruity where

module _
  {𝔬} {𝔒 : Ø 𝔬}
  {𝔯} (_∼ᵣ_ : π̂² 𝔯 𝔒)
  {𝔭} (𝔓 : π̂ 𝔭 𝔒)
  {ℓ} (_∼ₚ_ : ∀̇ π̂² ℓ 𝔓)
  ⦃ _ : 𝓢urjectextensivity _∼ᵣ_ 𝔓 ⦄
  where
  𝓢urjectextenscongruity : Ø _
  𝓢urjectextenscongruity = ∀ {m n} → Similarity.class (_∼ₚ_ {m}) (_∼ₚ_ {n}) (surjectextensivity {x = m} {n})
