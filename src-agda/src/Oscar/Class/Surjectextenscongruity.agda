
open import Oscar.Prelude
open import Oscar.Class.Surjectextensivity
import Oscar.Class.Surjection.⋆

module Oscar.Class.Surjectextenscongruity where

record [𝓢urjectextenscongruity]
  {𝔬} {𝔒 : Ø 𝔬}
  {𝔯} (_∼ᵣ_ : π̂² 𝔯 𝔒)
  {𝔭} (𝔓 : π̂ 𝔭 𝔒)
  {ℓ} (_∼ₚ_ : ∀̇ π̂² ℓ 𝔓)
  : Ø₀ where
  no-eta-equality
  constructor ∁

record 𝓢urjectextenscongruity
  {𝔬} {𝔒 : Ø 𝔬}
  {𝔯} (_∼ᵣ_ : π̂² 𝔯 𝔒)
  {𝔭} (𝔓 : π̂ 𝔭 𝔒)
  {ℓ} (_∼ₚ_ : ∀̇ π̂² ℓ 𝔓)
  ⦃ _ : [𝓢urjectextenscongruity] _∼ᵣ_ 𝔓 _∼ₚ_ ⦄
  ⦃ _ : 𝓢urjectextensivity _∼ᵣ_ 𝔓 ⦄
  : Ø 𝔬 ∙̂ 𝔭 ∙̂ 𝔯 ∙̂ ℓ where
  field
    surjectextenscongruity : ∀
      {m n} {P Q : 𝔓 m} (f : m ∼ᵣ n) → P ∼ₚ Q → (f ◃ P) ∼ₚ (f ◃ Q)

open 𝓢urjectextenscongruity ⦃ … ⦄ public
