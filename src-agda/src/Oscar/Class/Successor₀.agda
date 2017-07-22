
open import Oscar.Prelude
open import Oscar.Class.Injectivity

module Oscar.Class.Successor₀ where

module _
  {𝔬} (𝔒 : Ø 𝔬)
  where
  𝓼uccessor₀ = 𝔒 → 𝔒
  record 𝓢uccessor₀ : Ø 𝔬 where
    field
      successor₀ : 𝓼uccessor₀

    instance

      `𝓘njection₁ : 𝓘njection₁ (λ (_ : 𝔒) → 𝔒)
      `𝓘njection₁ .𝓘njection₁.injection₁ = successor₀

open 𝓢uccessor₀ ⦃ … ⦄ public using (successor₀)
open 𝓢uccessor₀ ⦃ … ⦄ public using () renaming (successor₀ to ⇑₀)
