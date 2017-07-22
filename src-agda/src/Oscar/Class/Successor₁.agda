
open import Oscar.Prelude
open import Oscar.Class.Successor₀
open import Oscar.Class.Injectivity

module Oscar.Class.Successor₁ where

module _
  {𝔬} {𝔒 : Ø 𝔬} {𝔭} (𝔓 : 𝔒 → Ø 𝔭)
  where
  record [𝓢uccessor₁] : Ø₀ where
    no-eta-equality
    constructor ∁
  module _
    ⦃ _ : 𝓢uccessor₀ 𝔒 ⦄
    where
    𝓼uccessor₁ = ∀ {m} → 𝔓 m → 𝔓 (⇑₀ m)
    record 𝓢uccessor₁ ⦃ _ : [𝓢uccessor₁] ⦄ : Ø 𝔬 ∙̂ 𝔭 where
      field
        successor₁ : 𝓼uccessor₁

      instance

        `𝓘njection₁ : ∀ {m} → 𝓘njection₁ (λ (_ : 𝔓 m) → 𝔓 (⇑₀ m))
        `𝓘njection₁ {m} .𝓘njection₁.injection₁ = successor₁

        `𝓘njection₂ : 𝓘njection₂ (λ (m : 𝔒) (n : 𝔓 m) → 𝔓 (⇑₀ m))
        `𝓘njection₂ .𝓘njection₂.injection₂ = λ _ → successor₁

open 𝓢uccessor₁ ⦃ … ⦄ public using (successor₁)
open 𝓢uccessor₁ ⦃ … ⦄ public using () renaming (successor₁ to ⇑₁)
