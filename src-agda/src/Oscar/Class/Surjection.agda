
open import Oscar.Prelude

module Oscar.Class.Surjection where

module _ where

  module _
    {𝔬₁} (𝔒₁ : Ø 𝔬₁)
    {𝔬₂} (𝔒₂ : Ø 𝔬₂)
    where
    module _
      where
      𝓼urjection = 𝔒₁ → 𝔒₂
      record 𝓢urjection : Ø 𝔬₁ ∙̂ 𝔬₂ where
        constructor ∁
        field surjection : 𝓼urjection
  open 𝓢urjection ⦃ … ⦄ public

  surjection[_] : ∀
    {𝔬₁} {𝔒₁ : Ø 𝔬₁}
    {𝔬₂} (𝔒₂ : Ø 𝔬₂)
    ⦃ _ : 𝓢urjection 𝔒₁ 𝔒₂ ⦄
    → 𝓼urjection 𝔒₁ 𝔒₂
  surjection[ _ ] = surjection
