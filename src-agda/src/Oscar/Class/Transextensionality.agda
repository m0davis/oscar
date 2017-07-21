
open import Oscar.Prelude
open import Oscar.Class.Transitivity

module Oscar.Class.Transextensionality where

module _
  {𝔬} {𝔒 : Ø 𝔬}
  {𝔯} (_∼_ : 𝔒 → 𝔒 → Ø 𝔯)
  {ℓ} (_∼̇_ : ∀ {x y} → x ∼ y → x ∼ y → Ø ℓ) (let infix 4 _∼̇_ ; _∼̇_ = _∼̇_)
  where
  record [𝓣ransextensionality] : Ø₀ where
    no-eta-equality
    constructor ∁
  module _
    ⦃ _ : 𝓣ransitivity _∼_ ⦄
    where
    𝓽ransextensionality = ∀ {x y z} {f₁ f₂ : x ∼ y} {g₁ g₂ : y ∼ z} → f₁ ∼̇ f₂ → g₁ ∼̇ g₂ → g₁ ∙ f₁ ∼̇ g₂ ∙ f₂
    record 𝓣ransextensionality ⦃ _ : [𝓣ransextensionality] ⦄ : Ø 𝔬 ∙̂ 𝔯 ∙̂ ℓ where
      field transextensionality : 𝓽ransextensionality
      syntax transextensionality f₁∼̇f₂ g₁∼̇g₂ = g₁∼̇g₂ ⟨∙⟩ f₁∼̇f₂
      infixr 19 transextensionality
open 𝓣ransextensionality ⦃ … ⦄ public
