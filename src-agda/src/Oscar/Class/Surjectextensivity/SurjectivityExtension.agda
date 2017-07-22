
open import Oscar.Prelude
open import Oscar.Class.Surjectivity
open import Oscar.Class.Surjectextensivity

module Oscar.Class.Surjectextensivity.SurjectivityExtension where

instance

  toSurj' : ∀
    {𝔬₁} {𝔒₁ : Ø 𝔬₁}
    {𝔯₁} {_∼₁_ : 𝔒₁ → 𝔒₁ → Ø 𝔯₁}
    {𝔬₂} {𝔒₂ : 𝔒₁ → Ø 𝔬₂}
    ⦃ _ : [𝓢urjectivity] _∼₁_ (Extension 𝔒₂) ⦄
    ⦃ _ : 𝓢urjectivity _∼₁_ (Extension 𝔒₂) ⦃ record { surjection = ¡ } ⦄ ⦄
    → 𝓢urjectextensivity _∼₁_ 𝔒₂
  toSurj' {{_}} {{x₂}} .𝓢urjectextensivity.surjectextensivity = § {{r = x₂}}
