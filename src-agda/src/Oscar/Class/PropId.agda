
open import Oscar.Prelude
open import Oscar.Class.Transitivity
open import Oscar.Class.Reflexivity
open import Oscar.Class.Transleftidentity
open import Oscar.Class.Symmetry

module Oscar.Class.PropId where

open import Oscar.Class

module Relpropid
  {𝔵₁} (𝔛₁ : Ø 𝔵₁)
  (p₁ : 𝔛₁ → 𝔛₁)
  {𝔵₂} (𝔛₂ : Ø 𝔵₂)
  (p₂ : 𝔛₂ → 𝔛₂)
  {𝔯₁₂} (ℜ₁₂ : 𝔛₁ → 𝔛₂ → Ø 𝔯₁₂)
  = ℭLASS (p₁ , p₂ , ℜ₁₂)
          (∀ {P₁} P₂
           → ℜ₁₂ P₁ P₂ → ℜ₁₂ (p₁ P₁) (p₂ P₂))

instance
  Relprop'idFromTransleftidentity : ∀
    {𝔵} {𝔛 : Ø 𝔵}
    {𝔞} {𝔄 : 𝔛 → Ø 𝔞}
    {𝔟} {𝔅 : 𝔛 → Ø 𝔟}
    (let _∼_ = Arrow 𝔄 𝔅)
    {ℓ̇} {_∼̇_ : ∀ {x y} → x ∼ y → x ∼ y → Ø ℓ̇}
    ⦃ _ : 𝓣ransitivity _∼_ ⦄
    ⦃ _ : 𝓡eflexivity _∼_ ⦄
    {ℓ}
    ⦃ _ : [𝓣ransleftidentity] _∼_ _∼̇_ ⦄
    ⦃ _ : 𝓣ransleftidentity _∼_ _∼̇_ ⦄
    ⦃ _ : ∀ {x y} → 𝓢ymmetry (_∼̇_ {x} {y}) ⦄
    → ∀ {m n}
    → Relpropid.class (m ∼ n)
                      (λ f → transitivity f reflexivity)
                      (LeftExtensionṖroperty ℓ _∼_ _∼̇_ m)
                      ¡
                      (λ f P → π₀ (π₀ P) f)
  Relprop'idFromTransleftidentity .⋆ (_ , P₁) = P₁ $ symmetry transleftidentity
