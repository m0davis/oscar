
open import Oscar.Prelude
open import Oscar.Class.Transitivity
open import Oscar.Class.Reflexivity
open import Oscar.Class.Transleftidentity
open import Oscar.Class.Symmetry

module Oscar.Class.PropId where

open import Oscar.Class

module Relpropid
  {𝔵} {𝔛 : Ø 𝔵}
  {𝔭₁} (𝔓₁ : 𝔛 → Ø 𝔭₁)
  (p₁ : ∀ {x} → 𝔓₁ x → 𝔓₁ x)
  {𝔭₂} (𝔓₂ : 𝔛 → Ø 𝔭₂)
  {𝔭̇₁₂} (𝔓̇₁₂ : ∀ {m} → 𝔓₂ m → 𝔓₁ m → Ø 𝔭̇₁₂)
  = ℭLASS (𝔓₁ ,, (λ {x} → p₁ {x}))
          (∀ {m} {P₁ : 𝔓₁ m} (P₂ : 𝔓₂ m)
           → 𝔓̇₁₂ P₂ P₁ → 𝔓̇₁₂ P₂ (p₁ P₁))

instance
  RelpropidFromTransleftidentity : ∀
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
    → ∀ {n} → Relpropid.class (_∼ n) (λ f → transitivity f reflexivity) (LeftExtensionṖroperty ℓ _∼_ _∼̇_) (λ P f → π₀ (π₀ P) f)
  RelpropidFromTransleftidentity .⋆ (_ , P₁) = P₁ $ symmetry transleftidentity
