
open import Oscar.Prelude
open import Oscar.Class.Transitivity
open import Oscar.Class.Reflexivity
open import Oscar.Class.Transleftidentity
open import Oscar.Class.Symmetry

module Oscar.Class.PropId where

open import Oscar.Class

module Relpropid
  {𝔭₁} (𝔓₁ : Ø 𝔭₁)
  (p₁ : 𝔓₁ → 𝔓₁)
  {𝔭₂} (𝔓₂ : Ø 𝔭₂)
  {𝔭̇₁₂} (𝔓̇₁₂ : 𝔓₁ → 𝔓₂ → Ø 𝔭̇₁₂)
  = ℭLASS (𝔓₁ ,, p₁)
          (∀ {P₁ : 𝔓₁} (P₂ : 𝔓₂)
           → 𝔓̇₁₂ P₁ P₂ → 𝔓̇₁₂ (p₁ P₁) P₂)

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
    → ∀ {m n} → Relpropid.class (m ∼ n) (λ f → transitivity f reflexivity) (LeftExtensionṖroperty ℓ _∼_ _∼̇_ m) (λ f P → π₀ (π₀ P) f)
  Relprop'idFromTransleftidentity .⋆ (_ , P₁) = P₁ $ symmetry transleftidentity
