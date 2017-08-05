
open import Oscar.Prelude
open import Oscar.Class.Surjectivity

module Oscar.Class.Surjectextensivity where

open OldSurjectextensional public

open import Oscar.Class.Surjection.⋆

surjectextensivity[]syntax : ∀
  {𝔬₁} {𝔒₁ : Ø 𝔬₁}
  {𝔯₁} {_∼₁_ : 𝔒₁ → 𝔒₁ → Ø 𝔯₁}
  {𝔬₂} (𝔒₂ : 𝔒₁ → Ø 𝔬₂)
  ⦃ _ : 𝓢urjectextensivity _∼₁_ 𝔒₂ ⦄
  → 𝓼urjectextensivity _∼₁_ 𝔒₂
surjectextensivity[]syntax _ = surjectextensivity

syntax surjectextensivity[]syntax 𝔒₂ x∼y fx = x∼y ◃[ 𝔒₂ ] fx
