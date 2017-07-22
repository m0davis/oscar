
open import Oscar.Prelude

module Oscar.Class.Surjectextensivity where

module _
  {𝔬₁} {𝔒₁ : Ø 𝔬₁}
  {𝔯₁} (_∼₁_ : 𝔒₁ → 𝔒₁ → Ø 𝔯₁)
  {𝔬₂} (𝔒₂ : 𝔒₁ → Ø 𝔬₂)
  where
  module _
    where
    𝓼urjectextensivity = ∀ {x y} → x ∼₁ y → 𝔒₂ x → 𝔒₂ y
    record 𝓢urjectextensivity : Ø 𝔬₁ ∙̂ 𝔯₁ ∙̂ 𝔬₂ where
      field
        surjectextensivity : 𝓼urjectextensivity
      infixr 10 surjectextensivity
      syntax surjectextensivity σ τ = σ ◃ τ
      surjectextensivity!syntax = surjectextensivity
      infixl 10 surjectextensivity!syntax
      syntax surjectextensivity!syntax rxy px = px ● rxy

open 𝓢urjectextensivity ⦃ … ⦄ public

surjectextensivity[]syntax : ∀
  {𝔬₁} {𝔒₁ : Ø 𝔬₁}
  {𝔯₁} {_∼₁_ : 𝔒₁ → 𝔒₁ → Ø 𝔯₁}
  {𝔬₂} (𝔒₂ : 𝔒₁ → Ø 𝔬₂)
  ⦃ _ : 𝓢urjectextensivity _∼₁_ 𝔒₂ ⦄
  → 𝓼urjectextensivity _∼₁_ 𝔒₂
surjectextensivity[]syntax _ = surjectextensivity

syntax surjectextensivity[]syntax 𝔒₂ x∼y fx = x∼y ◃[ 𝔒₂ ] fx
