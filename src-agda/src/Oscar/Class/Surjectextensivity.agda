
open import Oscar.Prelude
open import Oscar.Class.Surjectivity using (module 𝔖urjectivity)
open import Oscar.Class.Surjection

module Oscar.Class.Surjectextensivity where

module NewExtensional
  {𝔬₁ 𝔯₁ 𝔬₂ 𝔯₂} {𝔒₁ : Ø 𝔬₁} {𝔒₂ : Ø 𝔬₂} {𝔓 : 𝔒₂ → Ø 𝔯₂}
  where
  module _
    (_∼₁_ : 𝔒₁ → 𝔒₁ → Ø 𝔯₁)
    (μ : 𝔒₁ → 𝔒₂)
    where
    open 𝔖urjectivity _∼₁_ (Extension 𝔓) μ
    𝓢urjectextensivity = Surjectivity
    𝓼urjectextensivity = 𝓈urjectivity
  module _
    {_∼₁_ : 𝔒₁ → 𝔒₁ → Ø 𝔯₁}
    {μ : 𝔒₁ → 𝔒₂}
    where
    open 𝔖urjectivity _∼₁_ (Extension 𝔓) μ
    infixr 10 surjectextensivity
    surjectextensivity = surjectivity⟦_/_/_⟧
    syntax surjectextensivity σ τ = σ ◃ τ
    surjectextensivity!syntax = surjectextensivity
    infixl 10 surjectextensivity!syntax
    syntax surjectextensivity!syntax rxy px = px ● rxy

module OldSurjectextensional
  {𝔬₁ 𝔯₁ 𝔬₂ 𝔯₂} {𝔒₁ : Ø 𝔬₁} {𝔒₂ : Ø 𝔬₂}
  where
  module _
    (_∼₁_ : 𝔒₁ → 𝔒₁ → Ø 𝔯₁)
    (𝔓 : 𝔒₂ → Ø 𝔯₂)
    ⦃ _ : 𝓢urjection 𝔒₁ 𝔒₂ ⦄
    where
    open 𝔖urjectivity _∼₁_ (Extension 𝔓) surjection
    𝓢urjectextensivity = Surjectivity
    𝓼urjectextensivity = 𝓈urjectivity
  module _
    {_∼₁_ : 𝔒₁ → 𝔒₁ → Ø 𝔯₁}
    {𝔓 : 𝔒₂ → Ø 𝔯₂}
    ⦃ _ : 𝓢urjection 𝔒₁ 𝔒₂ ⦄
    where
    open 𝔖urjectivity _∼₁_ (Extension 𝔓) surjection
    infixr 10 surjectextensivity
    surjectextensivity = surjectivity⟦_/_/_⟧
    syntax surjectextensivity σ τ = σ ◃ τ
    surjectextensivity!syntax = surjectextensivity
    infixl 10 surjectextensivity!syntax
    syntax surjectextensivity!syntax rxy px = px ● rxy

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
