
open import Oscar.Prelude
open import Oscar.Class.Surjectivity
open import Oscar.Class.Surjection

module Oscar.Class.Surjectextensivity where

module Surjectextensivity
  {𝔬₁ 𝔯₁ 𝔬₂ 𝔯₂} {𝔒₁ : Ø 𝔬₁} {𝔒₂ : Ø 𝔬₂}
  (∼₁ : 𝔒₁ → 𝔒₁ → Ø 𝔯₁)
  (𝔓 : 𝔒₂ → Ø 𝔯₂)
  ⦃ _ : Surjection.class 𝔒₁ 𝔒₂ ⦄
  = Surjectivity ∼₁ (Extension 𝔓) surjection

module _
  {𝔬₁ 𝔯₁ 𝔬₂ 𝔯₂} {𝔒₁ : Ø 𝔬₁} {𝔒₂ : Ø 𝔬₂}
  {∼₁ : 𝔒₁ → 𝔒₁ → Ø 𝔯₁}
  {𝔓 : 𝔒₂ → Ø 𝔯₂}
  ⦃ _ : Surjection.class 𝔒₁ 𝔒₂ ⦄
  where
  open Surjectextensivity ∼₁ 𝔓
  surjectextensivity : ⦃ _ : class ⦄ → type
  surjectextensivity = method
  infixr 10 _◃_
  _◃_ = surjectextensivity

module _
  {𝔬₁ 𝔯₁ 𝔬₂ 𝔯₂} {𝔒₁ : Ø 𝔬₁} {𝔒₂ : Ø 𝔬₂}
  {∼₁ : 𝔒₁ → 𝔒₁ → Ø 𝔯₁}
  (𝔓 : 𝔒₂ → Ø 𝔯₂)
  ⦃ _ : Surjection.class 𝔒₁ 𝔒₂ ⦄
  where
  open Surjectextensivity ∼₁ 𝔓
  surjectextensivity[]syntax : ⦃ _ : class ⦄ → type
  surjectextensivity[]syntax = method
  syntax surjectextensivity[]syntax 𝔒₂ x∼y fx = x∼y ◃[ 𝔒₂ ] fx
