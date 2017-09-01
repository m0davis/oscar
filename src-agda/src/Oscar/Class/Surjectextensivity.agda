
open import Oscar.Prelude
open import Oscar.Class.Smap
open import Oscar.Class.Surjection

module Oscar.Class.Surjectextensivity where

module Surjectextensivity
  {𝔵₁ 𝔯₁ 𝔵₂ 𝔯₂} {𝔛₁ : Ø 𝔵₁} {𝔛₂ : Ø 𝔵₂}
  (ℜ : 𝔛₁ → 𝔛₁ → Ø 𝔯₁)
  (𝔓 : 𝔛₂ → Ø 𝔯₂)
  ⦃ _ : Surjection.class 𝔛₁ 𝔛₂ ⦄
  = Smap ℜ (Extension 𝔓) surjection

module _
  {𝔵₁ 𝔯₁ 𝔵₂ 𝔯₂} {𝔛₁ : Ø 𝔵₁} {𝔛₂ : Ø 𝔵₂}
  {ℜ : 𝔛₁ → 𝔛₁ → Ø 𝔯₁}
  {𝔓 : 𝔛₂ → Ø 𝔯₂}
  ⦃ _ : Surjection.class 𝔛₁ 𝔛₂ ⦄
  where
  open Surjectextensivity ℜ 𝔓
  surjectextensivity : ⦃ _ : class ⦄ → type
  surjectextensivity = method
  infixr 10 _◃_
  _◃_ = surjectextensivity

module _
  {𝔵₁ 𝔯₁ 𝔵₂ 𝔯₂} {𝔛₁ : Ø 𝔵₁} {𝔛₂ : Ø 𝔵₂}
  {ℜ : 𝔛₁ → 𝔛₁ → Ø 𝔯₁}
  (𝔓 : 𝔛₂ → Ø 𝔯₂)
  ⦃ _ : Surjection.class 𝔛₁ 𝔛₂ ⦄
  where
  open Surjectextensivity ℜ 𝔓
  surjectextensivity[]syntax : ⦃ _ : class ⦄ → type
  surjectextensivity[]syntax = method
  syntax surjectextensivity[]syntax 𝔛₂ x∼y fx = x∼y ◃[ 𝔛₂ ] fx
