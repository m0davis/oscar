
open import Oscar.Prelude
open import Oscar.Class
open import Oscar.Class.Surjection
open import Oscar.Data.Proposequality

module Oscar.Class.Smap where

module Smap
  {𝔵₁ 𝔯₁ 𝔵₂ 𝔯₂} {𝔛₁ : Ø 𝔵₁} {𝔛₂ : Ø 𝔵₂}
  (_∼₁_ : 𝔛₁ → 𝔛₁ → Ø 𝔯₁)
  (_∼₂_ : 𝔛₂ → 𝔛₂ → Ø 𝔯₂)
  (μ : Surjection.type 𝔛₁ 𝔛₂)
  where
  open ℭLASS (_∼₁_ , _∼₂_ , μ) (∀ {x y} → x ∼₁ y → μ x ∼₂ μ y) public

open import Oscar.Class.Map

module _
  {𝔵₁ 𝔯₁ 𝔵₂ 𝔯₂} {𝔛₁ : Ø 𝔵₁} {𝔛₂ : Ø 𝔵₂}
  {_∼₁_ : 𝔛₁ → 𝔛₁ → Ø 𝔯₁}
  {_∼₂_ : 𝔛₂ → 𝔛₂ → Ø 𝔯₂}
  {μ : Surjection.type 𝔛₁ 𝔛₂}
  where
  open Smap _∼₁_ _∼₂_ μ
  smap : ⦃ _ : class ⦄ → type
  smap = method
  § = smap

  instance
    sMaptoMap : ⦃ _ : Smap.class _∼₁_ _∼₂_ μ ⦄ → 𝓜ap _∼₁_ (_∼₂_ on μ)
    sMaptoMap .𝓜ap.map = smap

module _
  {𝔵₁ 𝔯₁ 𝔵₂ 𝔯₂} {𝔛₁ : Ø 𝔵₁} {𝔛₂ : Ø 𝔵₂}
  {_∼₁_ : 𝔛₁ → 𝔛₁ → Ø 𝔯₁}
  (_∼₂_ : 𝔛₂ → 𝔛₂ → Ø 𝔯₂)
  (μ : Surjection.type 𝔛₁ 𝔛₂)
  where
  open Smap _∼₁_ _∼₂_ μ
  smap⟦_/_⟧ : ⦃ _ : class ⦄ → type
  smap⟦_/_⟧ = smap

module _
  {𝔵₁ 𝔯₁ 𝔵₂} {𝔛₁ : Ø 𝔵₁} {𝔛₂ : Ø 𝔵₂}
  {_∼₁_ : 𝔛₁ → 𝔛₁ → Ø 𝔯₁}
  (μ : Surjection.type 𝔛₁ 𝔛₂)
  where
  open Smap _∼₁_ _≡_ μ
  ≡-smap⟦_⟧ : ⦃ _ : class ⦄ → type
  ≡-smap⟦_⟧ = smap

module Smap!
  {𝔵₁ 𝔯₁ 𝔵₂ 𝔯₂} {𝔛₁ : Ø 𝔵₁} {𝔛₂ : Ø 𝔵₂}
  (∼₁ : 𝔛₁ → 𝔛₁ → Ø 𝔯₁)
  (∼₂ : 𝔛₂ → 𝔛₂ → Ø 𝔯₂)
  ⦃ _ : Surjection.class 𝔛₁ 𝔛₂ ⦄
  = Smap ∼₁ ∼₂ surjection

module Smaparrow
  {𝔵₁ 𝔵₂ 𝔯 𝔭₁ 𝔭₂} {𝔛₁ : Ø 𝔵₁} {𝔛₂ : Ø 𝔵₂}
  (ℜ : 𝔛₁ → 𝔛₁ → Ø 𝔯)
  (𝔓₁ : 𝔛₂ → Ø 𝔭₁)
  (𝔓₂ : 𝔛₂ → Ø 𝔭₂)
  (surjection : Surjection.type 𝔛₁ 𝔛₂)
  = Smap ℜ (Arrow 𝔓₁ 𝔓₂) surjection

module _
  {𝔵₁ 𝔵₂ 𝔯 𝔭₁ 𝔭₂} {𝔛₁ : Ø 𝔵₁} {𝔛₂ : Ø 𝔵₂}
  {ℜ : 𝔛₁ → 𝔛₁ → Ø 𝔯}
  {𝔓₁ : 𝔛₂ → Ø 𝔭₁}
  {𝔓₂ : 𝔛₂ → Ø 𝔭₂}
  {surjection : Surjection.type 𝔛₁ 𝔛₂}
  where
  open Smaparrow ℜ 𝔓₁ 𝔓₂ surjection
  smaparrow : ⦃ _ : class ⦄ → type
  smaparrow = method
  infixr 10 _◃_
  _◃_ = smaparrow

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