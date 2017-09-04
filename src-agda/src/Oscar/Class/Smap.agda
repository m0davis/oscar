
open import Oscar.Prelude
open import Oscar.Class
open import Oscar.Class.Surjection
open import Oscar.Data.Proposequality

module Oscar.Class.Smap where

module Smap
  {𝔵₁ 𝔯₁ 𝔵₂ 𝔯₂} {𝔛₁ : Ø 𝔵₁} {𝔛₂ : Ø 𝔵₂}
  (_∼₁_ : 𝔛₁ → 𝔛₁ → Ø 𝔯₁)
  (_∼₂_ : 𝔛₂ → 𝔛₂ → Ø 𝔯₂)
  (μ₁ μ₂ : Surjection.type 𝔛₁ 𝔛₂)
  = ℭLASS (_∼₁_ , _∼₂_ , μ₁ , μ₂) (∀ {x y} → x ∼₁ y → μ₁ x ∼₂ μ₂ y)

module _
  {𝔵₁ 𝔯₁ 𝔵₂ 𝔯₂} {𝔛₁ : Ø 𝔵₁} {𝔛₂ : Ø 𝔵₂}
  {_∼₁_ : 𝔛₁ → 𝔛₁ → Ø 𝔯₁}
  {_∼₂_ : 𝔛₂ → 𝔛₂ → Ø 𝔯₂}
  {μ₁ μ₂ : Surjection.type 𝔛₁ 𝔛₂}
  where
  smap = Smap.method _∼₁_ _∼₂_ μ₁ μ₂
  § = smap

  open import Oscar.Class.Map

  instance
    sMaptoMap : ⦃ _ : Smap.class _∼₁_ _∼₂_ μ₁ μ₂ ⦄ → 𝓜ap _∼₁_ (λ x y → μ₁ x ∼₂ μ₂ y)
    sMaptoMap .𝓜ap.map = smap

module _
  {𝔵₁ 𝔯₁ 𝔵₂ 𝔯₂} {𝔛₁ : Ø 𝔵₁} {𝔛₂ : Ø 𝔵₂}
  {_∼₁_ : 𝔛₁ → 𝔛₁ → Ø 𝔯₁}
  (_∼₂_ : 𝔛₂ → 𝔛₂ → Ø 𝔯₂)
  (μ₁ μ₂ : Surjection.type 𝔛₁ 𝔛₂)
  where
  open Smap _∼₁_ _∼₂_ μ₁ μ₂
  smap⟦_/_/_⟧ : ⦃ _ : class ⦄ → type
  smap⟦_/_/_⟧ = smap

module ≡-Smap
  {𝔵₁ 𝔯₁ 𝔵₂} {𝔛₁ : Ø 𝔵₁} {𝔛₂ : Ø 𝔵₂}
  (∼₁ : 𝔛₁ → 𝔛₁ → Ø 𝔯₁)
  (μ₁ μ₂ : Surjection.type 𝔛₁ 𝔛₂)
  = Smap ∼₁ _≡_ μ₁ μ₂

module _
  {𝔵₁ 𝔯₁ 𝔵₂} {𝔛₁ : Ø 𝔵₁} {𝔛₂ : Ø 𝔵₂}
  {_∼₁_ : 𝔛₁ → 𝔛₁ → Ø 𝔯₁}
  (μ₁ μ₂ : Surjection.type 𝔛₁ 𝔛₂)
  where
  open Smap _∼₁_ _≡_ μ₁ μ₂
  ≡-smap⟦_⟧ : ⦃ _ : class ⦄ → type
  ≡-smap⟦_⟧ = smap

module Smap!
  {𝔵₁ 𝔯₁ 𝔵₂ 𝔯₂} {𝔛₁ : Ø 𝔵₁} {𝔛₂ : Ø 𝔵₂}
  (∼₁ : 𝔛₁ → 𝔛₁ → Ø 𝔯₁)
  (∼₂ : 𝔛₂ → 𝔛₂ → Ø 𝔯₂)
  ⦃ _ : Surjection.class 𝔛₁ 𝔛₂ ⦄
  = Smap ∼₁ ∼₂ surjection surjection

module Smaparrow
  {𝔵₁ 𝔵₂ 𝔯 𝔭₁ 𝔭₂} {𝔛₁ : Ø 𝔵₁} {𝔛₂ : Ø 𝔵₂}
  (ℜ : 𝔛₁ → 𝔛₁ → Ø 𝔯)
  (𝔓₁ : 𝔛₂ → Ø 𝔭₁)
  (𝔓₂ : 𝔛₂ → Ø 𝔭₂)
  (surjection₁ surjection₂ : Surjection.type 𝔛₁ 𝔛₂)
  = Smap ℜ (Arrow 𝔓₁ 𝔓₂) surjection₁ surjection₂

module _
  {𝔵₁ 𝔵₂ 𝔯 𝔭₁ 𝔭₂} {𝔛₁ : Ø 𝔵₁} {𝔛₂ : Ø 𝔵₂}
  {ℜ : 𝔛₁ → 𝔛₁ → Ø 𝔯}
  {𝔓₁ : 𝔛₂ → Ø 𝔭₁}
  {𝔓₂ : 𝔛₂ → Ø 𝔭₂}
  {surjection₁ surjection₂ : Surjection.type 𝔛₁ 𝔛₂}
  where
  smaparrow = Smaparrow.method ℜ 𝔓₁ 𝔓₂ surjection₁ surjection₂
  infixr 10 _◃_
  _◃_ = smaparrow
  smaparrow[]syntax = _◃_
  syntax smaparrow[]syntax 𝔛₂ x∼y fx = x∼y ◃[ 𝔛₂ ] fx

module Smaparrow!
  {𝔵₁ 𝔵₂ 𝔯 𝔭₁ 𝔭₂} {𝔛₁ : Ø 𝔵₁} {𝔛₂ : Ø 𝔵₂}
  (ℜ : 𝔛₁ → 𝔛₁ → Ø 𝔯)
  (𝔓₁ : 𝔛₂ → Ø 𝔭₁)
  (𝔓₂ : 𝔛₂ → Ø 𝔭₂)
  ⦃ _ : Surjection.class 𝔛₁ 𝔛₂ ⦄
  = Smaparrow ℜ 𝔓₁ 𝔓₂ surjection surjection

module Smaphomarrow
  {𝔵₁ 𝔯₁ 𝔵₂ 𝔯₂} {𝔛₁ : Ø 𝔵₁} {𝔛₂ : Ø 𝔵₂}
  (ℜ : 𝔛₁ → 𝔛₁ → Ø 𝔯₁)
  (𝔓 : 𝔛₂ → Ø 𝔯₂)
  (surjection : Surjection.type 𝔛₁ 𝔛₂)
  = Smaparrow ℜ 𝔓 𝔓 surjection surjection

module Smaphomarrow!
  {𝔵₁ 𝔯₁ 𝔵₂ 𝔯₂} {𝔛₁ : Ø 𝔵₁} {𝔛₂ : Ø 𝔵₂}
  (ℜ : 𝔛₁ → 𝔛₁ → Ø 𝔯₁)
  (𝔓 : 𝔛₂ → Ø 𝔯₂)
  ⦃ _ : Surjection.class 𝔛₁ 𝔛₂ ⦄
  = Smaphomarrow ℜ 𝔓 surjection
