
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

module _
  {𝔵₁ 𝔯₁ 𝔵₂ 𝔯₂} {𝔛₁ : Ø 𝔵₁} {𝔛₂ : Ø 𝔵₂}
  {_∼₁_ : 𝔛₁ → 𝔛₁ → Ø 𝔯₁}
  {_∼₂_ : 𝔛₂ → 𝔛₂ → Ø 𝔯₂}
  {μ : Surjection.type 𝔛₁ 𝔛₂}
  where
  open Smap _∼₁_ _∼₂_ μ
  surjectivity : ⦃ _ : class ⦄ → type
  surjectivity = method
  § = surjectivity

module _
  {𝔵₁ 𝔯₁ 𝔵₂ 𝔯₂} {𝔛₁ : Ø 𝔵₁} {𝔛₂ : Ø 𝔵₂}
  {_∼₁_ : 𝔛₁ → 𝔛₁ → Ø 𝔯₁}
  (_∼₂_ : 𝔛₂ → 𝔛₂ → Ø 𝔯₂)
  (μ : Surjection.type 𝔛₁ 𝔛₂)
  where
  open Smap _∼₁_ _∼₂_ μ
  surjectivity⟦_/_⟧ : ⦃ _ : class ⦄ → type
  surjectivity⟦_/_⟧ = surjectivity

module _
  {𝔵₁ 𝔯₁ 𝔵₂} {𝔛₁ : Ø 𝔵₁} {𝔛₂ : Ø 𝔵₂}
  {_∼₁_ : 𝔛₁ → 𝔛₁ → Ø 𝔯₁}
  (μ : Surjection.type 𝔛₁ 𝔛₂)
  where
  open Smap _∼₁_ _≡_ μ
  ≡-surjectivity⟦_⟧ : ⦃ _ : class ⦄ → type
  ≡-surjectivity⟦_⟧ = surjectivity

module Smap!
  {𝔵₁ 𝔯₁ 𝔵₂ 𝔯₂} {𝔛₁ : Ø 𝔵₁} {𝔛₂ : Ø 𝔵₂}
  (∼₁ : 𝔛₁ → 𝔛₁ → Ø 𝔯₁)
  (∼₂ : 𝔛₂ → 𝔛₂ → Ø 𝔯₂)
  ⦃ _ : Surjection.class 𝔛₁ 𝔛₂ ⦄
  = Smap ∼₁ ∼₂ surjection
