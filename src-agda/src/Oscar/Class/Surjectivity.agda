
open import Oscar.Prelude
open import Oscar.Class
open import Oscar.Class.Surjection
open import Oscar.Data.Proposequality

module Oscar.Class.Surjectivity where

module Surjectivity
  {𝔬₁ 𝔯₁ 𝔬₂ 𝔯₂} {𝔒₁ : Ø 𝔬₁} {𝔒₂ : Ø 𝔬₂}
  (_∼₁_ : 𝔒₁ → 𝔒₁ → Ø 𝔯₁)
  (_∼₂_ : 𝔒₂ → 𝔒₂ → Ø 𝔯₂)
  (μ : Surjection.type 𝔒₁ 𝔒₂)
  where
  open ℭLASS (_∼₁_ , _∼₂_ , μ) (∀ x y → x ∼₁ y → μ x ∼₂ μ y) public
  TYPE = ∀ {x y} → x ∼₁ y → μ x ∼₂ μ y

module _
  {𝔬₁ 𝔯₁ 𝔬₂ 𝔯₂} {𝔒₁ : Ø 𝔬₁} {𝔒₂ : Ø 𝔬₂}
  {_∼₁_ : 𝔒₁ → 𝔒₁ → Ø 𝔯₁}
  {_∼₂_ : 𝔒₂ → 𝔒₂ → Ø 𝔯₂}
  {μ : Surjection.type 𝔒₁ 𝔒₂}
  where
  open Surjectivity _∼₁_ _∼₂_ μ
  surjectivity : ⦃ _ : class ⦄ → TYPE
  surjectivity = method _ _
  § = surjectivity

module _
  {𝔬₁ 𝔯₁ 𝔬₂ 𝔯₂} {𝔒₁ : Ø 𝔬₁} {𝔒₂ : Ø 𝔬₂}
  {_∼₁_ : 𝔒₁ → 𝔒₁ → Ø 𝔯₁}
  (_∼₂_ : 𝔒₂ → 𝔒₂ → Ø 𝔯₂)
  (μ : Surjection.type 𝔒₁ 𝔒₂)
  where
  open Surjectivity _∼₁_ _∼₂_ μ
  surjectivity⟦_/_⟧ : ⦃ _ : class ⦄ → TYPE
  surjectivity⟦_/_⟧ = surjectivity

module _
  {𝔬₁ 𝔯₁ 𝔬₂} {𝔒₁ : Ø 𝔬₁} {𝔒₂ : Ø 𝔬₂}
  {_∼₁_ : 𝔒₁ → 𝔒₁ → Ø 𝔯₁}
  (μ : Surjection.type 𝔒₁ 𝔒₂)
  where
  open Surjectivity _∼₁_ _≡_ μ
  ≡-surjectivity⟦_⟧ : ⦃ _ : class ⦄ → TYPE
  ≡-surjectivity⟦_⟧ = surjectivity

module Surjectivity!
  {𝔬₁ 𝔯₁ 𝔬₂ 𝔯₂} {𝔒₁ : Ø 𝔬₁} {𝔒₂ : Ø 𝔬₂}
  (∼₁ : 𝔒₁ → 𝔒₁ → Ø 𝔯₁)
  (∼₂ : 𝔒₂ → 𝔒₂ → Ø 𝔯₂)
  ⦃ _ : Surjection.class 𝔒₁ 𝔒₂ ⦄
  = Surjectivity ∼₁ ∼₂ surjection
