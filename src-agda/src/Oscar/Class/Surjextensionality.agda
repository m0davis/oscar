
open import Oscar.Prelude
open import Oscar.Class
open import Oscar.Class.Surjection
open import Oscar.Class.Smap
open import Oscar.Data.Constraint

module Oscar.Class.Surjextensionality where

module Surjextensionality
  {𝔬₁ 𝔯₁ ℓ₁ 𝔬₂ 𝔯₂ ℓ₂} {𝔒₁ : Ø 𝔬₁} {𝔒₂ : Ø 𝔬₂}
  (_∼₁_ : 𝔒₁ → 𝔒₁ → Ø 𝔯₁)
  (_∼̇₁_ : ∀ {x y} → x ∼₁ y → x ∼₁ y → Ø ℓ₁)
  (_∼₂_ : 𝔒₂ → 𝔒₂ → Ø 𝔯₂)
  (_∼̇₂_ : ∀ {x y} → x ∼₂ y → x ∼₂ y → Ø ℓ₂)
  (surjection : Surjection.type 𝔒₁ 𝔒₂)
  (smap : Smap.type _∼₁_ _∼₂_ surjection surjection)
  where
  open ℭLASS (_∼₁_ ,, {- FIXME including `(λ {x y} → _∼̇₁_ {x} {y}) ,, ` leads to instance search depth exhausted in Oscar.Data.Surjextenscollation -} _∼₂_ ,, (λ {x y} → _∼̇₂_ {x} {y}) ,, surjection ,, (λ {x y} → smap {x} {y})) (∀ x y (f₁ f₂ : x ∼₁ y) → f₁ ∼̇₁ f₂ → smap f₁ ∼̇₂ smap f₂) public
  TYPE = ∀ {x y} {f₁ f₂ : x ∼₁ y} → f₁ ∼̇₁ f₂ → smap f₁ ∼̇₂ smap f₂

module Surjextensionality!
  {𝔬₁ 𝔯₁ ℓ₁ 𝔬₂ 𝔯₂ ℓ₂} {𝔒₁ : Ø 𝔬₁} {𝔒₂ : Ø 𝔬₂}
  (_∼₁_ : 𝔒₁ → 𝔒₁ → Ø 𝔯₁)
  (_∼̇₁_ : ∀ {x y} → _∼₁_ x y → _∼₁_ x y → Ø ℓ₁)
  (_∼₂_ : 𝔒₂ → 𝔒₂ → Ø 𝔯₂)
  (_∼̇₂_ : ∀ {x y} → _∼₂_ x y → _∼₂_ x y → Ø ℓ₂)
  ⦃ _ : Surjection.class 𝔒₁ 𝔒₂ ⦄
  ⦃ _ : Smap.class _∼₁_ _∼₂_ surjection surjection ⦄
  = Surjextensionality (_∼₁_) (λ {x y} → _∼̇₁_ {x} {y}) (_∼₂_) (λ {x y} → _∼̇₂_ {x} {y}) surjection (λ {x y} → smap {x = x} {y})

module _
  {𝔬₁ 𝔯₁ ℓ₁ 𝔬₂ 𝔯₂ ℓ₂} {𝔒₁ : Ø 𝔬₁} {𝔒₂ : Ø 𝔬₂}
  {∼₁ : 𝔒₁ → 𝔒₁ → Ø 𝔯₁}
  {∼̇₁ : ∀ {x y} → ∼₁ x y → ∼₁ x y → Ø ℓ₁}
  {∼₂ : 𝔒₂ → 𝔒₂ → Ø 𝔯₂}
  {∼̇₂ : ∀ {x y} → ∼₂ x y → ∼₂ x y → Ø ℓ₂}
  {surjection : Surjection.type 𝔒₁ 𝔒₂}
  {smap : Smap.type ∼₁ ∼₂ surjection surjection}
  where
  open Surjextensionality
    ∼₁
    (λ {x y} → ∼̇₁ {x} {y})
    ∼₂
    (λ {x y} → ∼̇₂ {x} {y})
    surjection
    (λ {x y} → smap {x = x} {y})
  surjextensionality : ⦃ _ : class ⦄ → TYPE
  surjextensionality = method _ _ _ _

module _
  {𝔬₁ 𝔯₁ ℓ₁ 𝔬₂ 𝔯₂ ℓ₂} {𝔒₁ : Ø 𝔬₁} {𝔒₂ : Ø 𝔬₂}
  {∼₁ : 𝔒₁ → 𝔒₁ → Ø 𝔯₁}
  {∼̇₁ : ∀ {x y} → ∼₁ x y → ∼₁ x y → Ø ℓ₁}
  {∼₂ : 𝔒₂ → 𝔒₂ → Ø 𝔯₂}
  (∼̇₂ : ∀ {x y} → ∼₂ x y → ∼₂ x y → Ø ℓ₂)
  {surjection : Surjection.type 𝔒₁ 𝔒₂}
  {smap : Smap.type ∼₁ ∼₂ surjection surjection}
  where
  open Surjextensionality
    ∼₁
    (λ {x y} → ∼̇₁ {x} {y})
    ∼₂
    (λ {x y} → ∼̇₂ {x} {y})
    surjection
    (λ {x y} → smap {x = x} {y})
  surjextensionality[_] : ⦃ _ : class ⦄ → TYPE
  surjextensionality[_] = surjextensionality
  ⟪⟫-surjextensionality[]-syntax = surjextensionality[_]
  syntax ⟪⟫-surjextensionality[]-syntax t x = ⟪ x ⟫[ t ]
