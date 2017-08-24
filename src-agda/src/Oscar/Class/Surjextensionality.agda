
open import Oscar.Prelude
open import Oscar.Class
open import Oscar.Class.Surjection
open import Oscar.Class.Surjectivity
open import Oscar.Data.Constraint

module Oscar.Class.Surjextensionality where

module Surjextensionality
  {𝔬₁ 𝔯₁ ℓ₁ 𝔬₂ 𝔯₂ ℓ₂} {𝔒₁ : Ø 𝔬₁} {𝔒₂ : Ø 𝔬₂}
  (_∼₁_ : 𝔒₁ → 𝔒₁ → Ø 𝔯₁)
  (_∼̇₁_ : ∀ {x y} → x ∼₁ y → x ∼₁ y → Ø ℓ₁)
  (_∼₂_ : 𝔒₂ → 𝔒₂ → Ø 𝔯₂)
  (_∼̇₂_ : ∀ {x y} → x ∼₂ y → x ∼₂ y → Ø ℓ₂)
  (surjection : Surjection.type 𝔒₁ 𝔒₂)
  (surjectivity : Surjectivity.type _∼₁_ _∼₂_ surjection)
  where
  open ℭLASS (_∼₁_ ,, (λ {x y} → _∼̇₁_ {x} {y}) ,, _∼₂_ ,, (λ {x y} → _∼̇₂_ {x} {y}) ,, surjection ,, (λ {x y} → surjectivity {x} {y})) (∀ x y (f₁ f₂ : x ∼₁ y) → f₁ ∼̇₁ f₂ → surjectivity f₁ ∼̇₂ surjectivity f₂) public
  TYPE = ∀ {x y} {f₁ f₂ : x ∼₁ y} → f₁ ∼̇₁ f₂ → surjectivity f₁ ∼̇₂ surjectivity f₂

module Surjextensionality!
  {𝔬₁ 𝔯₁ ℓ₁ 𝔬₂ 𝔯₂ ℓ₂} {𝔒₁ : Ø 𝔬₁} {𝔒₂ : Ø 𝔬₂}
  (_∼₁_ : 𝔒₁ → 𝔒₁ → Ø 𝔯₁)
  (_∼̇₁_ : ∀ {x y} → _∼₁_ x y → _∼₁_ x y → Ø ℓ₁)
  (_∼₂_ : 𝔒₂ → 𝔒₂ → Ø 𝔯₂)
  (_∼̇₂_ : ∀ {x y} → _∼₂_ x y → _∼₂_ x y → Ø ℓ₂)
  ⦃ I : Surjection.class 𝔒₁ 𝔒₂ ⦄
  ⦃ J : Surjectivity.class _∼₁_ _∼₂_ surjection ⦄
  where
  -- FIXME want to use this instead: open Surjextensionality _∼₁_ (λ {x y} → _∼̇₁_ {x} {y}) _∼₂_ (λ {x y} → _∼̇₂_ {x} {y}) surjection (λ {x y} → surjectivity {x = x} {y}) public
  open ℭLASS (_∼₁_ ,, (λ {x y} → _∼̇₁_ {x} {y}) ,, _∼₂_ ,, (λ {x y} → _∼̇₂_ {x} {y}) ,, I ,, J) (∀ x y (f₁ f₂ : x ∼₁ y) → f₁ ∼̇₁ f₂ → surjectivity f₁ ∼̇₂ surjectivity f₂) public
  TYPE = ∀ {x y} {f₁ f₂ : x ∼₁ y} → f₁ ∼̇₁ f₂ → surjectivity f₁ ∼̇₂ surjectivity f₂

module _
  {𝔬₁ 𝔯₁ ℓ₁ 𝔬₂ 𝔯₂ ℓ₂} {𝔒₁ : Ø 𝔬₁} {𝔒₂ : Ø 𝔬₂}
  {∼₁ : 𝔒₁ → 𝔒₁ → Ø 𝔯₁}
  {∼̇₁ : ∀ {x y} → ∼₁ x y → ∼₁ x y → Ø ℓ₁}
  {∼₂ : 𝔒₂ → 𝔒₂ → Ø 𝔯₂}
  {∼̇₂ : ∀ {x y} → ∼₂ x y → ∼₂ x y → Ø ℓ₂}
  -- FIXME why not use hidden (non-instance) arguments?
  -- {surjection : Surjection.type 𝔒₁ 𝔒₂}
  -- {surjectivity : Surjectivity.type ∼₁ ∼₂ surjection}
  ⦃ I : Surjection.class 𝔒₁ 𝔒₂ ⦄
  ⦃ J : Surjectivity.class ∼₁ ∼₂ surjection ⦄
  where
  open Surjextensionality!
    ∼₁
    (λ {x y} → ∼̇₁ {x} {y})
    ∼₂
    (λ {x y} → ∼̇₂ {x} {y})
    -- FIXME see above
    -- surjection
    -- (λ {x y} → surjectivity {x = x} {y})
  surjextensionality : ⦃ _ : class ⦄ → TYPE
  surjextensionality = method _ _ _ _

module _
  {𝔬₁ 𝔯₁ ℓ₁ 𝔬₂ 𝔯₂ ℓ₂} {𝔒₁ : Ø 𝔬₁} {𝔒₂ : Ø 𝔬₂}
  {∼₁ : 𝔒₁ → 𝔒₁ → Ø 𝔯₁}
  {∼̇₁ : ∀ {x y} → ∼₁ x y → ∼₁ x y → Ø ℓ₁}
  {∼₂ : 𝔒₂ → 𝔒₂ → Ø 𝔯₂}
  (∼̇₂ : ∀ {x y} → ∼₂ x y → ∼₂ x y → Ø ℓ₂)
  -- FIXME see above
  -- {surjection : Surjection.type 𝔒₁ 𝔒₂}
  -- {surjectivity : Surjectivity.TYPE ∼₁ ∼₂ surjection}
  ⦃ _ : Surjection.class 𝔒₁ 𝔒₂ ⦄
  ⦃ _ : Surjectivity.class ∼₁ ∼₂ surjection ⦄
  where
  open Surjextensionality!
    ∼₁
    (λ {x y} → ∼̇₁ {x} {y})
    ∼₂
    (λ {x y} → ∼̇₂ {x} {y})
    -- FIXME see above
    -- surjection
    -- (λ {x y} → surjectivity {x = x} {y})
  surjextensionality[_] : ⦃ _ : class ⦄ → TYPE
  surjextensionality[_] = surjextensionality
  ⟪⟫-surjextensionality[]-syntax = surjextensionality[_]
  syntax ⟪⟫-surjextensionality[]-syntax t x = ⟪ x ⟫[ t ]
