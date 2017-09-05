
open import Oscar.Prelude
open import Oscar.Class
open import Oscar.Class.Surjection
open import Oscar.Class.Smap
open import Oscar.Class.Transitivity

module Oscar.Class.Surjtranscommutativity where

module Surjtranscommutativity
  {𝔬₁} {𝔒₁ : Ø 𝔬₁}
  {𝔯₁} (_∼₁_ : 𝔒₁ → 𝔒₁ → Ø 𝔯₁)
  {𝔬₂} {𝔒₂ : Ø 𝔬₂}
  {𝔯₂} (_∼₂_ : 𝔒₂ → 𝔒₂ → Ø 𝔯₂)
  {ℓ₂} (_∼̇₂_ : ∀ {x y} → x ∼₂ y → x ∼₂ y → Ø ℓ₂) (let infix 4 _∼̇₂_ ; _∼̇₂_ = _∼̇₂_)
  ⦃ _ : Surjection.class 𝔒₁ 𝔒₂ ⦄
  ⦃ _ : Smap!.class _∼₁_ _∼₂_ ⦄
  ⦃ _ : Transitivity.class _∼₁_ ⦄
  ⦃ _ : Transitivity.class _∼₂_ ⦄
  = ℭLASS (λ {x y} → _∼̇₂_ {x} {y}) (∀ {x y z} (f : x ∼₁ y) (g : y ∼₁ z) → smap (g ∙ f) ∼̇₂ smap g ∙ smap f)

module _
  {𝔬₁} {𝔒₁ : Ø 𝔬₁}
  {𝔯₁} (_∼₁_ : 𝔒₁ → 𝔒₁ → Ø 𝔯₁)
  {𝔬₂} {𝔒₂ : Ø 𝔬₂}
  {𝔯₂} (_∼₂_ : 𝔒₂ → 𝔒₂ → Ø 𝔯₂)
  {ℓ₂} (_∼̇₂_ : ∀ {x y} → x ∼₂ y → x ∼₂ y → Ø ℓ₂) (let infix 4 _∼̇₂_ ; _∼̇₂_ = _∼̇₂_)
  ⦃ _ : Surjection.class 𝔒₁ 𝔒₂ ⦄
  ⦃ _ : Smap!.class _∼₁_ _∼₂_ ⦄
  ⦃ _ : Transitivity.class _∼₁_ ⦄
  ⦃ _ : Transitivity.class _∼₂_ ⦄
  where
  open Surjtranscommutativity _∼₁_ _∼₂_ _∼̇₂_ ⦃ ! ⦄ ⦃ ! ⦄ ⦃ ! ⦄ ⦃ ! ⦄ using () renaming (type to 𝓼urjtranscommutativity; class to 𝓢urjtranscommutativity) public

module _
  {𝔬₁} {𝔒₁ : Ø 𝔬₁}
  {𝔯₁} {_∼₁_ : 𝔒₁ → 𝔒₁ → Ø 𝔯₁}
  {𝔬₂} {𝔒₂ : Ø 𝔬₂}
  {𝔯₂} {_∼₂_ : 𝔒₂ → 𝔒₂ → Ø 𝔯₂}
  {ℓ₂} {_∼̇₂_ : ∀ {x y} → x ∼₂ y → x ∼₂ y → Ø ℓ₂}
  ⦃ _ : Surjection.class 𝔒₁ 𝔒₂ ⦄
  ⦃ _ : Smap!.class _∼₁_ _∼₂_ ⦄
  ⦃ _ : Transitivity.class _∼₁_ ⦄
  ⦃ _ : Transitivity.class _∼₂_ ⦄
  where
  open Surjtranscommutativity _∼₁_ _∼₂_ _∼̇₂_ ⦃ ! ⦄ ⦃ ! ⦄ ⦃ ! ⦄ ⦃ ! ⦄ using () renaming (method to surjtranscommutativity) public
  ⟪∙⟫-surjtranscommutativity-syntax = surjtranscommutativity
  syntax ⟪∙⟫-surjtranscommutativity-syntax f g = g ⟪∙⟫ f

module _
  {𝔬₁} {𝔒₁ : Ø 𝔬₁}
  {𝔯₁} {_∼₁_ : 𝔒₁ → 𝔒₁ → Ø 𝔯₁}
  {𝔬₂} {𝔒₂ : Ø 𝔬₂}
  {𝔯₂} {_∼₂_ : 𝔒₂ → 𝔒₂ → Ø 𝔯₂}
  {ℓ₂} (_∼̇₂_ : ∀ {x y} → x ∼₂ y → x ∼₂ y → Ø ℓ₂)
  ⦃ _ : Surjection.class 𝔒₁ 𝔒₂ ⦄
  ⦃ _ : Smap!.class _∼₁_ _∼₂_ ⦄
  ⦃ _ : Transitivity.class _∼₁_ ⦄
  ⦃ _ : Transitivity.class _∼₂_ ⦄
  where
  open Surjtranscommutativity _∼₁_ _∼₂_ _∼̇₂_ ⦃ ! ⦄ ⦃ ! ⦄ ⦃ ! ⦄ ⦃ ! ⦄ using () renaming (method to surjtranscommutativity[_]) public
  ⟪∙⟫-surjtranscommutativity[]-syntax = surjtranscommutativity[_]
  syntax ⟪∙⟫-surjtranscommutativity[]-syntax t f g = g ⟪∙⟫[ t ] f
