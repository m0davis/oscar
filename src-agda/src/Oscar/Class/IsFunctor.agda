
open import Oscar.Prelude
open import Oscar.Class.IsCategory
open import Oscar.Class.IsPrefunctor
open import Oscar.Class.Reflexivity
open import Oscar.Class.Smap
open import Oscar.Class.Surjection
open import Oscar.Class.Surjidentity
open import Oscar.Class.Transitivity

module Oscar.Class.IsFunctor where

module _
  {𝔬₁} {𝔒₁ : Ø 𝔬₁}
  {𝔯₁} (_∼₁_ : 𝔒₁ → 𝔒₁ → Ø 𝔯₁)
  {ℓ₁} (_∼̇₁_ : ∀ {x y} → x ∼₁ y → x ∼₁ y → Ø ℓ₁)
  (ε₁ : Reflexivity.type _∼₁_)
  (_↦₁_ : Transitivity.type _∼₁_)
  {𝔬₂} {𝔒₂ : Ø 𝔬₂}
  {𝔯₂} (_∼₂_ : 𝔒₂ → 𝔒₂ → Ø 𝔯₂)
  {ℓ₂} (_∼̇₂_ : ∀ {x y} → x ∼₂ y → x ∼₂ y → Ø ℓ₂)
  (ε₂ : Reflexivity.type _∼₂_)
  (_↦₂_ : Transitivity.type _∼₂_)
  {surjection : Surjection.type 𝔒₁ 𝔒₂}
  (smap : Smap.type _∼₁_ _∼₂_ surjection surjection)
  where
  record IsFunctor : Ø 𝔬₁ ∙̂ ↑̂ 𝔯₁ ∙̂ ℓ₁ ∙̂ ↑̂ (𝔬₂ ∙̂ 𝔯₂ ∙̂ ℓ₂) where
    constructor ∁
    field
      ⦃ `IsPrefunctor ⦄ : IsPrefunctor _∼₁_ _∼̇₁_ _↦₁_ _∼₂_ _∼̇₂_ _↦₂_ smap
      overlap ⦃ `IsCategory₁ ⦄ : IsCategory _∼₁_ _∼̇₁_ ε₁ _↦₁_
      overlap ⦃ `IsCategory₂ ⦄ : IsCategory _∼₂_ _∼̇₂_ ε₂ _↦₂_
      overlap ⦃ `𝒮urjidentity ⦄ : Surjidentity.class _∼₁_ _∼₂_ _∼̇₂_ smap ε₁ ε₂
