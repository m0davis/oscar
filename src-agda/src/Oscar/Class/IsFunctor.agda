
open import Oscar.Prelude
open import Oscar.Class.IsCategory
open import Oscar.Class.IsPrefunctor
open import Oscar.Class.Surjidentity

module Oscar.Class.IsFunctor where

module _
  {𝔬₁} {𝔒₁ : Ø 𝔬₁}
  {𝔯₁} (_∼₁_ : 𝔒₁ → 𝔒₁ → Ø 𝔯₁)
  {ℓ₁} (_∼̇₁_ : ∀ {x y} → x ∼₁ y → x ∼₁ y → Ø ℓ₁)
  {𝔬₂} {𝔒₂ : Ø 𝔬₂}
  {𝔯₂} (_∼₂_ : 𝔒₂ → 𝔒₂ → Ø 𝔯₂)
  {ℓ₂} (_∼̇₂_ : ∀ {x y} → x ∼₂ y → x ∼₂ y → Ø ℓ₂)
  where
  record IsFunctor : Ø 𝔬₁ ∙̂ ↑̂ 𝔯₁ ∙̂ ℓ₁ ∙̂ ↑̂ (𝔬₂ ∙̂ 𝔯₂ ∙̂ ℓ₂) where
    constructor ∁
    field
      ⦃ `IsPrefunctor ⦄ : IsPrefunctor _∼₁_ _∼̇₁_ _∼₂_ _∼̇₂_
      overlap ⦃ `IsCategory₁ ⦄ : IsCategory _∼₁_ _∼̇₁_
      overlap ⦃ `IsCategory₂ ⦄ : IsCategory _∼₂_ _∼̇₂_
      overlap ⦃ `[𝒮urjidentity] ⦄ : [𝓢urjidentity] _∼₁_ _∼₂_ _∼̇₂_
      overlap ⦃ `𝒮urjidentity ⦄ : 𝓢urjidentity _∼₁_ _∼₂_ _∼̇₂_
