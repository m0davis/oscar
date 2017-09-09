
open import Oscar.Prelude
open import Oscar.Class.IsFunctor
open import Oscar.Class.Reflexivity
open import Oscar.Class.Smap
open import Oscar.Class.Surjection
open import Oscar.Class.Transitivity

module Oscar.Class.Functor where

record Functor 𝔬₁ 𝔯₁ ℓ₁ 𝔬₂ 𝔯₂ ℓ₂ : Ø ↑̂ (𝔬₁ ∙̂ 𝔯₁ ∙̂ ℓ₁ ∙̂ 𝔬₂ ∙̂ 𝔯₂ ∙̂ ℓ₂) where
  constructor ∁
  field
    {𝔒₁} : Ø 𝔬₁
    _∼₁_ : 𝔒₁ → 𝔒₁ → Ø 𝔯₁
    _∼̇₁_ : ∀ {x y} → x ∼₁ y → x ∼₁ y → Ø ℓ₁
    ε₁ : Reflexivity.type _∼₁_
    _↦₁_ : Transitivity.type _∼₁_
    {𝔒₂} : Ø 𝔬₂
    _∼₂_ : 𝔒₂ → 𝔒₂ → Ø 𝔯₂
    _∼̇₂_ : ∀ {x y} → x ∼₂ y → x ∼₂ y → Ø ℓ₂
    ε₂ : Reflexivity.type _∼₂_
    _↦₂_ : Transitivity.type _∼₂_
    {μ} : Surjection.type 𝔒₁ 𝔒₂
    functor-smap : Smap.type _∼₁_ _∼₂_ μ μ -- FIXME cannot name this § or smap b/c of namespace conflict
    ⦃ `IsFunctor ⦄ : IsFunctor _∼₁_ _∼̇₁_ ε₁ _↦₁_ _∼₂_ _∼̇₂_ ε₂ _↦₂_ functor-smap
