{-# OPTIONS --allow-unsolved-metas #-} -- FIXME

open import Oscar.Prelude
open import Oscar.Class.IsCategory
open import Oscar.Class.IsFunctor
open import Oscar.Class.IsPrecategory
open import Oscar.Class.Reflexivity
open import Oscar.Class.Surjection
open import Oscar.Class.Smap
open import Oscar.Class.Transextensionality
open import Oscar.Class.Transitivity

module Test.Test2 where

  failed-test test-functor-transextensionality test-the-test : ∀
    {𝔬₁} {𝔒₁ : Ø 𝔬₁}
    {𝔯₁} {_∼₁_ : 𝔒₁ → 𝔒₁ → Ø 𝔯₁}
    {ℓ₁} {_∼̇₁_ : ∀ {x y} → x ∼₁ y → x ∼₁ y → Ø ℓ₁}
    {ε₁ : Reflexivity.type _∼₁_}
    {_↦₁_ : Transitivity.type _∼₁_}
    {𝔬₂} {𝔒₂ : Ø 𝔬₂}
    {𝔯₂} {_∼₂_ : 𝔒₂ → 𝔒₂ → Ø 𝔯₂}
    {ℓ₂} {_∼̇₂_ : ∀ {x y} → x ∼₂ y → x ∼₂ y → Ø ℓ₂}
    {ε₂ : Reflexivity.type _∼₂_}
    {_↦₂_ : Transitivity.type _∼₂_}
    {surjection : Surjection.type 𝔒₁ 𝔒₂}
    {smap : Smap.type _∼₁_ _∼₂_ surjection surjection}
    ⦃ I : IsFunctor _∼₁_ _∼̇₁_ ε₁ _↦₁_ _∼₂_ _∼̇₂_ ε₂ _↦₂_ smap ⦄
    ⦃ J : IsFunctor _∼₁_ _∼̇₁_ ε₁ _↦₁_ _∼₂_ _∼̇₂_ ε₂ _↦₂_ smap ⦄
    → Transextensionality.type _∼₁_ _∼̇₁_ _↦₁_

  failed-test = transextensionality

  test-functor-transextensionality {_∼₁_ = _∼₁_} {_∼̇₁_ = _∼̇₁_} {_↦₁_ = _↦₁_} {{I}} = transextensionality {_∼_ = λ z z₁ → z ∼₁ z₁} {_∼̇_ = λ {x} {y} → _∼̇₁_ {x} {y}} {transitivity = λ {x y z} → _↦₁_ {x} {y} {z}} {{I .IsFunctor.`IsCategory₁ .IsCategory.`IsPrecategory .IsPrecategory.`𝓣ransextensionality}} -- FIXME can this be simplified?

  test-the-test {_∼₁_ = _∼₁_} {_∼̇₁_ = _∼̇₁_} {_↦₁_ = _↦₁_} = test-functor-transextensionality {_∼₁_ = _∼₁_} {_∼̇₁_ = _∼̇₁_} {_↦₁_ = _↦₁_}
