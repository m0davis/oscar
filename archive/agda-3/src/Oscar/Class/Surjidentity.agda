
open import Oscar.Prelude
open import Oscar.Class
open import Oscar.Class.Surjection
open import Oscar.Class.Smap
open import Oscar.Class.Reflexivity
open import Oscar.Data.Proposequality

module Oscar.Class.Surjidentity where

module _
  {𝔬₁ 𝔯₁ 𝔬₂ 𝔯₂ ℓ₂}
  {𝔒₁ : Ø 𝔬₁}
  {𝔒₂ : Ø 𝔬₂}
  where
  module Surjidentity
    {μ : Surjection.type 𝔒₁ 𝔒₂}
    (_∼₁_ : 𝔒₁ → 𝔒₁ → Ø 𝔯₁)
    (_∼₂_ : 𝔒₂ → 𝔒₂ → Ø 𝔯₂)
    (_∼̇₂_ : ∀ {x y} → x ∼₂ y → x ∼₂ y → Ø ℓ₂)
    (§ : Smap.type _∼₁_ _∼₂_ μ μ)
    (ε₁ : Reflexivity.type _∼₁_)
    (ε₂ : Reflexivity.type _∼₂_)
    = ℭLASS ((λ {x} {y} → § {x} {y}) , (λ {x} → ε₁ {x}) , (λ {x y} → _∼̇₂_ {x} {y}) , (λ {x} → ε₂ {x})) (∀ {x} → § (ε₁ {x}) ∼̇₂ ε₂)
  module _
    {μ : Surjection.type 𝔒₁ 𝔒₂}
    {_∼₁_ : 𝔒₁ → 𝔒₁ → Ø 𝔯₁}
    {_∼₂_ : 𝔒₂ → 𝔒₂ → Ø 𝔯₂}
    {_∼̇₂_ : ∀ {x y} → x ∼₂ y → x ∼₂ y → Ø ℓ₂}
    {§ : Smap.type _∼₁_ _∼₂_ μ μ}
    {ε₁ : Reflexivity.type _∼₁_}
    {ε₂ : Reflexivity.type _∼₂_}
    where
    surjidentity = Surjidentity.method _∼₁_ _∼₂_ _∼̇₂_ (λ {x} {y} → § {x} {y}) (λ {x} → ε₁ {x}) (λ {x} → ε₂ {x})
  module Surjidentity!
    (∼₁ : 𝔒₁ → 𝔒₁ → Ø 𝔯₁)
    (∼₂ : 𝔒₂ → 𝔒₂ → Ø 𝔯₂)
    (∼̇₂ : ∀ {x y} → ∼₂ x y → ∼₂ x y → Ø ℓ₂)
    ⦃ _ : Surjection.class 𝔒₁ 𝔒₂ ⦄
    ⦃ _ : Smap!.class ∼₁ ∼₂ ⦄
    ⦃ _ : Reflexivity.class ∼₁ ⦄
    ⦃ _ : Reflexivity.class ∼₂ ⦄
    = Surjidentity {surjection} ∼₁ ∼₂ ∼̇₂ § ε ε
  module _
    (_∼₁_ : 𝔒₁ → 𝔒₁ → Ø 𝔯₁)
    {_∼₂_ : 𝔒₂ → 𝔒₂ → Ø 𝔯₂}
    (_∼̇₂_ : ∀ {x y} → x ∼₂ y → x ∼₂ y → Ø ℓ₂)
    ⦃ _ : Surjection.class 𝔒₁ 𝔒₂ ⦄
    ⦃ _ : Smap!.class _∼₁_ _∼₂_ ⦄
    ⦃ _ : Reflexivity.class _∼₁_ ⦄
    ⦃ _ : Reflexivity.class _∼₂_ ⦄
    where
    surjidentity[_,_] = Surjidentity.method {surjection} _∼₁_ _∼₂_ _∼̇₂_ § ε ε
