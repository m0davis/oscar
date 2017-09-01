
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
    (§ : Smap.type _∼₁_ _∼₂_ μ)
    (ε₁ : 𝓻eflexivity _∼₁_)
    (ε₂ : 𝓻eflexivity _∼₂_)
    = ℭLASS ((λ {x} {y} → § {x} {y}) , (λ {x} → ε₁ {x}) , (λ {x y} → _∼̇₂_ {x} {y}) , (λ {x} → ε₂ {x})) (∀ {x} → § (ε₁ {x}) ∼̇₂ ε₂)
  module _
    {μ : Surjection.type 𝔒₁ 𝔒₂}
    (_∼₁_ : 𝔒₁ → 𝔒₁ → Ø 𝔯₁)
    (_∼₂_ : 𝔒₂ → 𝔒₂ → Ø 𝔯₂)
    (_∼̇₂_ : ∀ {x y} → x ∼₂ y → x ∼₂ y → Ø ℓ₂)
    (§ : Smap.type _∼₁_ _∼₂_ μ)
    (ε₁ : 𝓻eflexivity _∼₁_)
    (ε₂ : 𝓻eflexivity _∼₂_)
    where
    open Surjidentity _∼₁_ _∼₂_ _∼̇₂_ (λ {x} {y} → § {x} {y}) (λ {x} → ε₁ {x}) (λ {x} → ε₂ {x}) public
      using () renaming (class to Surjidentity; type to 𝓼urjidentity')
  module _
    {μ : Surjection.type 𝔒₁ 𝔒₂}
    {_∼₁_ : 𝔒₁ → 𝔒₁ → Ø 𝔯₁}
    {_∼₂_ : 𝔒₂ → 𝔒₂ → Ø 𝔯₂}
    {_∼̇₂_ : ∀ {x y} → x ∼₂ y → x ∼₂ y → Ø ℓ₂}
    {§ : Smap.type _∼₁_ _∼₂_ μ}
    {ε₁ : 𝓻eflexivity _∼₁_}
    {ε₂ : 𝓻eflexivity _∼₂_}
    where
    open Surjidentity _∼₁_ _∼₂_ _∼̇₂_ (λ {x} {y} → § {x} {y}) (λ {x} → ε₁ {x}) (λ {x} → ε₂ {x}) public
      using () renaming (method to surjidentity) public
  module _
    (_∼₁_ : 𝔒₁ → 𝔒₁ → Ø 𝔯₁)
    (_∼₂_ : 𝔒₂ → 𝔒₂ → Ø 𝔯₂)
    (_∼̇₂_ : ∀ {x y} → x ∼₂ y → x ∼₂ y → Ø ℓ₂)
    ⦃ _ : Surjection.class 𝔒₁ 𝔒₂ ⦄
    ⦃ _ : Smap!.class _∼₁_ _∼₂_ ⦄
    ⦃ _ : 𝓡eflexivity _∼₁_ ⦄
    ⦃ _ : 𝓡eflexivity _∼₂_ ⦄
    where
    open Surjidentity {surjection} _∼₁_ _∼₂_ _∼̇₂_ § ε ε public
      using () renaming (class to 𝓢urjidentity; type to 𝓼urjidentity) public
  module _
    (_∼₁_ : 𝔒₁ → 𝔒₁ → Ø 𝔯₁)
    {_∼₂_ : 𝔒₂ → 𝔒₂ → Ø 𝔯₂}
    (_∼̇₂_ : ∀ {x y} → x ∼₂ y → x ∼₂ y → Ø ℓ₂)
    ⦃ _ : Surjection.class 𝔒₁ 𝔒₂ ⦄
    ⦃ _ : Smap!.class _∼₁_ _∼₂_ ⦄
    ⦃ _ : 𝓡eflexivity _∼₁_ ⦄
    ⦃ _ : 𝓡eflexivity _∼₂_ ⦄
    where
    open Surjidentity {surjection} _∼₁_ _∼₂_ _∼̇₂_ § ε ε using () renaming (method to surjidentity[_,_]) public
