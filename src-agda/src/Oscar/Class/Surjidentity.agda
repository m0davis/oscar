
open import Oscar.Prelude
open import Oscar.Class.Surjection
open import Oscar.Class.Surjectivity
open import Oscar.Class.Reflexivity
open import Oscar.Data.Proposequality

module Oscar.Class.Surjidentity where

module _
  {𝔬₁ 𝔯₁ 𝔬₂ 𝔯₂ ℓ₂}
  {𝔒₁ : Ø 𝔬₁}
  {𝔒₂ : Ø 𝔬₂}
  where
  module Visible6
    {μ : 𝓼urjection 𝔒₁ 𝔒₂}
    (_∼₁_ : 𝔒₁ → 𝔒₁ → Ø 𝔯₁)
    (_∼₂_ : 𝔒₂ → 𝔒₂ → Ø 𝔯₂)
    (_∼̇₂_ : ∀ {x y} → x ∼₂ y → x ∼₂ y → Ø ℓ₂)
    (§ : 𝓈urjectivity _∼₁_ _∼₂_ μ)
    (ε₁ : 𝓻eflexivity _∼₁_)
    (ε₂ : 𝓻eflexivity _∼₂_)
    where
    𝓼urjidentity' = λ x → § (ε₁ {x}) ∼̇₂ ε₂
    𝓈urjidentity' = ∀ {x} → 𝓼urjidentity' x
    record 𝒮urjidentity
      {𝓢 : _}
      ⦃ _ : 𝓢 ≡ 𝓼urjidentity' ⦄
      : Ø 𝔬₁ ∙̂ ℓ₂
      where
      field surjidentity' : 𝓈urjidentity'
    Surjidentity : Ø _
    Surjidentity = 𝒮urjidentity ⦃ ∅ ⦄
    surjidentityV6 : ⦃ _ : 𝒮urjidentity ⦄ → 𝓈urjidentity'
    surjidentityV6 = 𝒮urjidentity.surjidentity' ⦃ ∅ ⦄ !
  module Hidden
    {μ : 𝓼urjection 𝔒₁ 𝔒₂}
    {_∼₁_ : 𝔒₁ → 𝔒₁ → Ø 𝔯₁}
    {_∼₂_ : 𝔒₂ → 𝔒₂ → Ø 𝔯₂}
    {_∼̇₂_ : ∀ {x y} → x ∼₂ y → x ∼₂ y → Ø ℓ₂}
    {§ : 𝓈urjectivity _∼₁_ _∼₂_ μ}
    {ε₁ : 𝓻eflexivity _∼₁_}
    {ε₂ : 𝓻eflexivity _∼₂_}
    where
    open Visible6 {μ} _∼₁_ _∼₂_ _∼̇₂_ § ε₁ ε₂
    surjidentity = surjidentityV6
  module Standard
    (_∼₁_ : 𝔒₁ → 𝔒₁ → Ø 𝔯₁)
    (_∼₂_ : 𝔒₂ → 𝔒₂ → Ø 𝔯₂)
    (_∼̇₂_ : ∀ {x y} → x ∼₂ y → x ∼₂ y → Ø ℓ₂)
    ⦃ _ : 𝓢urjection 𝔒₁ 𝔒₂ ⦄
    ⦃ _ : 𝒮urjectivity _∼₁_ _∼₂_ ⦄
    ⦃ _ : 𝓡eflexivity _∼₁_ ⦄
    ⦃ _ : 𝓡eflexivity _∼₂_ ⦄
    where
    open Visible6 {surjection} _∼₁_ _∼₂_ _∼̇₂_ surjectivity ε ε
    𝓼urjidentity = 𝓈urjidentity'
    𝓢urjidentity = Surjidentity
  module SubStandard
    (_∼₁_ : 𝔒₁ → 𝔒₁ → Ø 𝔯₁)
    {_∼₂_ : 𝔒₂ → 𝔒₂ → Ø 𝔯₂}
    (_∼̇₂_ : ∀ {x y} → x ∼₂ y → x ∼₂ y → Ø ℓ₂)
    ⦃ _ : 𝓢urjection 𝔒₁ 𝔒₂ ⦄
    ⦃ _ : 𝒮urjectivity _∼₁_ _∼₂_ ⦄
    ⦃ _ : 𝓡eflexivity _∼₁_ ⦄
    ⦃ _ : 𝓡eflexivity _∼₂_ ⦄
    where
    open Visible6 {surjection} _∼₁_ _∼₂_ _∼̇₂_ surjectivity ε ε
    surjidentity[_,_] = surjidentityV6

open Visible6 public
open Hidden public
open Standard public
open SubStandard public
