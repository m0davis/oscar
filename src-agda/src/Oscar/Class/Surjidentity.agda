
open import Oscar.Prelude
open import Oscar.Class
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
  module _
    {μ : Surjection.type 𝔒₁ 𝔒₂}
    (_∼₁_ : 𝔒₁ → 𝔒₁ → Ø 𝔯₁)
    (_∼₂_ : 𝔒₂ → 𝔒₂ → Ø 𝔯₂)
    (_∼̇₂_ : ∀ {x y} → x ∼₂ y → x ∼₂ y → Ø ℓ₂)
    (§ : 𝒮urjectivity _∼₁_ _∼₂_ μ)
    (ε₁ : 𝓻eflexivity _∼₁_)
    (ε₂ : 𝓻eflexivity _∼₂_)
    where
    𝔰urjidentity : ℭlass $ (λ {x} {y} → § {x} {y}) , (λ {x} → ε₁ {x}) , (λ {x y} → _∼̇₂_ {x} {y}) , (λ {x} → ε₂ {x})
    𝔰urjidentity = ∁ ∀ {x} → § (ε₁ {x}) ∼̇₂ ε₂
    open ℭlass 𝔰urjidentity using () renaming (GET-CLASS to Surjidentity; SET-METHOD to 𝓼urjidentity') public
  module _
    {μ : Surjection.type 𝔒₁ 𝔒₂}
    {_∼₁_ : 𝔒₁ → 𝔒₁ → Ø 𝔯₁}
    {_∼₂_ : 𝔒₂ → 𝔒₂ → Ø 𝔯₂}
    {_∼̇₂_ : ∀ {x y} → x ∼₂ y → x ∼₂ y → Ø ℓ₂}
    {§ : 𝒮urjectivity _∼₁_ _∼₂_ μ}
    {ε₁ : 𝓻eflexivity _∼₁_}
    {ε₂ : 𝓻eflexivity _∼₂_}
    where
    open ℭlass (𝔰urjidentity {μ} _∼₁_ _∼₂_ _∼̇₂_ § ε₁ ε₂) using () renaming (GET-METHOD to surjidentity) public
  module _
    (_∼₁_ : 𝔒₁ → 𝔒₁ → Ø 𝔯₁)
    (_∼₂_ : 𝔒₂ → 𝔒₂ → Ø 𝔯₂)
    (_∼̇₂_ : ∀ {x y} → x ∼₂ y → x ∼₂ y → Ø ℓ₂)
    ⦃ _ : Surjection.class 𝔒₁ 𝔒₂ ⦄
    ⦃ _ : 𝒮urjectivity! _∼₁_ _∼₂_ ⦄
    ⦃ _ : 𝓡eflexivity _∼₁_ ⦄
    ⦃ _ : 𝓡eflexivity _∼₂_ ⦄
    where
    open ℭlass (𝔰urjidentity {surjection} _∼₁_ _∼₂_ _∼̇₂_ § ε ε) using () renaming (GET-CLASS to 𝓢urjidentity; SET-METHOD to 𝓼urjidentity) public
  module _
    (_∼₁_ : 𝔒₁ → 𝔒₁ → Ø 𝔯₁)
    {_∼₂_ : 𝔒₂ → 𝔒₂ → Ø 𝔯₂}
    (_∼̇₂_ : ∀ {x y} → x ∼₂ y → x ∼₂ y → Ø ℓ₂)
    ⦃ _ : Surjection.class 𝔒₁ 𝔒₂ ⦄
    ⦃ _ : 𝒮urjectivity! _∼₁_ _∼₂_ ⦄
    ⦃ _ : 𝓡eflexivity _∼₁_ ⦄
    ⦃ _ : 𝓡eflexivity _∼₂_ ⦄
    where
    open ℭlass (𝔰urjidentity {surjection} _∼₁_ _∼₂_ _∼̇₂_ § ε ε) using () renaming (GET-METHOD to surjidentity[_,_]) public
