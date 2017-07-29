
open import Oscar.Prelude
open import Oscar.Class.Surjection
open import Oscar.Class.Surjectivity
open import Oscar.Class.Reflexivity
open import Oscar.Class.Surjidentity

module Test.SurjidentityP where

module _
    {𝔬₁} {𝔒₁ : Ø 𝔬₁}
    {𝔯₁} (_∼₁_ : 𝔒₁ → 𝔒₁ → Ø 𝔯₁)
    {𝔬₂} {𝔒₂ : Ø 𝔬₂}
    {𝔯₂} (_∼₂_ : 𝔒₂ → 𝔒₂ → Ø 𝔯₂)
         (_∼₂2_ : 𝔒₂ → 𝔒₂ → Ø 𝔯₂)
    {𝔯₂'} (_∼₂'_ : 𝔒₂ → 𝔒₂ → Ø 𝔯₂')
    {ℓ₂} (_∼̇₂_ : ∀ {x y} → x ∼₂ y → x ∼₂ y → Ø ℓ₂)
         (_∼̇₂'_ : ∀ {x y} → x ∼₂' y → x ∼₂' y → Ø ℓ₂)
         (_∼̇₂2_ : ∀ {x y} → x ∼₂2 y → x ∼₂2 y → Ø ℓ₂)
    ⦃ _ : 𝓢urjection 𝔒₁ 𝔒₂ ⦄
    ⦃ _ : [𝓢urjectivity] _∼₁_ _∼₂_ ⦄
    ⦃ _ : [𝓢urjectivity] _∼₁_ _∼₂'_                      ⦄
    ⦃ _ : [𝓢urjectivity] _∼₁_ _∼₂2_                      ⦄
    ⦃ _ : 𝓢urjectivity _∼₁_ _∼₂_                         ⦄
    ⦃ _ : 𝓢urjectivity _∼₁_ _∼₂'_                        ⦄
    ⦃ _ : 𝓢urjectivity _∼₁_ _∼₂2_                        ⦄
    ⦃ _ : 𝓡eflexivity _∼₁_                               ⦄
    ⦃ _ : 𝓡eflexivity _∼₂_                               ⦄
    ⦃ _ : 𝓡eflexivity _∼₂'_                                ⦄
    ⦃ _ : 𝓡eflexivity _∼₂2_                                ⦄
    ⦃ _ : [𝓢urjidentity] _∼₁_ _∼₂_ _∼̇₂_ 𝔯₁ 𝔬₂ 𝔯₂           ⦄
    ⦃ _ : [𝓢urjidentity] _∼₁_ _∼₂'_ _∼̇₂'_ 𝔯₁ 𝔬₂ 𝔯₂'       ⦄
    ⦃ _ : [𝓢urjidentity] _∼₁_ _∼₂2_ _∼̇₂2_ 𝔯₁ 𝔬₂ 𝔯₂        ⦄
    ⦃ _ : 𝓢urjidentity _∼₁_ _∼₂_ _∼̇₂_                        ⦄
    ⦃ _ : 𝓢urjidentity _∼₁_ _∼₂'_ _∼̇₂'_                     ⦄
    ⦃ _ : 𝓢urjidentity _∼₁_ _∼₂2_ _∼̇₂2_                     ⦄
    where

  test-surj : 𝓼urjidentity _∼₁_ _∼₂_ _∼̇₂_
  test-surj = surjidentity

  test-surj[] : 𝓼urjidentity _∼₁_ _∼₂_ _∼̇₂_
  test-surj[] = surjidentity[ _∼₁_ , _∼̇₂_ ]
