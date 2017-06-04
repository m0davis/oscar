
module Oscar where

open import Oscar.Prelude
open import Oscar.Class
open import Oscar.Data


test-transassociativity-≡ : ∀
  {𝔬} {𝔒 : Ø 𝔬}
  {𝔯} {_∼_ : 𝔒 → 𝔒 → Ø 𝔯}
  ⦃ _ : [𝓣ransassociativity] _∼_ Proposequality ⦄
  ⦃ _ : 𝓣ransitivity _∼_ ⦄
  ⦃ _ : 𝓣ransassociativity _∼_ Proposequality ⦄
  → ∀ {w x y z} (f : w ∼ x) (g : x ∼ y) (h : y ∼ z) → (h ∙ g) ∙ f ≡ h ∙ g ∙ f
test-transassociativity-≡ f g h rewrite transassociativity {_∼̇_ = Proposequality} f g h = ∅ -- transassociativity


module Test-Surjidentity
  {𝔬₁ 𝔯₁ 𝔬₂ 𝔯₂ ℓ₂}
  {𝔒₁ : Ø 𝔬₁}
  (_∼₁_ : 𝔒₁ → 𝔒₁ → Ø 𝔯₁)
  {𝔒₂ : Ø 𝔬₂}
  (_∼₂_ : 𝔒₂ → 𝔒₂ → Ø 𝔯₂)
  (_∼₂'_ : 𝔒₂ → 𝔒₂ → Ø 𝔯₂)
  (_∼̇₂_ : ∀ {x y} → x ∼₂ y → x ∼₂ y → Ø ℓ₂)
  (_∼̇₂'_ : ∀ {x y} → x ∼₂' y → x ∼₂' y → Ø ℓ₂)
  ⦃ `𝓢urjection : 𝓢urjection 𝔒₁ 𝔒₂ ⦄
  ⦃ `[𝓢urjectivity] : [𝓢urjectivity] _∼₁_ _∼₂_ ⦄
  ⦃ `[𝓢urjectivity]' : [𝓢urjectivity] _∼₁_ _∼₂'_ ⦄
  ⦃ `𝓢urjectivity : 𝓢urjectivity _∼₁_ _∼₂_ ⦄
  ⦃ `𝓢urjectivity' : 𝓢urjectivity _∼₁_ _∼₂'_ ⦄
  ⦃ `𝓡eflexivity₁ : 𝓡eflexivity _∼₁_ ⦄
  ⦃ `𝓡eflexivity₂ : 𝓡eflexivity _∼₂_ ⦄
  ⦃ `𝓡eflexivity₂' : 𝓡eflexivity _∼₂'_ ⦄
  where
  instance

    `[𝒮urjidentity] : [𝓢urjidentity] _∼₁_ _∼₂_ _∼̇₂_ 𝔯₁ 𝔬₂ 𝔯₂
    `[𝒮urjidentity] = ∁ _∼₁_ _∼₂_ _∼̇₂_

  instance

    `𝒮urjidentity : 𝓢urjidentity _∼₁_ _∼₂_ _∼̇₂_
    `𝒮urjidentity .𝒮urjidentity.surjidentity = magic

  test-surjidentity : 𝓼urjidentity _∼₁_ _∼₂_ _∼̇₂_
  test-surjidentity = surjidentity

module TestSurjidentityI
    {𝔬₁} {𝔒₁ : Ø 𝔬₁}
    {𝔯₁} (_∼₁_ : 𝔒₁ → 𝔒₁ → Ø 𝔯₁)
    {𝔬₂} {𝔒₂ : Ø 𝔬₂}
    {𝔯₂} (_∼₂_ : 𝔒₂ → 𝔒₂ → Ø 𝔯₂)
         (_∼₂2_ : 𝔒₂ → 𝔒₂ → Ø 𝔯₂)
    {𝔯₂'} (_∼₂'_ : 𝔒₂ → 𝔒₂ → Ø 𝔯₂')
    {ℓ₂} (_∼̇₂_ : ∀ {x y} → x ∼₂ y → x ∼₂ y → Ø ℓ₂)
         (_∼̇₂'_ : ∀ {x y} → x ∼₂' y → x ∼₂' y → Ø ℓ₂)
         (_∼̇₂2_ : ∀ {x y} → x ∼₂2 y → x ∼₂2 y → Ø ℓ₂)
  where
  postulate
    instance `𝓢urjection : 𝓢urjection 𝔒₁ 𝔒₂
    instance `[𝓢urjectivity] : [𝓢urjectivity] _∼₁_ _∼₂_
    instance `[𝓢urjectivity]' : [𝓢urjectivity] _∼₁_ _∼₂'_
    instance `[𝓢urjectivity]2 : [𝓢urjectivity] _∼₁_ _∼₂2_
    instance `𝓢urjectivity : 𝓢urjectivity _∼₁_ _∼₂_
    instance `𝓢urjectivity' : 𝓢urjectivity _∼₁_ _∼₂'_
    instance `𝓢urjectivity2 : 𝓢urjectivity _∼₁_ _∼₂2_
    instance `𝓡eflexivity₁ : 𝓡eflexivity _∼₁_
    instance `𝓡eflexivity₂ : 𝓡eflexivity _∼₂_
    instance `𝓡eflexivity₂' : 𝓡eflexivity _∼₂'_
    instance `𝓡eflexivity₂2 : 𝓡eflexivity _∼₂2_
    instance `[𝒮urjidentity] : [𝓢urjidentity] _∼₁_ _∼₂_ _∼̇₂_ 𝔯₁ 𝔬₂ 𝔯₂
    instance `[𝒮urjidentity]' : [𝓢urjidentity] _∼₁_ _∼₂'_ _∼̇₂'_ 𝔯₁ 𝔬₂ 𝔯₂'
    instance `[𝒮urjidentity]2 : [𝓢urjidentity] _∼₁_ _∼₂2_ _∼̇₂2_ 𝔯₁ 𝔬₂ 𝔯₂
    instance `𝒮urjidentity : 𝓢urjidentity _∼₁_ _∼₂_ _∼̇₂_
    instance `𝒮urjidentity' : 𝓢urjidentity _∼₁_ _∼₂'_ _∼̇₂'_
    instance `𝒮urjidentity2 : 𝓢urjidentity _∼₁_ _∼₂2_ _∼̇₂2_

  test-surj : 𝓼urjidentity _∼₁_ _∼₂_ _∼̇₂_
  test-surj = surjidentity

module TestSurjidentityP
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

module Test0 where

  test-functor-surjidentity : ∀
    {𝔬₁ 𝔯₁ ℓ₁ 𝔬₂ 𝔯₂ ℓ₂}
    ⦃ functor : Functor 𝔬₁ 𝔯₁ ℓ₁ 𝔬₂ 𝔯₂ ℓ₂ ⦄
    (open Functor functor)
    → 𝓼urjidentity _∼₁_ _∼₂_ _∼̇₂_
  test-functor-surjidentity = surjidentity

  -- test-functor-transextensionality ⦃ functor ⦄ = let open Functor ⦃ … ⦄ in transextensionality1

module Test1 where

  test-functor-transextensionality : ∀
    {𝔬₁ 𝔯₁ ℓ₁ 𝔬₂ 𝔯₂ ℓ₂}
    ⦃ functor : Functor 𝔬₁ 𝔯₁ ℓ₁ 𝔬₂ 𝔯₂ ℓ₂ ⦄
    (open Functor functor)
    → 𝓽ransextensionality _∼₁_ _∼̇₁_
  test-functor-transextensionality = transextensionality
  -- test-functor-transextensionality ⦃ functor ⦄ = let open Functor ⦃ … ⦄ in transextensionality1

module Test2 where

  test-functor-transextensionality : ∀
    {𝔬₁} {𝔒₁ : Ø 𝔬₁}
    {𝔯₁} {_∼₁_ : 𝔒₁ → 𝔒₁ → Ø 𝔯₁}
    {ℓ₁} {_∼̇₁_ : ∀ {x y} → x ∼₁ y → x ∼₁ y → Ø ℓ₁}
    {𝔬₂} {𝔒₂ : Ø 𝔬₂}
    {𝔯₂} {_∼₂_ : 𝔒₂ → 𝔒₂ → Ø 𝔯₂}
    {ℓ₂} {_∼̇₂_ : ∀ {x y} → x ∼₂ y → x ∼₂ y → Ø ℓ₂}
    ⦃ _ : IsFunctor _∼₁_ _∼̇₁_ _∼₂_ _∼̇₂_ ⦄
    ⦃ _ : IsFunctor _∼₁_ _∼̇₁_ _∼₂_ _∼̇₂_ ⦄
    → 𝓽ransextensionality _∼₁_ _∼̇₁_
  test-functor-transextensionality = transextensionality

module Test3 where

  module _
    {𝔬₁ 𝔯₁ ℓ₁ 𝔬₂ 𝔯₂ ℓ₂}
    where
    postulate instance functor : Functor 𝔬₁ 𝔯₁ ℓ₁ 𝔬₂ 𝔯₂ ℓ₂
    open Functor ⦃ … ⦄
    test : asInstance `IsFunctor $ 𝓽ransextensionality _∼₁_ _∼̇₁_
    test = asInstance `IsFunctor transextensionality
    -- -- Test1.test-functor-transextensionality


{-
module _ where

  record Injection
    {𝔬₁} (𝔒₁ : Ø 𝔬₁)
    {𝔬₂} (𝔒₂ : Ø 𝔬₂)
    : Ø 𝔬₁ ∙̂ 𝔬₂ where
    field
      injection : 𝔒₁ → 𝔒₂

  open Injection ⦃ … ⦄ public

  record Injectivity
    {𝔬₁} {𝔒₁ : Ø 𝔬₁}
    {𝔬₂} {𝔒₂ : Ø 𝔬₂}
    ⦃ _ : Injection 𝔒₁ 𝔒₂ ⦄
    {ℓ₂} (_∼₂_ : 𝔒₂ → 𝔒₂ → Ø ℓ₂)
    {ℓ₁} (_∼₁_ : 𝔒₁ → 𝔒₁ → Ø ℓ₁)
    : Ø 𝔬₁ ∙̂ 𝔬₂ ∙̂ ℓ₂ ∙̂ ℓ₁ where
    field
      injectivity : ∀ {x₁ x₂} → injection x₁ ∼₂ injection x₂ → x₁ ∼₁ x₂

  open Injectivity ⦃ … ⦄ public

{-
  test-injectivity''' : ∀
    {𝔬₁} {𝔒₁ : Ø 𝔬₁}
    {𝔬₂} {𝔒₂ : Ø 𝔬₂}
    ⦃ _ : Injection 𝔒₁ 𝔒₂ ⦄
    {ℓ₂} {_∼₂_ : 𝔒₂ → 𝔒₂ → Ø ℓ₂}
    {ℓ₁} {_∼₁_ : 𝔒₁ → 𝔒₁ → Ø ℓ₁}
    ⦃ _ : Injectivity _∼₂_ _∼₁_ ⦄
    → ∀ {x₁ x₂} → injection x₁ ∼₂ injection x₂ → x₁ ∼₁ x₂
  test-injectivity''' = injectivity
-}

  injectivity⟦_⟧ : ∀
    {𝔬₁} {𝔒₁ : Ø 𝔬₁}
    {𝔬₂} {𝔒₂ : Ø 𝔬₂}
    ⦃ _ : Injection 𝔒₁ 𝔒₂ ⦄
    (`injection : 𝔒₁ → 𝔒₂)
    {ℓ₂} {_∼₂_ : 𝔒₂ → 𝔒₂ → Ø ℓ₂}
    {ℓ₁} {_∼₁_ : 𝔒₁ → 𝔒₁ → Ø ℓ₁}
    ⦃ _ : Injectivity _∼₂_ _∼₁_ ⦄
    ⦃ _ : `injection ≡ injection ⦄
    → ∀ {x₁ x₂} → injection x₁ ∼₂ injection x₂ → x₁ ∼₁ x₂
  injectivity⟦ injection ⟧ {_∼₂_ = _∼₂_} {_∼₁_ = _∼₁_} = injectivity {_∼₂_ = _∼₂_} {_∼₁_ = _∼₁_}

  test-injectivity' : ∀
    {𝔬₁} {𝔒₁ : Ø 𝔬₁}
    {𝔬₂} {𝔒₂ : Ø 𝔬₂}
    ⦃ _ : Injection 𝔒₁ 𝔒₂ ⦄
    {ℓ₂} {_∼₂_ : 𝔒₂ → 𝔒₂ → Ø ℓ₂}
    {ℓ₁} {_∼₁_ : 𝔒₁ → 𝔒₁ → Ø ℓ₁}
    ⦃ _ : Injectivity _∼₂_ _∼₁_ ⦄
    → ∀ {x₁ x₂} → injection x₁ ∼₂ injection x₂ → x₁ ∼₁ x₂
  test-injectivity' {_∼₂_ = _∼₂_} {_∼₁_ = _∼₁_} = injectivity⟦ injection ⟧ {_∼₂_ = _∼₂_} {_∼₁_ = _∼₁_}
-}

-- ⦃ r = inj ⦄
{-
  ≡-injectivity⟦_⟧ : ∀
    {𝔬₁} {𝔒₁ : Ø 𝔬₁}
    {𝔬₂} {𝔒₂ : Ø 𝔬₂}
    (injection : 𝔒₁ → 𝔒₂)
    ⦃ _ : Injectivity injection _≡_ _≡_ ⦄
    → ∀ {x₁ x₂} → injection x₁ ≡ injection x₂ → x₁ ≡ x₂
  ≡-injectivity⟦ injection ⟧ = injectivity { injection = injection }
-}

{-

  ≡-injectivity₂,₀,₁ : ∀
    {𝔬₁} {𝔒₁ : Ø 𝔬₁}
    {𝔬₂} {𝔒₂ : 𝔒₁ → Ø 𝔬₂}
    {𝔬₃} {𝔒₃ : Ø 𝔬₃}
    ⦃ _ : 𝓘njection₂ {𝔒₂ = 𝔒₂} (λ _ _ → 𝔒₃) ⦄
    ⦃ _ : [𝓘njectivity₂,₀,₁] {𝔒₂ = 𝔒₂} (λ _ _ → 𝔒₃) Proposequality Proposequality ⦄
    ⦃ _ : 𝓘njectivity₂,₀,₁ {𝔒₂ = 𝔒₂} (λ _ _ → 𝔒₃) Proposequality Proposequality ⦄
    → 𝓲njectivity₂,₀,₁ {𝔒₂ = 𝔒₂} (λ _ _ → 𝔒₃) Proposequality Proposequality
  ≡-injectivity₂,₀,₁ = injectivity₂,₀,₁
-}

{-

  module _ -- Arity=2
    {𝔬} {𝔒 : Ø 𝔬}
    {𝔭₁} (𝔓₁ : 𝔒 → Ø 𝔭₁)
    {𝔭₂} (𝔓₂ : 𝔒 → Ø 𝔭₂)
    where
    𝓲njection₁̇ = ∀ {x} → 𝔓₁ x → 𝔓₂ x
    record 𝓘njection₁̇ : Ø 𝔬 ∙̂ 𝔭₁ ∙̂ 𝔭₂ where
      constructor ∁
      field injection₁̇ : 𝓲njection₁̇
    open 𝓘njection₁̇ ⦃ … ⦄ public
    module _ -- Fixed=1
      {ℓ₁} (_∼₁_ : ∀ {x} → 𝔓₁ x → 𝔓₁ x → Ø ℓ₁)
      {ℓ₂} (_∼₂_ : ∀ {x} → 𝔓₂ x → 𝔓₂ x → Ø ℓ₂)
      where
      record [𝓘njectivity₁̇] : Ø₀ where
        no-eta-equality
        constructor ∁
      module _
        ⦃ _ : 𝓘njection₁̇ ⦄
        where
        𝓲njectivity₁̇ = ∀ {x : 𝔒} {y₁ y₂ : 𝔓₁ x} → injection₁̇ y₁ ∼₂ injection₁̇ y₂ → y₁ ∼₁ y₂
        record 𝓘njectivity₁̇ ⦃ _ : [𝓘njectivity₁̇] ⦄ : Ø 𝔬 ∙̂ 𝔭₁ ∙̂ 𝔭₂ ∙̂ ℓ₁ ∙̂ ℓ₂ where field injectivity₁̇ : 𝓲njectivity₁̇
        open 𝓘njectivity₁̇ ⦃ … ⦄ public
-}

{-

{-
    module _ -- Fixed=1
      {ℓ₃} (_∼₃_ : ∀ {x} {y₁ y₂ : 𝔒₂ x} → 𝔒₃ _ y₁ → 𝔒₃ _ y₂ → Ø ℓ₃)
      {ℓ₂} (_∼₂_ : ∀ {x} → 𝔒₂ x → 𝔒₂ x → Ø ℓ₂)
      where
      record [𝓘njectivity₃,₁] : Ø₀ where
        no-eta-equality
        constructor ∁
      module _
        ⦃ _ : 𝓘njection₂ ⦄
        where
        𝓲njectivity₃,₁ = ∀ {x₁ x₂ : 𝔒₁} {y₁ : 𝔒₂ x₁} {y₂ : 𝔒₂ x₂} → injection₂ _ y₁ ∼₄ injection₂ _ y₂ → y₁ ∼₂ y₂
        record 𝓘njectivity₃,₁ ⦃ _ : [𝓘njectivity₃,₁] ⦄ : Ø 𝔬₁ ∙̂ 𝔬₂ ∙̂ 𝔬₃ ∙̂ ℓ₂ ∙̂ ℓ₃ where field injectivity₂,₁ : 𝓲njectivity₂,₁
        open 𝓘njectivity₃,₁ ⦃ … ⦄ public
-}

{-
    module _ -- Fixed=1/Proposequality
      {ℓ₃} (_∼₃_ : ∀ {x} {y₁ y₂ : 𝔒₂ x} → 𝔒₃ _ y₁ → 𝔒₃ _ y₂ → Ø ℓ₃)
      where
      record [≡-𝓘njectivity₂,₁] : Ø₀ where
        no-eta-equality
        constructor ∁
      where
      module _
        ⦃ _ : 𝓘njection₂ ⦄
        where
        ≡-𝓲njectivity₂,₁ = 𝓲njectivity₂,₁ Proposequality _∼₃_
        record ≡-𝓘njectivity₂,₁ : Ø 𝔬₁ ∙̂ 𝔬₂ ∙̂ 𝔬₃ ∙̂ ℓ₂ where
          field
            ⦃ `[𝓘njectivity₂,₁] ⦄ : [𝓘njectivity₂,₁] Proposequality _∼₃_
            ⦃ `𝓘njectivity₂,₁ ⦄ : 𝓘njectivity₂,₁ Proposequality _∼₃_
-}

  injectivity₂,₁′ : ∀
    {𝔬₁} {𝔒₁ : Ø 𝔬₁}
    {𝔬₂} {𝔒₂ : Ø 𝔬₂}
    {𝔬₃} {𝔒₃ : 𝔒₁ → 𝔒₂ → Ø 𝔬₃}
    {ℓ₃} {_∼₃_ : ∀ {x} {y₁ y₂ : 𝔒₂} → 𝔒₃ x y₁ → 𝔒₃ x y₂ → Ø ℓ₃}
    {ℓ₂} {_∼₂_ : 𝔒₂ → 𝔒₂ → Ø ℓ₂}
    ⦃ _ : 𝓘njection₂ 𝔒₃ ⦄
    ⦃ _ : [𝓘njectivity₂,₁] 𝔒₃  _∼₃_ _∼₂_ ⦄
    ⦃ _ : 𝓘njectivity₂,₁ 𝔒₃ _∼₃_ _∼₂_ ⦄
    → ∀ {y₁ y₂ : 𝔒₂} (x : 𝔒₁) → injection₂ x y₁ ∼₃ injection₂ x y₂ → y₁ ∼₂ y₂
  injectivity₂,₁′ x = injectivity₂,₁ x

-}

{-

          `𝓘njection₁̇ : 𝓘njection₁̇ 𝔓 (𝔓 ∘ ⇑₀)
          `𝓘njection₁̇ .𝓘njection₁̇.injection₁̇ = successor₁

-}

{-

  module _
    {𝔬₁} {𝔒₁ : Ø 𝔬₁}
    {𝔬₂} {𝔒₂ : 𝔒₁ → Ø 𝔬₂}
    {ℓ₁} (_∼₁_ : (x : 𝔒₁) → 𝔒₂ x → Ø ℓ₁)
    {ℓ₂} (_∼₂_ : (x : 𝔒₁) → 𝔒₂ x → Ø ℓ₂)
    where
    𝓶ap' = ∀ {x y} → x ∼₁ y → x ∼₂ y
    record 𝓜ap' : Ø 𝔬₁ ∙̂ 𝔬₂ ∙̂ ℓ₁ ∙̂ ℓ₂ where field map' : 𝓶ap'
  open 𝓜ap' ⦃ … ⦄ public
-}

{-

    -- 𝓢urjectionMaybe : ∀ {𝔬} {𝔒 : Ø 𝔬} → 𝓢urjection 𝔒 (Maybe 𝔒)
    -- 𝓢urjectionMaybe .𝓢urjection.surjection = ↑_

    𝓜apMaybe : ∀ {𝔬₁} → 𝓜ap {𝔒₁ = Ø 𝔬₁} (λ x y → x → y) (λ x y → Maybe x → Maybe y)
    𝓜apMaybe .𝓜ap.map f ∅ = ∅
    𝓜apMaybe .𝓜ap.map f (↑ x) = ↑ f x

-}

{-

    [𝓘njectivity₁̇]Fin : [𝓘njectivity₁̇] Fin (Fin ∘ ⇑₀) Proposequality Proposequality
    [𝓘njectivity₁̇]Fin = ∁

    𝓘njectivity₁̇Fin : 𝓘njectivity₁̇ Fin (Fin ∘ ⇑₀) Proposequality Proposequality
    𝓘njectivity₁̇Fin .𝓘njectivity₁̇.injectivity₁̇ ∅ = ∅

-}
