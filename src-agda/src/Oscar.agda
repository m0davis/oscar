
module Oscar where

open import Oscar.Prelude
open import Oscar.Class
open import Oscar.Data
open import Oscar.Property


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
  ⦃ `𝓢urjectextensivity : 𝓢urjectivity _∼₁_ _∼₂'_ ⦄
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
    instance `𝓢urjectextensivity : 𝓢urjectivity _∼₁_ _∼₂'_
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

module Test3 (_ : Ø₀) where

  module _
    {𝔬₁ 𝔯₁ ℓ₁ 𝔬₂ 𝔯₂ ℓ₂}
    where
    postulate instance functor : Functor 𝔬₁ 𝔯₁ ℓ₁ 𝔬₂ 𝔯₂ ℓ₂
    open Functor ⦃ … ⦄
    test : asInstance `IsFunctor $ 𝓽ransextensionality _∼₁_ _∼̇₁_
    test = asInstance `IsFunctor transextensionality
    -- -- Test1.test-functor-transextensionality

module Test4
  {𝔵} {𝔛 : Ø 𝔵}
  {𝔞} {𝔒₁ : 𝔛 → Ø 𝔞}
  {𝔟} {𝔒₂ : 𝔛 → Ø 𝔟}
  {ℓ : Ł}
  ⦃ _ : 𝓣ransitivity (Arrow 𝔒₁ 𝔒₂) ⦄
  -- ⦃ _ : [𝓢urjectivity] (Arrow 𝔒₁ 𝔒₂) (Extension $ ArrowṖroperty ℓ 𝔒₁ 𝔒₂) ⦄
  where
  test[∙] : ∀ {x y} → ArrowṖroperty ℓ 𝔒₁ 𝔒₂ x → Arrow 𝔒₁ 𝔒₂ x y → ArrowṖroperty ℓ 𝔒₁ 𝔒₂ y
  test[∙] P f .π₀ g = (f ◃ P) .π₀ g


module Test5
  {𝔵} {𝔛 : Ø 𝔵}
  {𝔞} {𝔒₁ : 𝔛 → Ø 𝔞}
  {𝔟} {𝔒₂ : 𝔛 → Ø 𝔟}
  {ℓ}
  {ℓ̇} (_↦_ : ∀ {x} → 𝔒₂ x → 𝔒₂ x → Ø ℓ̇)
  ⦃ _ : [ExtensibleType] _↦_ ⦄
  ⦃ _ : [𝓢urjectivity] (Arrow 𝔒₁ 𝔒₂) (Extension 𝔒₂) ⦄
  ⦃ _ : 𝓢urjectivity (Arrow 𝔒₁ 𝔒₂) (Extension 𝔒₂) ⦄
  ⦃ _ : [𝓢urjextensionality] (Arrow 𝔒₁ 𝔒₂) (Pointwise _↦_) (Extension 𝔒₂) (Pointwise _↦_) ⦄
  ⦃ _ : 𝓢urjextensionality (Arrow 𝔒₁ 𝔒₂) (Pointwise _↦_) (Extension 𝔒₂) (Pointwise _↦_) ⦄
  ⦃ _ : [𝓢urjectivity] (Arrow 𝔒₁ 𝔒₂) (Extension $ ArrowExtensionṖroperty ℓ 𝔒₁ 𝔒₂ _↦_) ⦄
  where
  test[∙] : ∀ {x y} → ArrowExtensionṖroperty ℓ 𝔒₁ 𝔒₂ _↦_ x → Arrow 𝔒₁ 𝔒₂ x y → ArrowExtensionṖroperty ℓ 𝔒₁ 𝔒₂ _↦_ y
  test[∙] P f = f ◃ P

module Test7 where

  𝓅rop-id : ∀
    {𝔵} {𝔛 : Ø 𝔵}
    {𝔞} {𝔄 : 𝔛 → Ø 𝔞}
    {𝔟} {𝔅 : 𝔛 → Ø 𝔟}
    (let _∼_ = Arrow 𝔄 𝔅)
    {ℓ̇} {_∼̇_ : ∀ {x y} → x ∼ y → x ∼ y → Ø ℓ̇}
    ⦃ _ : 𝓣ransitivity _∼_ ⦄
    ⦃ _ : 𝓡eflexivity _∼_ ⦄
    ⦃ _ : [𝓣ransleftidentity] _∼_ _∼̇_ ⦄
    ⦃ _ : 𝓣ransleftidentity _∼_ _∼̇_ ⦄
    ⦃ _ : ∀ {x y} → 𝓢ymmetry (_∼̇_ {x} {y}) ⦄
    {m n}
    {ℓ} {f : m ∼ n} (P : ExtensionṖroperty ℓ (Arrow 𝔄 𝔅 m) _∼̇_) (let P₀ = π₀ (π₀ P))
    → P₀ f
    → P₀ (ε ∙ f)
  𝓅rop-id = prop-id

module Test8 where
  ≡-ExtensionṖroperty : ∀
    {𝔵} {𝔛 : Ø 𝔵}
    {𝔬₁} ℓ (𝔒₁ : 𝔛 → Ø 𝔬₁)
    {𝔬₂} (𝔒₂ : 𝔛 → Ø 𝔬₂)
    → 𝔛
    → Ø 𝔵 ∙̂ 𝔬₁ ∙̂ 𝔬₂ ∙̂ ↑̂ ℓ
  ≡-ExtensionṖroperty ℓ 𝔒₁ 𝔒₂ x = ArrowExtensionṖroperty ℓ 𝔒₁ 𝔒₂ _≡_ x

  postulate 𝔓 : Set
  postulate ℓ : Ł
  open Term 𝔓
  open Substitunction 𝔓

  test-epfs : ∀ {x y} → ExtensionṖroperty ℓ (Arrow Fin Term x) (Pointwise Proposequality) → Arrow Fin Term x y → ArrowExtensionṖroperty ℓ Fin Term _≡_ y
  test-epfs P f = f ◃ P

  test-epfs⋆ : ∀ {x y} → ArrowṖroperty ℓ Fin Term x → Substitunction x y → ArrowṖroperty ℓ Fin Term y
  test-epfs⋆ P f = f ◃ P

  test-epfs2 : ∀ {x y} → ≡-ExtensionṖroperty ℓ Fin Term x → Arrow Fin Term x y → ≡-ExtensionṖroperty ℓ Fin Term y
  test-epfs2 P f = f ◃ P

  fact1⋆ : ∀ {m} (s t : Term m) → ≡-Unifies₀⟦ Substitunction ⟧ s t ≈ ≡-Unifies₀ t s
  fact1⋆ = symmetrical

  fact1 : ∀ {m} (s t : Term m) → ≡-ExtensionalUnifies {𝔄 = Fin} s t ≈ ≡-ExtensionalUnifies t s
  fact1 = symmetrical

  Properties-fact1'⋆ : ∀ {m} {s1 s2 t1 t2 : Term m}
         → ≡-Unifies₀⟦ Arrow Fin Term ⟧ (s1 fork s2) (t1 fork t2) ≈ ≡-Unifies₀ s1 t1 ∧ ≡-Unifies₀ s2 t2
  Properties-fact1'⋆ .π₀ = (λ s≡t → injectivity₂,₀,₁ s≡t , injectivity₂,₀,₂ s≡t) , uncurry (congruity₂ _fork_)

  Properties-fact1' : ∀ {m} {s1 s2 t1 t2 : Term m}
         → ≡-ExtensionalUnifies {𝔄 = Fin} (s1 fork s2) (t1 fork t2) ≈ ≡-ExtensionalUnifies s1 t1 ∧ ≡-ExtensionalUnifies s2 t2
  Properties-fact1' .π₀ .π₀ = (λ s≡t → injectivity₂,₀,₁ s≡t , injectivity₂,₀,₂ s≡t) , uncurry (congruity₂ _fork_)

  fact3⋆ : ∀ {m} {P : Ṗroperty ℓ (Arrow Fin Term m)} → P ≈ i ◃ P
  fact3⋆ .π₀ = ¡ , ¡

  fact3 : ∀ {m} {P : ExtensionṖroperty ℓ (Arrow Fin Term m) (Pointwise Proposequality)} → P ≈ i ◃ P
  fact3 .π₀ .π₀ = ¡ , ¡

  fact4⋆ : ∀{m n} (P : LeftṖroperty ℓ (Arrow Fin Term) m) (f : _ → Term n)
          → Nothing P → Nothing (f ◃ P)
  fact4⋆ _ _ nop = nop

  fact4 : ∀{m n} (P : LeftExtensionṖroperty ℓ (Arrow Fin Term) Proposextensequality m) (f : _ → Term n)
          → Nothing P → Nothing (f ◃ P)
  fact4 _ _ nop = nop

  fact5⋆ : ∀{m n} {P Q : ArrowṖroperty ℓ Fin Term m} (f : Arrow Fin Term m n) → P ≈ Q → (f ◃ P) ≈ (f ◃ Q)
  fact5⋆ = surjectextenscongruity

  fact5 : ∀{m n} {P Q : LeftExtensionṖroperty ℓ Substitunction Proposextensequality m} (f : Arrow Fin Term m n) → P ≈ Q
           → f ◃ P ≈ f ◃ Q
  fact5 = surjectextenscongruity

  fact6 : ∀{m n} (P : LeftExtensionṖroperty ℓ (Arrow Fin Term) _≈_ m) {f g : Arrow Fin Term m n} → f ≈ g → f ◃ P ≈ g ◃ P
  fact6 P f≐g .π₀ .π₀ {f = h} = π₁ P (congruity (surjectivity h) ∘ f≐g) , π₁ P (symmetry (congruity (surjectivity h) ∘ f≐g))

  left-identity-∧ : ∀ {m} (P : LeftṖroperty ℓ Substitunction m) → ➊ ∧ P ≈ P
  left-identity-∧ P .π₀ .π₀ (_ , π₃) = π₃
  left-identity-∧ P .π₀ .π₁ x = lift ∅ , x

  left-identity-∧-ext : ∀ {m} (P : LeftExtensionṖroperty ℓ Substitunction Proposextensequality m) → ➊ ∧ P ≈ P
  left-identity-∧-ext P .π₀ .π₀ = π₁ , (λ x → (lift ∅) , x)

module TestEquivalenceṖroperty
  {𝔵} {𝔛 : Ø 𝔵}
  {𝔬} {𝔒 : 𝔛 → Ø 𝔬}
  {ℓ : Ł}
  where

  test-sym-regular : {P Q : Ṗroperty ℓ 𝔒} → P ≈ Q → Q ≈ P
  test-sym-regular = symmetry

  test-trans-regular : {P Q R : Ṗroperty ℓ 𝔒} → P ≈ Q → Q ≈ R → P ≈ R
  test-trans-regular P≈Q Q≈R = transitivity P≈Q Q≈R

module TestEquivalenceExtensionṖroperty
  {𝔵} {𝔛 : Ø 𝔵}
  {𝔬} {𝔒 : 𝔛 → Ø 𝔬}
  {ℓ}
  {ℓ̇} {_↦_ : ∀ {x} → 𝔒 x → 𝔒 x → Ø ℓ̇}
  where

  test-sym-ext : {P Q : ExtensionṖroperty ℓ 𝔒 _↦_} → P ≈ Q → Q ≈ P
  test-sym-ext P≈Q = symmetry P≈Q

  test-trans-ext : {P Q R : ExtensionṖroperty ℓ 𝔒 _↦_} → P ≈ Q → Q ≈ R → P ≈ R
  test-trans-ext P≈Q Q≈R = transitivity P≈Q Q≈R

module TestSymmetrical where
  test-𝓢ymmetrical𝓢ymmetry : ∀
    {𝔬} {𝔒 : Ø 𝔬}
    {ℓ} {_∼_ : 𝔒 → 𝔒 → Ø ℓ}
    ⦃ _ : 𝓢ymmetry _∼_ ⦄
    → 𝓼ymmetry _∼_
  test-𝓢ymmetrical𝓢ymmetry = symmetrical _ _
