
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

module Test4
  {𝔵} {𝔛 : Ø 𝔵}
  {𝔞} {𝔒₁ : 𝔛 → Ø 𝔞}
  {𝔟} {𝔒₂ : 𝔛 → Ø 𝔟}
  {ℓ : Ł}
  ⦃ _ : 𝓣ransitivity (Arrow 𝔒₁ 𝔒₂) ⦄
  -- ⦃ _ : [𝓢urjectivity] (Arrow 𝔒₁ 𝔒₂) (Extension $ ArrowsourceProperty 𝔒₁ 𝔒₂ ℓ) ⦄
  where
  test[∙] : ∀ {x y} → ArrowsourceProperty 𝔒₁ 𝔒₂ ℓ x → Arrow 𝔒₁ 𝔒₂ x y → ArrowsourceProperty 𝔒₁ 𝔒₂ ℓ y
  test[∙] P f g = (f ◃ λ {_} → P) g


module Test5
  {𝔵} {𝔛 : Ø 𝔵}
  {𝔞} {𝔒₁ : 𝔛 → Ø 𝔞}
  {𝔟} {𝔒₂ : 𝔛 → Ø 𝔟}
  {ℓ}
  {ℓ̇} (_↦_ : ∀ {x} → 𝔒₂ x → 𝔒₂ x → Ø ℓ̇)
  ⦃ _ : [ExtensibleType] _↦_ ⦄
  ⦃ _ : [𝓢urjectivity] (Arrow 𝔒₁ 𝔒₂) (Extension 𝔒₂) ⦄
  ⦃ _ : 𝓢urjectivity (Arrow 𝔒₁ 𝔒₂) (Extension 𝔒₂) ⦄
  ⦃ _ : [𝓢urjextensionality] (Arrow 𝔒₁ 𝔒₂) (Extended _↦_) (Extension 𝔒₂) (Extended _↦_) ⦄
  ⦃ _ : 𝓢urjextensionality (Arrow 𝔒₁ 𝔒₂) (Extended _↦_) (Extension 𝔒₂) (Extended _↦_) ⦄
  ⦃ _ : [𝓢urjectivity] (Arrow 𝔒₁ 𝔒₂) (Extension $ λ v → ArrowsourceExtendedProperty 𝔒₁ 𝔒₂ ℓ v (Extended _↦_)) ⦄
  where
  test[∙] : ∀ {x y} → ArrowsourceExtendedProperty 𝔒₁ 𝔒₂ ℓ x (Extended _↦_) → Arrow 𝔒₁ 𝔒₂ x y → ArrowsourceExtendedProperty 𝔒₁ 𝔒₂ ℓ y (Extended _↦_)
  test[∙] P f = f ◃ P

module Test6 where
  postulate 𝔓 : Set
  postulate ℓ : Ł
  open Term 𝔓
  test-epfs : ∀ {x y} → ArrowsourceExtendedProperty Fin Term ℓ x (λ {y} → Extended Proposequality⟦ Term y ⟧) → Arrow Fin Term x y → ArrowsourceExtendedProperty Fin Term ℓ y (Extended _≡_)
  test-epfs P f = f ◃ P

  test-epfs' : ∀ {x y} → ArrowsourceProperty Fin Term ℓ x → Arrow Fin Term x y → ArrowsourceProperty Fin Term ℓ y
  test-epfs' P f = f ◃ (λ {_} → P)

  fact1U : ∀ {m} {s t : Term m} → (λ {d} → ≡-Unifies₀⟦ Arrow Fin Term ⟧ s t {d}) ⇔ ≡-Unifies₀ t s
  fact1U = symmetry , symmetry

  Properties-fact1 : ∀ {m} {s t : Term m} → (≡-ExtensionalUnifies {𝔄 = Fin} {𝔅 = Term} s t) ⇔ ≡-ExtensionalUnifies t s
  Properties-fact1 = symmetry , symmetry

  Properties-fact1'⋆ : ∀ {m} {s1 s2 t1 t2 : Term m}
         → (λ {m} → ≡-Unifies₀⟦ Arrow Fin Term ⟧ (s1 fork s2) (t1 fork t2) {m}) ⇔ ((λ {m} → ≡-Unifies₀ s1 t1 {m}) ∧ ≡-Unifies₀ s2 t2)
  Properties-fact1'⋆ = (λ s≡t → injectivity₂,₀,₁ s≡t , injectivity₂,₀,₂ s≡t) , uncurry (congruity₂ _fork_)

  Properties-fact1' : ∀ {m} {s1 s2 t1 t2 : Term m}
         → ≡-ExtensionalUnifies {𝔄 = Fin} {𝔅 = Term} (s1 fork s2) (t1 fork t2) ⇔ (≡-ExtensionalUnifies s1 t1 ∧ ≡-ExtensionalUnifies s2 t2)
  Properties-fact1' = (λ s≡t → injectivity₂,₀,₁ s≡t , injectivity₂,₀,₂ s≡t) , uncurry (congruity₂ _fork_)

  fact3 : ∀ {m} {P : ArrowsourceExtendedProperty Fin Term ℓ m (λ {y} → Extended Proposequality⟦ Term y ⟧)} → P ⇔ (i ◃ P)
  fact3 = ¡ , ¡

  fact4 : ∀{m n} {P : ArrowsourceExtendedProperty Fin Term ℓ m (λ {y} → Extended Proposequality⟦ Term y ⟧)} (f : _ → Term n)
          → Nothing P → Nothing (f ◃ P)
  fact4 f nop {f = g} Pf = nop {f = g ∙[ Arrow Fin Term ] f} Pf

  fact5⋆ : ∀{m n} {P Q : ArrowsourceProperty Fin Term ℓ m} {f : Arrow Fin Term m n} → (λ {x} → P {x}) ⇔ Q
           → (λ {w} → (f ◃ λ {_} → P) {w}) ⇔ (f ◃ λ {_} → Q)
  fact5⋆ P⇔Q = P⇔Q

  fact5 : ∀{m n} {P Q : ArrowsourceExtendedProperty Fin Term ℓ m (λ {y} → Extended Proposequality⟦ Term y ⟧)} {f : Arrow Fin Term m n} → P ⇔ Q
           → (f ◃ P) ⇔ (f ◃ Q)
  fact5 P⇔Q = P⇔Q

  fact6 : ∀{m n} (P : ArrowsourceExtendedProperty Fin Term ℓ m (λ {y} → Extended Proposequality⟦ Term y ⟧)) {f g : Arrow Fin Term m n} → f ≡̇ g → (f ◃ P) ⇔ (g ◃ P)
  fact6 P f≐g {f = h} = π₁ P (congruity (surjectivity h) ∘ f≐g) , π₁ P (symmetry (congruity (surjectivity h) ∘ f≐g))

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
    {ℓ} {f : m ∼ n} (P : ExtendedProperty (Arrow 𝔄 𝔅 m) ℓ _∼̇_) (let P₀ = π₀ P)
    → P₀ f
    → P₀ (ε ∙ f)
  𝓅rop-id = prop-id
