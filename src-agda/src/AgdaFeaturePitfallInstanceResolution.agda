
module AgdaFeaturePitfallInstanceResolution where

record Symmetry {B : Set₁} (_∼_ : B → B → Set) : Set₁ where
  field symmetry : ∀ {x y} → x ∼ y → y ∼ x

Property : Set → Set₁
Property A = A → Set

Extension : {A : Set} → Property A → Set
Extension P = ∀ f → P f

postulate PropertyEquivalence : ∀ {P : Set} → Property P → Property P → Set

record Regular : Set where
  no-eta-equality

  infixr 5 _,_
  record Σ (𝔒 : Set₁) (𝔓 : 𝔒 → Set) : Set₁ where
    constructor _,_
    field
      π₀ : 𝔒
      π₁ : 𝔓 π₀

  open Σ public

  ExtensionProperty : ∀ (𝔒 : Set) → Set₁
  ExtensionProperty 𝔒 = Σ (Property 𝔒) Extension

  _≈_ : {𝔒 : Set} → ExtensionProperty 𝔒 → ExtensionProperty 𝔒 → Set
  _≈_ P Q = PropertyEquivalence (π₀ P) (π₀ Q)

  record Instance : Set where
    no-eta-equality

    postulate instance _ : ∀ {𝔒 : Set} → Symmetry (_≈_ {𝔒 = 𝔒})
    open Symmetry ⦃ … ⦄

    module Test {𝔒 : Set} where

      test1-fails : {P Q : ExtensionProperty 𝔒} → P ≈ Q → Q ≈ P
      test1-fails P≈Q = symmetry P≈Q

      test2-works : {P Q : ExtensionProperty 𝔒} → P ≈ Q → Q ≈ P
      test2-works {P} {Q} P≈Q = symmetry {x = P} {y = Q} P≈Q

      test3-fails : {P Q : ExtensionProperty 𝔒} → P ≈ Q → Q ≈ P
      test3-fails {P} {Q} P≈Q = symmetry {x = _ , _} {y = _ , _} P≈Q

      test4-works : {P Q : ExtensionProperty 𝔒} → P ≈ Q → Q ≈ P
      test4-works {P} {Q} P≈Q = symmetry {x = _ , π₁ P} {y = _ , π₁ Q} P≈Q

  record Function : Set where
    no-eta-equality

    postulate symmetry : ∀ {𝔒} {x y : ExtensionProperty 𝔒} → x ≈ y → y ≈ x
    -- normalises to   : {𝔒 : Set} {x y : Σ (𝔒 → Set) (λ P → (f : 𝔒) → P f)} → PropertyEquivalence (π₀ x) (π₀ y) → PropertyEquivalence (π₀ y) (π₀ x)

    module Test {𝔒 : Set} where

      test1-fails : {P Q : ExtensionProperty 𝔒} → P ≈ Q → Q ≈ P
      test1-fails P≈Q = symmetry P≈Q

      test2-works : {P Q : ExtensionProperty 𝔒} → P ≈ Q → Q ≈ P
      test2-works {P} {Q} P≈Q = symmetry {x = P} {y = Q} P≈Q

      test3-fails : {P Q : ExtensionProperty 𝔒} → P ≈ Q → Q ≈ P
      test3-fails {P} {Q} P≈Q = symmetry {x = _ , _} {y = _ , _} P≈Q

      test4-works : {P Q : ExtensionProperty 𝔒} → P ≈ Q → Q ≈ P
      test4-works {P} {Q} P≈Q = symmetry {x = _ , π₁ P} {y = _ , π₁ Q} P≈Q

record Revamped : Set where
  no-eta-equality

  record ExtensionProperty (𝔒 : Set) : Set₁ where
    constructor _,_
    field
      π₀ : Property 𝔒
      π₁ : Extension π₀

  open ExtensionProperty

  _≈_ : {𝔒 : Set} → ExtensionProperty 𝔒 → ExtensionProperty 𝔒 → Set
  _≈_ P Q = PropertyEquivalence (π₀ P) (π₀ Q)

  record Instance : Set where
    no-eta-equality

    postulate instance _ : ∀ {𝔒 : Set} → Symmetry (_≈_ {𝔒 = 𝔒})
    open Symmetry ⦃ … ⦄

    module Test {𝔒 : Set} where

      test1-fails : {P Q : ExtensionProperty 𝔒} → P ≈ Q → Q ≈ P
      test1-fails P≈Q = symmetry P≈Q

      test2-works : {P Q : ExtensionProperty 𝔒} → P ≈ Q → Q ≈ P
      test2-works {P} {Q} P≈Q = symmetry {x = P} {y = Q} P≈Q

      test3-fails : {P Q : ExtensionProperty 𝔒} → P ≈ Q → Q ≈ P
      test3-fails {P} {Q} P≈Q = symmetry {x = _ , _} {y = _ , _} P≈Q

      test4-works : {P Q : ExtensionProperty 𝔒} → P ≈ Q → Q ≈ P
      test4-works {P} {Q} P≈Q = symmetry {x = _ , π₁ P} {y = _ , π₁ Q} P≈Q

  record Function : Set where
    no-eta-equality

    postulate symmetry : ∀ {𝔒} {x y : ExtensionProperty 𝔒} → x ≈ y → y ≈ x
    -- normalises to   : ∀ {𝔒} {x y : ExtensionProperty 𝔒} → PropertyEquivalence (π₀ x) (π₀ y) → PropertyEquivalence (π₀ y) (π₀ x)

    module Test {𝔒 : Set} where

      test1-fails : {P Q : ExtensionProperty 𝔒} → P ≈ Q → Q ≈ P
      test1-fails P≈Q = symmetry P≈Q

      test2-works : {P Q : ExtensionProperty 𝔒} → P ≈ Q → Q ≈ P
      test2-works {P} {Q} P≈Q = symmetry {x = P} {y = Q} P≈Q

      test3-fails : {P Q : ExtensionProperty 𝔒} → P ≈ Q → Q ≈ P
      test3-fails {P} {Q} P≈Q = symmetry {x = _ , _} {y = _ , _} P≈Q

      test4-works : {P Q : ExtensionProperty 𝔒} → P ≈ Q → Q ≈ P
      test4-works {P} {Q} P≈Q = symmetry {x = _ , π₁ P} {y = _ , π₁ Q} P≈Q

record PostulatedExtensionProperty : Set where
  no-eta-equality

  postulate
    ExtensionProperty : Set → Set₁
    π₀ : {𝔒 : Set} → ExtensionProperty 𝔒 → Property 𝔒
    π₁ : {𝔒 : Set} → (P : ExtensionProperty 𝔒) → Extension (π₀ P)
    _,_ : {𝔒 : Set} → (π₀ : Property 𝔒) → Extension π₀ → ExtensionProperty 𝔒

  _≈_ : {𝔒 : Set} → ExtensionProperty 𝔒 → ExtensionProperty 𝔒 → Set
  _≈_ P Q = PropertyEquivalence (π₀ P) (π₀ Q)

  record Instance : Set where
    no-eta-equality

    postulate instance _ : ∀ {𝔒 : Set} → Symmetry (_≈_ {𝔒 = 𝔒})
    open Symmetry ⦃ … ⦄

    module Test {𝔒 : Set} where

      test1-works : {P Q : ExtensionProperty 𝔒} → P ≈ Q → Q ≈ P
      test1-works P≈Q = symmetry P≈Q

      test2-works : {P Q : ExtensionProperty 𝔒} → P ≈ Q → Q ≈ P
      test2-works {P} {Q} P≈Q = symmetry {x = P} {y = Q} P≈Q

      test3-inexpressible : {P Q : ExtensionProperty 𝔒} → P ≈ Q → Q ≈ P
      test3-inexpressible {P} {Q} P≈Q = {!!} -- symmetry {x = _ , _} {y = _ , _} P≈Q

      test4-inexpressible : {P Q : ExtensionProperty 𝔒} → P ≈ Q → Q ≈ P
      test4-inexpressible {P} {Q} P≈Q = {!!} -- symmetry {x = _ , π₁ P} {y = _ , π₁ Q} P≈Q

  record Function : Set where
    no-eta-equality

    postulate symmetry : ∀ {𝔒} {x y : ExtensionProperty 𝔒} → x ≈ y → y ≈ x
    -- normalises to   : ∀ {𝔒} {x y : ExtensionProperty 𝔒} → PropertyEquivalence (π₀ x) (π₀ y) → PropertyEquivalence (π₀ y) (π₀ x)

    module Test {𝔒 : Set} where

      test1-works : {P Q : ExtensionProperty 𝔒} → P ≈ Q → Q ≈ P
      test1-works P≈Q = symmetry P≈Q

      test2-works : {P Q : ExtensionProperty 𝔒} → P ≈ Q → Q ≈ P
      test2-works {P} {Q} P≈Q = symmetry {x = P} {y = Q} P≈Q

      test3-inexpressible : {P Q : ExtensionProperty 𝔒} → P ≈ Q → Q ≈ P
      test3-inexpressible {P} {Q} P≈Q = {!!} -- symmetry {x = _ , _} {y = _ , _} P≈Q

      test4-inexpressible : {P Q : ExtensionProperty 𝔒} → P ≈ Q → Q ≈ P
      test4-inexpressible {P} {Q} P≈Q = {!!} -- symmetry {x = _ , π₁ P} {y = _ , π₁ Q} P≈Q

record Constructed : Set where
  no-eta-equality

  infixr 5 _,_
  record Σ (𝔒 : Set₁) (𝔓 : 𝔒 → Set) : Set₁ where
    constructor _,_
    field
      π₀ : 𝔒
      π₁ : 𝔓 π₀

  open Σ public

  ExtensionProperty : Set → Set₁
  ExtensionProperty 𝔒 = Σ (Property 𝔒) Extension

  record _≈_ {𝔒 : Set} (P Q : ExtensionProperty 𝔒) : Set where
    constructor ∁
    field
      π₀ : PropertyEquivalence (π₀ P) (π₀ Q)

  record Instance : Set where
    no-eta-equality

    postulate instance _ : {𝔒 : Set} → Symmetry (_≈_ {𝔒 = 𝔒})
    open Symmetry ⦃ … ⦄

    module Test {𝔒 : Set} where

      test1-works : {P Q : ExtensionProperty 𝔒} → P ≈ Q → Q ≈ P
      test1-works P≈Q = symmetry P≈Q

      test2-works : {P Q : ExtensionProperty 𝔒} → P ≈ Q → Q ≈ P
      test2-works {P} {Q} P≈Q = symmetry {x = P} {y = Q} P≈Q

      test3-works : {P Q : ExtensionProperty 𝔒} → P ≈ Q → Q ≈ P
      test3-works {P} {Q} P≈Q = symmetry {x = _ , _} {y = _ , _} P≈Q

      test4-works : {P Q : ExtensionProperty 𝔒} → P ≈ Q → Q ≈ P
      test4-works {P} {Q} P≈Q = symmetry {x = _ , π₁ P} {y = _ , π₁ Q} P≈Q

  record Function : Set where
    no-eta-equality

    postulate symmetry : ∀ {𝔒} {x y : ExtensionProperty 𝔒} → x ≈ y → y ≈ x
    -- normalises to   : {𝔒 : Set} {x y : Σ (𝔒 → Set) (λ P → (f : 𝔒) → P f)} → x ≈ y → y ≈ x

    module Test {𝔒 : Set} where

      test1-works : {P Q : ExtensionProperty 𝔒} → P ≈ Q → Q ≈ P
      test1-works P≈Q = symmetry P≈Q

      test2-works : {P Q : ExtensionProperty 𝔒} → P ≈ Q → Q ≈ P
      test2-works {P} {Q} P≈Q = symmetry {x = P} {y = Q} P≈Q

      test3-works : {P Q : ExtensionProperty 𝔒} → P ≈ Q → Q ≈ P
      test3-works {P} {Q} P≈Q = symmetry {x = _ , _} {y = _ , _} P≈Q

      test4-works : {P Q : ExtensionProperty 𝔒} → P ≈ Q → Q ≈ P
      test4-works {P} {Q} P≈Q = symmetry {x = _ , π₁ P} {y = _ , π₁ Q} P≈Q

module RevampedSimpleFailure where

  record ExtensionProperty (𝔒 : Set) : Set₁ where
    field
      π₀ : Property 𝔒
      π₁ : Extension π₀

  open ExtensionProperty

  _≈_ : {𝔒 : Set} → ExtensionProperty 𝔒 → ExtensionProperty 𝔒 → Set
  _≈_ P Q = PropertyEquivalence (π₀ P) (π₀ Q)

  postulate symmetry : ∀ {𝔒} {x y : ExtensionProperty 𝔒} → x ≈ y → y ≈ x
  -- normalises to   : ∀ {𝔒} {x y : ExtensionProperty 𝔒} → PropertyEquivalence (π₀ x) (π₀ y) → PropertyEquivalence (π₀ y) (π₀ x)

  test-fails : {𝔒 : Set} {P Q : ExtensionProperty 𝔒} → P ≈ Q → Q ≈ P
  test-fails P≈Q = symmetry P≈Q

module PostulatedExtensionPropertySimpleSuccess where

  postulate
    ExtensionProperty : Set → Set₁
    π₀ : {𝔒 : Set} → ExtensionProperty 𝔒 → Property 𝔒

  _≈_ : {𝔒 : Set} → ExtensionProperty 𝔒 → ExtensionProperty 𝔒 → Set
  _≈_ P Q = PropertyEquivalence (π₀ P) (π₀ Q)

  postulate symmetry : ∀ {𝔒} {x y : ExtensionProperty 𝔒} → x ≈ y → y ≈ x
  -- normalises to   : ∀ {𝔒} {x y : ExtensionProperty 𝔒} → PropertyEquivalence (π₀ {𝔒} x) (π₀ {𝔒} y) → PropertyEquivalence (π₀ {𝔒} y) (π₀ {𝔒} x)

  test-works : {𝔒 : Set} {P Q : ExtensionProperty 𝔒} → P ≈ Q → Q ≈ P
  test-works P≈Q = symmetry P≈Q

module RevampedVerySimpleFailure where

  postulate _∼_ : Set → Set → Set

  record ExtensionProperty : Set₁ where
    field
      π₀ : Set
      π₁ : Set

  open ExtensionProperty

  postulate symmetry : ∀ {x y : ExtensionProperty} → π₀ x ∼ π₀ y → π₀ y ∼ π₀ x

  postulate x y : ExtensionProperty

  test-fails : π₀ x ∼ π₀ y → π₀ y ∼ π₀ x
  test-fails = symmetry

module PostulatedExtensionPropertyVerySimpleSuccess where

  postulate _∼_ : Set → Set → Set

  postulate
    ExtensionProperty : Set₁
    π₀ : ExtensionProperty → Set

  postulate symmetry : ∀ {x y : ExtensionProperty} → π₀ x ∼ π₀ y → π₀ y ∼ π₀ x

  postulate x y : ExtensionProperty

  test-works : π₀ x ∼ π₀ y → π₀ y ∼ π₀ x
  test-works P≈Q = symmetry P≈Q

module RevampedEvenSimplerFailure where

  postulate F : Set → Set

  record ExtensionProperty : Set₁ where
    field
      π₀ : Set
      π₁ : Set

  open ExtensionProperty

  postulate symmetry : ∀ {x : ExtensionProperty} → F (π₀ x) → Set

  postulate x : ExtensionProperty
  postulate Fpx : F (π₀ x)

  test-fails : Set
  test-fails = symmetry Fpx

module PostulatedExtensionPropertyEvenSimplerSuccess where

  postulate F : Set → Set

  postulate
    ExtensionProperty : Set₁
    π₀ : ExtensionProperty → Set

  postulate symmetry : ∀ {x : ExtensionProperty} → F (π₀ x) → Set

  postulate x : ExtensionProperty
  postulate Fpx : F (π₀ x)

  test-works : Set
  test-works = symmetry Fpx
