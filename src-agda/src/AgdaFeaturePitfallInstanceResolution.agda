
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

record RegularVsConstructed : Set where
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

  record _≈R_ {𝔒 : Set} (P Q : ExtensionProperty 𝔒) : Set where
    constructor ∁
    field
      π₀ : PropertyEquivalence (π₀ P) (π₀ Q)

  _≈F_ : {𝔒 : Set} → ExtensionProperty 𝔒 → ExtensionProperty 𝔒 → Set
  _≈F_ P Q = PropertyEquivalence (π₀ P) (π₀ Q)

  record Instance : Set where
    no-eta-equality

    postulate instance _ : {𝔒 : Set} → Symmetry (_≈R_ {𝔒 = 𝔒})
    postulate instance _ : {𝔒 : Set} → Symmetry (_≈F_ {𝔒 = 𝔒})
    open Symmetry ⦃ … ⦄

    module Test {𝔒 : Set} where

      test1-worksR : {P Q : ExtensionProperty 𝔒} → P ≈R Q → Q ≈R P
      test1-worksR P≈Q = symmetry P≈Q

      test2-worksR : {P Q : ExtensionProperty 𝔒} → P ≈R Q → Q ≈R P
      test2-worksR {P} {Q} P≈Q = symmetry {x = P} {y = Q} P≈Q

      test3-worksR : {P Q : ExtensionProperty 𝔒} → P ≈R Q → Q ≈R P
      test3-worksR {P} {Q} P≈Q = symmetry {x = _ , _} {y = _ , _} P≈Q

      test4-worksR : {P Q : ExtensionProperty 𝔒} → P ≈R Q → Q ≈R P
      test4-worksR {P} {Q} P≈Q = symmetry {x = _ , π₁ P} {y = _ , π₁ Q} P≈Q

      test1-failsF : {P Q : ExtensionProperty 𝔒} → P ≈F Q → Q ≈F P
      test1-failsF P≈Q = symmetry P≈Q

      test2-worksF : {P Q : ExtensionProperty 𝔒} → P ≈F Q → Q ≈F P
      test2-worksF {P} {Q} P≈Q = symmetry {x = P} {y = Q} P≈Q

      test3-failsF : {P Q : ExtensionProperty 𝔒} → P ≈F Q → Q ≈F P
      test3-failsF {P} {Q} P≈Q = symmetry {x = _ , _} {y = _ , _} P≈Q

      test4-worksF : {P Q : ExtensionProperty 𝔒} → P ≈F Q → Q ≈F P
      test4-worksF {P} {Q} P≈Q = symmetry {x = _ , π₁ P} {y = _ , π₁ Q} P≈Q

  record Function : Set where
    no-eta-equality

    postulate symmetryR : ∀ {𝔒} {x y : ExtensionProperty 𝔒} → x ≈R y → y ≈R x
    postulate symmetryF : ∀ {𝔒} {x y : ExtensionProperty 𝔒} → x ≈F y → y ≈F x

    module Test {𝔒 : Set} where

      test1-worksR : {P Q : ExtensionProperty 𝔒} → P ≈R Q → Q ≈R P
      test1-worksR P≈Q = symmetryR P≈Q

      test2-worksR : {P Q : ExtensionProperty 𝔒} → P ≈R Q → Q ≈R P
      test2-worksR {P} {Q} P≈Q = symmetryR {x = P} {y = Q} P≈Q

      test3-worksR : {P Q : ExtensionProperty 𝔒} → P ≈R Q → Q ≈R P
      test3-worksR {P} {Q} P≈Q = symmetryR {x = _ , _} {y = _ , _} P≈Q

      test4-worksR : {P Q : ExtensionProperty 𝔒} → P ≈R Q → Q ≈R P
      test4-worksR {P} {Q} P≈Q = symmetryR {x = _ , π₁ P} {y = _ , π₁ Q} P≈Q

      test1-failsF : {P Q : ExtensionProperty 𝔒} → P ≈F Q → Q ≈F P
      test1-failsF P≈Q = symmetryF P≈Q

      test2-worksF : {P Q : ExtensionProperty 𝔒} → P ≈F Q → Q ≈F P
      test2-worksF {P} {Q} P≈Q = symmetryF {x = P} {y = Q} P≈Q

      test3-failsF : {P Q : ExtensionProperty 𝔒} → P ≈F Q → Q ≈F P
      test3-failsF {P} {Q} P≈Q = symmetryF {x = _ , _} {y = _ , _} P≈Q

      test4-worksF : {P Q : ExtensionProperty 𝔒} → P ≈F Q → Q ≈F P
      test4-worksF {P} {Q} P≈Q = symmetryF {x = _ , π₁ P} {y = _ , π₁ Q} P≈Q

record RegularVsConstructedSimpler : Set where
  no-eta-equality

  infixr 5 _,_
  record Σ (𝔒 : Set₁) (𝔓 : 𝔒 → Set) : Set₁ where
    constructor _,_
    field
      π₀ : 𝔒
      π₁ : 𝔓 π₀

  open Σ public

  postulate Prop : Set₁
  postulate Ext : Prop → Set
  postulate PropEq : Prop → Set

  ExtProp : Set₁
  ExtProp = Σ Prop Ext

  record ≈C_ (P : ExtProp) : Set where
    constructor ∁
    field
      π₀ : PropEq (π₀ P)

  ≈R_ : ExtProp → Set
  ≈R_ P = PropEq (π₀ P)

  record Instance : Set where
    no-eta-equality

    record Class {B : Set₁} (∼_ : B → Set) : Set₁ where
      field foo : ∀ {x} → ∼ x → Set
    open Class ⦃ … ⦄

    postulate instance _ : Class ≈C_
    postulate instance _ : Class ≈R_

    module Test where

      test1-worksC : {P : ExtProp} → ≈C P → Set
      test1-worksC P≈Q = foo P≈Q

      test2-worksC : {P : ExtProp} → ≈C P → Set
      test2-worksC {P} P≈Q = foo {x = P} P≈Q

      test3-worksC : {P : ExtProp} → ≈C P → Set
      test3-worksC {P} P≈Q = foo {x = _ , _} P≈Q

      test4-worksC : {P : ExtProp} → ≈C P → Set
      test4-worksC {P} P≈Q = foo {x = _ , π₁ P} P≈Q

      test1-failsR : {P : ExtProp} → ≈R P → Set
      test1-failsR P≈Q = foo P≈Q

      test2-worksR : {P : ExtProp} → ≈R P → Set
      test2-worksR {P} P≈Q = foo {x = P} P≈Q

      test3-failsR : {P : ExtProp} → ≈R P → Set
      test3-failsR {P} P≈Q = foo {x = _ , _} P≈Q

      test4-worksR : {P : ExtProp} → ≈R P → Set
      test4-worksR {P} P≈Q = foo {x = _ , π₁ P} P≈Q

  record Function : Set where
    no-eta-equality

    postulate fooC : {x : ExtProp} → ≈C x → Set
    postulate fooR : {x : ExtProp} → ≈R x → Set

    module Test where

      test1-worksC : {P : ExtProp} → ≈C P → Set
      test1-worksC P≈Q = fooC P≈Q

      test2-worksC : {P : ExtProp} → ≈C P → Set
      test2-worksC {P} P≈Q = fooC {x = P} P≈Q

      test3-worksC : {P : ExtProp} → ≈C P → Set
      test3-worksC {P} P≈Q = fooC {x = _ , _} P≈Q

      test4-worksC : {P : ExtProp} → ≈C P → Set
      test4-worksC {P} P≈Q = fooC {x = _ , π₁ P} P≈Q

      test1-failsR : {P : ExtProp} → ≈R P → Set
      test1-failsR P≈Q = fooR P≈Q

      test2-worksR : {P : ExtProp} → ≈R P → Set
      test2-worksR {P} P≈Q = fooR {x = P} P≈Q

      test3-failsR : {P : ExtProp} → ≈R P → Set
      test3-failsR {P} P≈Q = fooR {x = _ , _} P≈Q

      test4-worksR : {P : ExtProp} → ≈R P → Set
      test4-worksR {P} P≈Q = fooR {x = _ , π₁ P} P≈Q

record RegularVsConstructedMoreSimpler : Set where
  no-eta-equality

  infixr 5 _,_
  record Σ (𝔒 : Set₁) (𝔓 : 𝔒 → Set) : Set₁ where
    constructor _,_
    field
      π₀ : 𝔒
      π₁ : 𝔓 π₀

  open Σ public

  postulate Prop : Set₁
  postulate Ext : Prop → Set
  postulate PropEq : Prop → Set

  ExtProp : Set₁
  ExtProp = Σ Prop Ext

  record Con (P : ExtProp) : Set where
    constructor ∁
    field
      π₀ : PropEq (π₀ P)

  Reg : ExtProp → Set
  Reg P = PropEq (π₀ P)

  record Instance : Set where
    no-eta-equality

    record Class {B : Set₁} (F : B → Set) : Set₁ where
      field foo : ∀ {x} → F x → Set
    open Class ⦃ … ⦄

    postulate instance _ : Class Reg
    postulate instance _ : Class Con

    module Test where

      test1-worksC : {P : ExtProp} → Con P → Set
      test1-worksC P≈Q = foo P≈Q

      test2-worksC : {P : ExtProp} → Con P → Set
      test2-worksC {P} P≈Q = foo {x = P} P≈Q

      test3-worksC : {P : ExtProp} → Con P → Set
      test3-worksC {P} P≈Q = foo {x = _ , _} P≈Q

      test4-worksC : {P : ExtProp} → Con P → Set
      test4-worksC {P} P≈Q = foo {x = _ , π₁ P} P≈Q

      test1-failsR : {P : ExtProp} → Reg P → Set
      test1-failsR P≈Q = foo P≈Q

      test2-worksR : {P : ExtProp} → Reg P → Set
      test2-worksR {P} P≈Q = foo {x = P} P≈Q

      test3-failsR : {P : ExtProp} → Reg P → Set
      test3-failsR {P} P≈Q = foo {x = _ , _} P≈Q

      test4-worksR : {P : ExtProp} → Reg P → Set
      test4-worksR {P} P≈Q = foo {x = _ , π₁ P} P≈Q

  record Function : Set where
    no-eta-equality

    postulate fooC : {x : ExtProp} → Con x → Set
    postulate fooR : {x : ExtProp} → Reg x → Set

    module Test where

      test1-worksC : {P : ExtProp} → Con P → Set
      test1-worksC P≈Q = fooC P≈Q

      test2-worksC : {P : ExtProp} → Con P → Set
      test2-worksC {P} P≈Q = fooC {x = P} P≈Q

      test3-worksC : {P : ExtProp} → Con P → Set
      test3-worksC {P} P≈Q = fooC {x = _ , _} P≈Q

      test4-worksC : {P : ExtProp} → Con P → Set
      test4-worksC {P} P≈Q = fooC {x = _ , π₁ P} P≈Q

      test1-failsR : {P : ExtProp} → Reg P → Set
      test1-failsR P≈Q = fooR P≈Q

      test2-worksR : {P : ExtProp} → Reg P → Set
      test2-worksR {P} P≈Q = fooR {x = P} P≈Q

      test3-failsR : {P : ExtProp} → Reg P → Set
      test3-failsR {P} P≈Q = fooR {x = _ , _} P≈Q

      test4-worksR : {P : ExtProp} → Reg P → Set
      test4-worksR {P} P≈Q = fooR {x = _ , π₁ P} P≈Q

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

  -- was PropertyEquivalence : ∀ {P : Set} → Property P → Property P → Set
  postulate _∼_ : Set → Set → Set

  record ExtensionProperty : Set₁ where
    field
      π₀ : Set -- was Property 𝔒
      π₁ : Set -- was Extension π₀

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

  -- was _∼_, which was PropertyEquivalence
  postulate F : Set → Set

  record ExtensionProperty : Set₁ where
    field
      π₀ : Set
      π₁ : Set

  open ExtensionProperty

  postulate symmetry : ∀ {x : ExtensionProperty} → F (π₀ x) → Set

  postulate x : ExtensionProperty
  postulate Fpx : F (π₀ x)

  test-fails1 : Set
  test-fails1 = symmetry Fpx

  test-fails2 : Set
  test-fails2 = symmetry {x = record { π₀ = π₀ x ; π₁ = _}} Fpx

  test-works-arbitrarily : Set
  test-works-arbitrarily = symmetry {x = record { π₀ = π₀ x ; π₁ = F (F (π₁ x)) }} Fpx

module PostulatedExtensionPropertyEvenSimplerSuccess where

  postulate F : Set → Set

  postulate
    ExtensionProperty : Set₁
    π₀ : ExtensionProperty → Set

  postulate symmetry : ∀ {x : ExtensionProperty} → F (π₀ x) → Set

  postulate x : ExtensionProperty
  postulate Fpx : F (π₀ x)

  test-works1 : Set
  test-works1 = symmetry Fpx

  test-works2 : Set
  test-works2 = symmetry {x = x} Fpx

module RevampedEvenSimplerFailureClassified where

  postulate F : Set → Set

  record ExtensionProperty : Set₁ where
    field
      π₀ : Set
      π₁ : Set

  open ExtensionProperty

  record Symmetry' (R : Set → Set) : Set₁ where
    field symmetry : ∀ {x : ExtensionProperty} → R (π₀ x) → Set
  open Symmetry' ⦃ … ⦄

  postulate instance _ : Symmetry' F

  postulate x : ExtensionProperty
  postulate Fpx : F (π₀ x)

  test-fails1 : Set
  test-fails1 = symmetry Fpx

  test-fails2 : Set
  test-fails2 = symmetry {x = record { π₀ = π₀ x ; π₁ = _}} Fpx

  test-works-arbitrarily : Set
  test-works-arbitrarily = symmetry {x = record { π₀ = π₀ x ; π₁ = F (F (π₁ x)) }} Fpx

module PostulatedExtensionPropertyEvenSimplerSuccessClassified where

  postulate F : Set → Set

  postulate
    ExtensionProperty : Set₁
    π₀ : ExtensionProperty → Set

  record Symmetry' (R : Set → Set) : Set₁ where
    field symmetry : ∀ {x : ExtensionProperty} → R (π₀ x) → Set
  open Symmetry' ⦃ … ⦄

  postulate instance _ : Symmetry' F

  postulate x : ExtensionProperty
  postulate Fpx : F (π₀ x)

  test-works1 : Set
  test-works1 = symmetry Fpx

  test-works2 : Set
  test-works2 = symmetry {x = x} Fpx

module RevampedVsPostulated where

  record R : Set₁ where
    field
      f1 : Set
      f2 : Set

  open R

  postulate fooR : ∀ {x : R} → f1 x → Set

  postulate r : R
  postulate f1r : f1 r

  test-fails1 : Set
  test-fails1 = fooR f1r

  postulate
    S : Set₁
    g1 : S → Set

  postulate fooS : ∀ {x : S} → g1 x → Set

  postulate s : S
  postulate g1s : g1 s

  test-works1 : Set
  test-works1 = fooS g1s
