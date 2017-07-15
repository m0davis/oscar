
module AgdaFeaturePitfallInstanceResolution where

record Symmetry {B : Set₁} (_∼_ : B → B → Set) : Set₁ where
  field symmetry : ∀ {x y} → x ∼ y → y ∼ x
open Symmetry ⦃ … ⦄

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

  postulate instance SymmetryExtensionProperty : ∀ {𝔒 : Set} → Symmetry (_≈_ {𝔒 = 𝔒})

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

  postulate instance SymmetryExtensionProperty : ∀ {𝔒 : Set} → Symmetry (_≈_ {𝔒 = 𝔒})

  module Test {𝔒 : Set} where

    test1-fails : {P Q : ExtensionProperty 𝔒} → P ≈ Q → Q ≈ P
    test1-fails P≈Q = symmetry P≈Q

    test2-works : {P Q : ExtensionProperty 𝔒} → P ≈ Q → Q ≈ P
    test2-works {P} {Q} P≈Q = symmetry {x = P} {y = Q} P≈Q

    test3-fails : {P Q : ExtensionProperty 𝔒} → P ≈ Q → Q ≈ P
    test3-fails {P} {Q} P≈Q = symmetry {x = _ , _} {y = _ , _} P≈Q

    test4-works : {P Q : ExtensionProperty 𝔒} → P ≈ Q → Q ≈ P
    test4-works {P} {Q} P≈Q = symmetry {x = _ , π₁ P} {y = _ , π₁ Q} P≈Q

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

  postulate instance SymmetryExtensionProperty : {𝔒 : Set} → Symmetry (_≈_ {𝔒 = 𝔒})

  module Test {𝔒 : Set} where

    test1-works : {P Q : ExtensionProperty 𝔒} → P ≈ Q → Q ≈ P
    test1-works P≈Q = symmetry P≈Q

    test2-works : {P Q : ExtensionProperty 𝔒} → P ≈ Q → Q ≈ P
    test2-works {P} {Q} P≈Q = symmetry {x = P} {y = Q} P≈Q

    test3-works : {P Q : ExtensionProperty 𝔒} → P ≈ Q → Q ≈ P
    test3-works {P} {Q} P≈Q = symmetry {x = _ , _} {y = _ , _} P≈Q

    test4-works : {P Q : ExtensionProperty 𝔒} → P ≈ Q → Q ≈ P
    test4-works {P} {Q} P≈Q = symmetry {x = _ , π₁ P} {y = _ , π₁ Q} P≈Q
