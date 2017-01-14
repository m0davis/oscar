{-# OPTIONS --show-implicit #-}
module Exegesis where

module Superclasses where

  open import Agda.Primitive
  open import Agda.Builtin.Equality

  record Semigroup (A : Set) : Set where
    field
      _∙_ : A → A → A
      assoc : ∀ x y z → (x ∙ y) ∙ z ≡ x ∙ (y ∙ z)
      cong : ∀ w x y z → w ≡ y → x ≡ z → w ∙ x ≡ y ∙ z

  open Semigroup ⦃ … ⦄

  record Identity {A : Set} (_∙_ : A → A → A) : Set where
    field
      ε : A
      left-identity  : ∀ x → ε ∙ x ≡ x
      right-identity : ∀ x → x ∙ ε ≡ x

  open Identity ⦃ … ⦄

  record Monoid (A : Set) : Set where
    field
      ⦃ semigroup ⦄ : Semigroup A
      ⦃ identity ⦄  : Identity (_∙_ ⦃ semigroup ⦄)

  open Monoid ⦃ … ⦄

  foo : {A : Set} ⦃ m : Monoid A ⦄ → (x : A) → x ∙ ε ⦃ identity ⦄ ≡ x
  foo x = right-identity x

module StandardLibraryMethod where

  open import Agda.Primitive
  open import Agda.Builtin.Equality

  record Semigroup (A : Set) : Set where
    field
      _∙_ : A → A → A
      assoc : ∀ x y z → (x ∙ y) ∙ z ≡ x ∙ (y ∙ z)
      cong : ∀ w x y z → w ≡ y → x ≡ z → w ∙ x ≡ y ∙ z

  --open Semigroup ⦃ … ⦄

  record Identity (A : Set) (ε : A) (_∙_ : A → A → A) : Set where
    field
      left-identity  : ∀ x → ε ∙ x ≡ x
      right-identity : ∀ x → x ∙ ε ≡ x

  --open Identity ⦃ … ⦄

  record Monoid (A : Set) : Set where
    field
      s : Semigroup A

    open Semigroup s public

    field
      ε : A
      i : Identity A ε _∙_

    open Identity i public

  open Monoid ⦃ … ⦄

  foo : {A : Set} ⦃ m : Monoid A ⦄ → (x : A) → x ∙ ε ≡ x
  foo x = right-identity x -- right-identity x

module Cascade where

  open import Agda.Primitive
  open import Agda.Builtin.Equality

  record Semigroup (A : Set) : Set where
    field
      _∙_ : A → A → A
      assoc : ∀ x y z → (x ∙ y) ∙ z ≡ x ∙ (y ∙ z)
      cong : ∀ w x y z → w ≡ y → x ≡ z → w ∙ x ≡ y ∙ z

  open Semigroup ⦃ … ⦄

  record RawMonoid (A : Set) ⦃ _ : Semigroup A ⦄ : Set where
    no-eta-equality
    field
      ε : A

  open RawMonoid ⦃ … ⦄

  record Identity (A : Set) (ε : A) (_∙_ : A → A → A) : Set where
    field
      left-identity  : ∀ x → ε ∙ x ≡ x
      right-identity : ∀ x → x ∙ ε ≡ x

  open Identity ⦃ … ⦄

  foo : {A : Set} ⦃ _ : Semigroup A ⦄ ⦃ _ : RawMonoid A ⦄ ⦃ i : Identity A ε _∙_ ⦄ → (x : A) → x ∙ ε ≡ x
  foo ⦃ s ⦄ ⦃ rm ⦄ ⦃ i ⦄ x = right-identity ⦃ i ⦄ x

module Buncha where

  open import Agda.Primitive
  open import Agda.Builtin.Equality

  record Semigroup (A : Set) : Set where
    field
      _∙_ : A → A → A
      assoc : ∀ x y z → (x ∙ y) ∙ z ≡ x ∙ (y ∙ z)
      cong : ∀ w x y z → w ≡ y → x ≡ z → w ∙ x ≡ y ∙ z

  open Semigroup ⦃ … ⦄

  record RawMonoid (A : Set) : Set where
    field
      ε : A

  open RawMonoid ⦃ … ⦄

  record Identity {A : Set} (_∙_ : A → A → A) ⦃ _ : RawMonoid A ⦄ : Set where
    field
      left-identity  : ∀ x → ε ∙ x ≡ x
      right-identity : ∀ x → x ∙ ε ≡ x

  open Identity ⦃ … ⦄

  record Monoid (A : Set) : Set where
    field
      ⦃ semigroup ⦄ : Semigroup A
      ⦃ rawmonoid ⦄ : RawMonoid A
      ⦃ identity ⦄ : Identity {A} _∙_

  open Monoid ⦃ … ⦄

  foo : {A : Set} ⦃ _ : Semigroup A ⦄ ⦃ _ : RawMonoid A ⦄ ⦃ _ : Identity _∙_ ⦄ → (x : A) → x ∙ ε ≡ x
  foo x = right-identity x

  bar : {A : Set} ⦃ _ : Monoid A ⦄ → (x : A) → x ∙ ε ≡ x
  bar x = right-identity x

module SomethingThatWorks where

  open import Agda.Primitive
  open import Agda.Builtin.Equality

  record Equivalence (A : Set) : Set₁ where
    infix 4 _≈_
    field
      _≈_ : A → A → Set
      reflexive : ∀ x → x ≈ x
      symmetric : ∀ {x y} → x ≈ y → y ≈ x
      transitive : ∀ {x y z} → x ≈ y → y ≈ z → x ≈ z

  open Equivalence ⦃ … ⦄

  record Operator (A : Set) : Set where
    field
      _∙_ : A → A → A

  record Semigroup (A : Set) : Set₁ where
    field
      ⦃ operator ⦄ : Operator A
      ⦃ equivalence ⦄ : Equivalence A

    open Operator operator public
    field
      assoc : ∀ x y z → (x ∙ y) ∙ z ≡ x ∙ (y ∙ z)
      cong : ∀ w x y z → w ≡ y → x ≡ z → w ∙ x ≡ y ∙ z

  open Semigroup ⦃ … ⦄

  record IdentityElement (A : Set) : Set where
    field
      ε : A

  module ε where

    open IdentityElement ⦃ … ⦄ public

  record Identity {A : Set} (_∙_ : A → A → A) ⦃ _ : IdentityElement A ⦄ : Set where
    open ε
    field
      left-identity  : ∀ x → ε ∙ x ≡ x
      right-identity : ∀ x → x ∙ ε ≡ x

  open Identity ⦃ … ⦄

  record Monoid (A : Set) : Set₁ where
    field
      ⦃ semigroup ⦄ : Semigroup A
      ⦃ identityElement ⦄ : IdentityElement A
      ⦃ identity ⦄ : Identity {A} _∙_

  open Monoid ⦃ … ⦄

  bar : {A : Set} ⦃ _ : Monoid A ⦄ {B : Set} ⦃ _ : Monoid B ⦄ (open ε) → (x : A) → x ∙ ε ≡ x
  bar x = right-identity x

module SeparatingIsFromOught where

  open import Agda.Primitive
  open import Agda.Builtin.Equality

  record Equivalence (A : Set) : Set₁ where
    infix 4 _≈_
    field
      _≈_ : A → A → Set
      reflexive : ∀ x → x ≈ x
      symmetric : ∀ {x y} → x ≈ y → y ≈ x
      transitive : ∀ {x y z} → x ≈ y → y ≈ z → x ≈ z

  open Equivalence ⦃ … ⦄

  record Operator (A : Set) : Set where
    field
      _∙_ : A → A → A

  open Operator ⦃ … ⦄

  record IsSemigroup (A : Set) ⦃ _ : Operator A ⦄ ⦃ _ : Equivalence A ⦄ : Set where
    field
      assoc : ∀ (x : A) y z → (x ∙ y) ∙ z ≈ x ∙ (y ∙ z)
      cong : ∀ (w : A) x y z → w ≈ y → x ≈ z → w ∙ x ≈ y ∙ z

  open IsSemigroup ⦃ … ⦄

  record Semigroup (A : Set) : Set₁ where
    field
      ⦃ operator ⦄ : Operator A
      ⦃ equivalence ⦄ : Equivalence A
      ⦃ isSemigroup ⦄ : IsSemigroup A

  open Semigroup ⦃ … ⦄
{-
  record IdentityElement (A : Set) : Set where
    field
      ε : A

  open IdentityElement ⦃ … ⦄
-}
  record IsIdentity (A : Set) ⦃ _ : Operator A ⦄ {-⦃ _ : IdentityElement A ⦄-} ⦃ _ : Equivalence A ⦄ : Set where

--  record IsIdentity {A : Set} (_∙_ : A → A → A) (ε : A) ⦃ _ : Equivalence A ⦄ : Set where
    field
      ε : A
      left-identity  : ∀ (x : A) → ε ∙ x ≈ x
      right-identity : ∀ (x : A) → x ∙ ε ≈ x

  open IsIdentity ⦃ … ⦄

  record Monoid (A : Set) : Set₁ where
    field
      ⦃ semigroup ⦄ : Semigroup A
      --⦃ identityElement ⦄ : IdentityElement A
      --ε : A
      --⦃ identity ⦄ : IsIdentity (_∙_ {A}) ε
--      ⦃ operator ⦄ : Operator A
      ⦃ identity ⦄ : IsIdentity A

  open Monoid ⦃ … ⦄

  bar : {A : Set} ⦃ m : Monoid A ⦄ {B : Set} ⦃ _ : Semigroup B ⦄ → (x : A) → x ∙ ε ≈ x
  bar x = right-identity x

  bar2 : {A : Set} ⦃ _ : Monoid A ⦄ → (x y : A) → (x ∙ ε) ∙ y ≈ x ∙ (ε ∙ y)
  bar2 x y = assoc x ε y

module FineControl where

  record IsEquivalence {A : Set} (_≈_ : A → A → Set) : Set₁ where
    field
      reflexive : ∀ x → x ≈ x
      symmetric : ∀ {x y} → x ≈ y → y ≈ x
      transitive : ∀ {x y z} → x ≈ y → y ≈ z → x ≈ z

  open IsEquivalence ⦃ … ⦄

  record Equivalence (A : Set) : Set₁ where
    infix 4 _≈_
    field
      _≈_ : A → A → Set
      ⦃ isEquivalence ⦄ : IsEquivalence _≈_

  open Equivalence ⦃ … ⦄

  record IsSemigroup {A : Set} (_∙_ : A → A → A) ⦃ _ : Equivalence A ⦄ : Set where
    field
      assoc : ∀ (x : A) y z → (x ∙ y) ∙ z ≈ x ∙ (y ∙ z)
      cong : ∀ (w : A) x y z → w ≈ y → x ≈ z → w ∙ x ≈ y ∙ z

  open IsSemigroup ⦃ … ⦄

  record Semigroup (A : Set) : Set₁ where
    field
      ⦃ equivalence ⦄ : Equivalence A
      _∙_ : A → A → A
      ⦃ isSemigroup ⦄ : IsSemigroup _∙_

  open Semigroup ⦃ … ⦄

  record Identity (A : Set) : Set where
    field
      ε : A

  open Identity ⦃ … ⦄

--  record IsLeftIdentity {A B : Set} (_∙_ : A → B → B) ⦃ _ : Identity A ⦄ (ε : A) ⦃ _ : Equivalence B ⦄ : Set where
  record IsLeftIdentity {A B : Set} (_∙_ : A → B → B) ⦃ _ : Identity A ⦄ ⦃ _ : Equivalence B ⦄ : Set where
    field
      left-identity  : ∀ x → ε ∙ x ≈ x

  open IsLeftIdentity ⦃ … ⦄

--  record IsRightIdentity {A B : Set} (_∙_ : B → A → B) (ε : A) ⦃ _ : Equivalence B ⦄ : Set where
  record IsRightIdentity {A B : Set} (_∙_ : B → A → B) ⦃ _ : Identity A ⦄ ⦃ _ : Equivalence B ⦄ : Set where
    field
      right-identity : ∀ x → x ∙ ε ≈ x

  open IsRightIdentity ⦃ … ⦄

  record Monoid (A : Set) : Set₁ where
    field
      ⦃ semigroup ⦄ : Semigroup A
      --ε : A
      ⦃ identity ⦄ : Identity A
      ⦃ lidentity ⦄ : IsLeftIdentity {A = A} _∙_
      ⦃ ridentity ⦄ : IsRightIdentity {A = A} _∙_

  open Monoid ⦃ … ⦄

  bar : {A : Set} ⦃ m : Monoid A ⦄ → (x : A) → x ∙ ε ≈ x
  bar {A} x = right-identity {_∙_ = _∙_} x -- right-identity {_∙_ = _∙_} x

  bar' : {A : Set} ⦃ m : Monoid A ⦄ → (x : A) → x ∙ ε ≈ x
  bar' x = right-identity x

  bar2 : {A : Set} ⦃ _ : Monoid A ⦄ → (x y z : A) → (x ∙ y) ∙ z ≈ x ∙ (y ∙ z)
  bar2 x y z = assoc x y z

module FineControl2 where

  record IsEquivalence {A : Set} (_≈_ : A → A → Set) : Set₁ where
    field
      reflexive : ∀ x → x ≈ x
      symmetric : ∀ {x y} → x ≈ y → y ≈ x
      transitive : ∀ {x y z} → x ≈ y → y ≈ z → x ≈ z

  open IsEquivalence ⦃ … ⦄

  record Equivalence (A : Set) : Set₁ where
    infix 4 _≈_
    field
      _≈_ : A → A → Set
      ⦃ isEquivalence ⦄ : IsEquivalence _≈_

  open Equivalence ⦃ … ⦄

  record IsSemigroup {A : Set} (_∙_ : A → A → A) ⦃ _ : Equivalence A ⦄ : Set where
    field
      assoc : ∀ (x : A) y z → (x ∙ y) ∙ z ≈ x ∙ (y ∙ z)
      cong : ∀ (w : A) x y z → w ≈ y → x ≈ z → w ∙ x ≈ y ∙ z

  open IsSemigroup ⦃ … ⦄



  record Semigroup (A : Set) : Set₁ where
    field
      overlap ⦃ equivalence ⦄ : Equivalence A
      _∙_ : A → A → A
      ⦃ isSemigroup ⦄ : IsSemigroup _∙_

  open Semigroup ⦃ … ⦄

  record Identity (A : Set) : Set where
    field
      ε : A

  open Identity ⦃ … ⦄

--  record IsLeftIdentity {A B : Set} (_∙_ : A → B → B) (ε : A) ⦃ _ : Equivalence B ⦄ : Set where
--  record IsLeftIdentity {A B : Set} (_∙_ : A → B → B) : Set₁ where
  record IsLeftIdentity {A B : Set} (_∙_ : A → B → B) ⦃ _ : Identity A ⦄ ⦃ _ : Equivalence B ⦄ : Set₁ where
    field
      left-identity  : ∀ x → ε ∙ x ≈ x

  open IsLeftIdentity ⦃ … ⦄

--  record IsRightIdentity {A B : Set} (_∙_ : B → A → B) (ε : A) ⦃ _ : Equivalence B ⦄ : Set where
--  record IsRightIdentity {A B : Set} (_∙_ : B → A → B) : Set₁ where
  record IsRightIdentity {A B : Set} (_∙_ : B → A → B) ⦃ _ : Identity A ⦄ ⦃ _ : Equivalence B ⦄ : Set₁ where
    field
      right-identity : ∀ x → x ∙ ε ≈ x

--  open IsRightIdentity ⦃ … ⦄

  record Monoid (A : Set) : Set₁ where
    field
      ⦃ semigroup ⦄ : Semigroup A
      --ε : A
      ⦃ identity ⦄ : Identity A
      ⦃ lidentity ⦄ : IsLeftIdentity {A = A} _∙_
      ⦃ ridentity ⦄ : IsRightIdentity {A = A} _∙_

    open IsRightIdentity ridentity public

  open Monoid ⦃ … ⦄

  bar : {A : Set} ⦃ m : Monoid A ⦄ → (x : A) → x ∙ ε ≈ x
  bar {A} x = right-identity x -- right-identity {_∙_ = _∙_} x

  bar' : {A : Set} ⦃ m : Monoid A ⦄ → (x : A) → x ∙ ε ≈ x
  bar' x = right-identity x

  bar2 : {A : Set} ⦃ _ : Monoid A ⦄ → (x y z : A) → (x ∙ y) ∙ z ≈ x ∙ (y ∙ z)
  bar2 x y z = assoc x y z
