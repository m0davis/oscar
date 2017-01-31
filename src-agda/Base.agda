
module Base where

module Classes where

  record LeastUpperBound {ℓ} (A : Set ℓ) : Set ℓ where
    infixl 6 _⊔_
    field
      _⊔_ : A → A → A

  open LeastUpperBound ⦃ … ⦄ public

  record Successor {ℓ} (A : Set ℓ) : Set ℓ where
    field
      ↑ : A → A

  open Successor ⦃ … ⦄ public

module Primitive where
  import Agda.Primitive as P

  open Classes

  instance LeastUpperBoundLevel : LeastUpperBound P.Level
  LeastUpperBound._⊔_ LeastUpperBoundLevel = P._⊔_

  instance SuccessorLevel : Successor P.Level
  Successor.↑ SuccessorLevel = P.lsuc

open Primitive
open Classes

infix -65536 ℞_
℞_ : ∀ ℓ → Set _
℞_ ℓ = Set ℓ

record IsIndexedReflexive {𝔵} {𝔛 : Set 𝔵} {𝔞} (𝔄 : 𝔛 → Set 𝔞) {ℓ} (ėq : ∀ {𝑥} → 𝔄 𝑥 → 𝔄 𝑥 → Set ℓ) : ℞ 𝔵 ⊔ 𝔞 ⊔ ℓ where
  private
    infix 4 _≈̇_
    _≈̇_ = ėq
  field
    ṙeflexivity : ∀ {𝑥} (a : 𝔄 𝑥) → a ≈̇ a

open IsIndexedReflexive ⦃ … ⦄ public

record IsIndexedSymmetric {𝔵} {𝔛 : Set 𝔵} {𝔞} (𝔄 : 𝔛 → Set 𝔞) {ℓ} (ėq : ∀ {𝑥} → 𝔄 𝑥 → 𝔄 𝑥 → Set ℓ) : ℞ 𝔵 ⊔ 𝔞 ⊔ ℓ where
  private
    infix 4 _≈̇_
    _≈̇_ = ėq
  field
    ṡymmetry : ∀ {𝑥} (a b : 𝔄 𝑥) → a ≈̇ b → b ≈̇ a

open IsIndexedSymmetric ⦃ … ⦄ public

record IsIndexedTransitive {𝔵} {𝔛 : Set 𝔵} {𝔞} (𝔄 : 𝔛 → Set 𝔞) {ℓ} (ėq : ∀ {𝑥} → 𝔄 𝑥 → 𝔄 𝑥 → Set ℓ) : ℞ 𝔵 ⊔ 𝔞 ⊔ ℓ where
  private
    infix 4 _≈̇_
    _≈̇_ = ėq
  field
    ṫransitivity : ∀ {𝑥} (a b c : 𝔄 𝑥) → a ≈̇ b → b ≈̇ c → a ≈̇ c

open IsIndexedTransitive ⦃ … ⦄ public

record IsIndexedEquivalence {𝔵} {𝔛 : Set 𝔵} {𝔞} (𝔄 : 𝔛 → Set 𝔞) {ℓ} (ėq : ∀ {𝑥 : 𝔛} → 𝔄 𝑥 → 𝔄 𝑥 → Set ℓ) : ℞ 𝔵 ⊔ 𝔞 ⊔ ℓ where
  field
    ⦃ isReflexive ⦄ : IsIndexedReflexive 𝔄 ėq
    ⦃ isSymmetric ⦄ : IsIndexedSymmetric 𝔄 ėq
    ⦃ isTransitive ⦄ : IsIndexedTransitive 𝔄 ėq

open IsIndexedEquivalence ⦃ … ⦄ public

record IndexedEquivalence {𝔵} {𝔛 : Set 𝔵} {𝔞} (𝔄 : 𝔛 → Set 𝔞) ℓ : ℞ 𝔵 ⊔ 𝔞 ⊔ ↑ ℓ where
  infix 4 _≈̇_
  field
    _≈̇_ : ∀ {𝑥 : 𝔛} → 𝔄 𝑥 → 𝔄 𝑥 → Set ℓ
    ⦃ isIndexedEquivalence ⦄ : IsIndexedEquivalence 𝔄 _≈̇_

open import Prelude.Nat
open import Prelude.Fin
open import Prelude.Equality
open import Prelude.Function

postulate
  eFin : ∀ {n} → Fin n → Fin n → Set

eqFin : ∀ {n} → Fin n → Fin n → Set
eqFin = _≡_

module IndexedEquivalence₁ = IndexedEquivalence
open IndexedEquivalence₁ ⦃ … ⦄ renaming (_≈̇_ to _≈̇₁_)

module IndexedEquivalence₂ = IndexedEquivalence
open IndexedEquivalence₂ ⦃ … ⦄ renaming (_≈̇_ to _≈̇₂_)

postulate
  instance IndexedEquivalenceFinProp : IndexedEquivalence Fin _

-- instance IsIndexedReflexiveEqFin : IsIndexedReflexive Fin _≡_
-- IsIndexedReflexive.ṙeflexivity IsIndexedReflexiveEqFin a = it

-- {-
-- instance IndexedEquivalenceProp : ∀ {𝔵} {𝔛 : Set 𝔵} {𝔞} {𝔄 : 𝔛 → Set 𝔞} → IndexedEquivalence 𝔄 𝔞
-- IndexedEquivalence._≈̇_ IndexedEquivalenceProp = _≡_
-- IsIndexedEquivalence.isReflexive (IndexedEquivalence.isIndexedEquivalence IndexedEquivalenceProp) = {!!}
-- IsIndexedEquivalence.isSymmetric (IndexedEquivalence.isIndexedEquivalence IndexedEquivalenceProp) = {!!}
-- IsIndexedEquivalence.isTransitive (IndexedEquivalence.isIndexedEquivalence IndexedEquivalenceProp) = {!!}
-- -}

-- instance IndexedEquivalenceFinProp : IndexedEquivalence Fin _
-- IndexedEquivalence._≈̇_ IndexedEquivalenceFinProp = _≡_
-- IsIndexedEquivalence.isReflexive (IndexedEquivalence.isIndexedEquivalence IndexedEquivalenceFinProp) = it
-- IsIndexedEquivalence.isSymmetric (IndexedEquivalence.isIndexedEquivalence IndexedEquivalenceFinProp) = {!!}
-- IsIndexedEquivalence.isTransitive (IndexedEquivalence.isIndexedEquivalence IndexedEquivalenceFinProp) = {!!}

-- someFin : Fin 5
-- someFin = suc (suc zero)

-- eqFinLemma : someFin ≈̇ someFin
-- eqFinLemma = ṙeflexivity someFin

-- record IsReflexive {𝔞} {𝔄 : Set 𝔞} {ℓ} (eq : 𝔄 → 𝔄 → Set ℓ) : ℞ 𝔞 ⊔ ℓ where
--   private
--     infix 4 _≈_
--     _≈_ = eq
--   field
--     reflexivity : ∀ a → a ≈ a

-- open IsReflexive ⦃ … ⦄

-- record IsSymmetric {𝔞} {𝔄 : Set 𝔞} {ℓ} (eq : 𝔄 → 𝔄 → Set ℓ) : ℞ 𝔞 ⊔ ℓ where
--   private
--     infix 4 _≈_
--     _≈_ = eq
--   field
--     symmetry : ∀ a b → a ≈ b → b ≈ a

-- open IsReflexive ⦃ … ⦄

-- record IsTransitive {𝔞} {𝔄 : Set 𝔞} {ℓ} (eq : 𝔄 → 𝔄 → Set ℓ) : ℞ 𝔞 ⊔ ℓ where
--   private
--     infix 4 _≈_
--     _≈_ = eq
--   field
--     transitivity : ∀ a b c → a ≈ b → b ≈ c → a ≈ c

-- open IsTransitive ⦃ … ⦄

-- record IsEquivalence {𝔞} {𝔄 : Set 𝔞} {ℓ} (eq : 𝔄 → 𝔄 → Set ℓ) : ℞ 𝔞 ⊔ ℓ where
--   field
--     ⦃ isReflexive ⦄ : IsReflexive eq
--     ⦃ isSymmetric ⦄ : IsSymmetric eq
--     ⦃ isTransitive ⦄ : IsTransitive eq

-- open IsEquivalence ⦃ … ⦄

-- record Equivalence {𝔞} {𝔄 : Set 𝔞} ℓ : ℞ 𝔞 ⊔ ↑ ℓ where
--   infix 4 _≈_
--   field
--     _≈_ : 𝔄 → 𝔄 → Set ℓ
--     ⦃ isEquivalence ⦄ : IsEquivalence _≈_

-- open Equivalence ⦃ … ⦄

-- data IndexedTree {𝔵} {𝔛 : Set 𝔵} {𝔞} (𝔄 : 𝔛 → Set 𝔞) : ℞ 𝔵 ⊔ 𝔞 where
--   leaf : IndexedTree 𝔄
--   _fork_ : IndexedTree 𝔄 → IndexedTree 𝔄 → IndexedTree 𝔄
--   variable : ∀ {𝑥} → 𝔄 𝑥 → IndexedTree 𝔄

-- infix 4 _≈ᵗ_
-- data _≈ᵗ_ {𝔵} {𝔛 : Set 𝔵} {𝔞} {𝔄 : 𝔛 → Set 𝔞} ⦃ _ : IndexedEquivalence 𝔄 𝔞 ⦄ : IndexedTree 𝔄 → IndexedTree 𝔄 → ℞ 𝔵 ⊔ 𝔞 where
--   leaf : leaf ≈ᵗ leaf
--   _fork_ : ∀ {left-t₁ left-t₂ right-t₁ right-t₂} →
--              left-t₁ ≈ᵗ left-t₂ →
--              right-t₁ ≈ᵗ right-t₂ →
--              left-t₁ fork right-t₁ ≈ᵗ left-t₂ fork right-t₂
--   variable : ∀ {a} → {left-x right-x : 𝔄 a} → left-x ≈̇ right-x → variable left-x ≈ᵗ variable right-x

-- -- reflexivityIndexedTreeEquality : ∀ {𝔵} {𝔛 : Set 𝔵} {𝔞} (𝔄 : 𝔛 → Set 𝔞) ⦃ _ : IndexedEquivalence 𝔄 𝔞 ⦄ (a : IndexedTree 𝔄) → a ≈ᵗ a
-- -- reflexivityIndexedTreeEquality 𝔄 leaf = leaf
-- -- reflexivityIndexedTreeEquality 𝔄 (a fork a₁) = (reflexivityIndexedTreeEquality 𝔄 _≈_ a) fork (reflexivityIndexedTreeEquality 𝔄 _≈_ a₁)
-- -- reflexivityIndexedTreeEquality 𝔄 (variable x₁) = variable (ṙeflexivity _)

-- -- -- instance IsEquivalenceIndexedTreeEquality : ∀ {𝔵} {𝔛 : Set 𝔵} {𝔞} (𝔄 : 𝔛 → Set 𝔞) {ℓ} (_≈_ : ∀ {𝑥} → 𝔄 𝑥 → 𝔄 𝑥 → Set ℓ) ⦃ _ : IsIndexedEquivalence 𝔄 _≈_ ⦄ → IsEquivalence ((IndexedTreeEquality 𝔄 _≈_))
-- -- -- IsReflexive.reflexivity (IsEquivalence.isReflexive (IsEquivalenceIndexedTreeEquality 𝔄 _≈_)) a = reflexivityIndexedTreeEquality 𝔄 _≈_ a
-- -- -- IsEquivalence.isSymmetric (IsEquivalenceIndexedTreeEquality 𝔄 _≈_) = {!!}
-- -- -- IsEquivalence.isTransitive (IsEquivalenceIndexedTreeEquality 𝔄 _≈_) = {!!}

-- -- -- data Tree {𝔞} (𝔄 : Set 𝔞) : ℞ 𝔞 where
-- -- --   leaf : Tree 𝔄
-- -- --   _fork_ : Tree 𝔄 → Tree 𝔄 → Tree 𝔄
-- -- --   variable : 𝔄 → Tree 𝔄
