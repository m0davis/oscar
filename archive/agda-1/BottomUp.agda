{-# OPTIONS --show-implicit #-}

module BottomUp where

open import Foundation.Primitive
open import Foundation.Bottom
open import Foundation.Equivalence

open import Agda.Builtin.List
open import Agda.Builtin.Equality
open import Agda.Builtin.Unit

module NegEquiv {ℓ'} (⊥ : Set ℓ') ⦃ _ : ∀ {b} → IsBottom ⊥ b ⦄ where

  _≉_ : ∀ {a} {A : Set a} {ℓ} ⦃ _ : Equivalence A ℓ ⦄ → A → A → Set (ℓ ⊔ ℓ')
  x ≉ y = x ≈ y → ⊥

module Data-⊥ where

  data Data⊥ : Set where

  instance bottom-rule : ∀ {b} → IsBottom Data⊥ b
  IsBottom.⊥-elim (bottom-rule {b}) () {B}

module IsDecisive-Module {ℓ'} (⊥ : Set ℓ') ⦃ _ : ∀ {b} → IsBottom ⊥ b ⦄ where

  open NegEquiv ⊥

  record IsDecisive a
                    (Decision : (A : Set a) → Set a)
                    (yes-c : {A : Set a} → A → Decision A)
                    (no-c : {A : Set a} → (A → ⊥) → Decision A)
                    ℓ
                    ⦃ equiv-decision : {A : Set a} → Equivalence (Decision A) ℓ ⦄
                    : Set (ℓ ⊔ ⟰ a ⊔ ℓ') where
    field
      yes-correct : {A : Set a} → (dec : Decision A) → (x : A) → yes-c x ≈ dec
      no-correct : {A : Set a} → (dec : Decision A) → (x : A → ⊥) → no-c x ≈ dec
      yes-no-incompat : {A : Set a} (x : A) (nx : A → ⊥) → yes-c x ≉ no-c nx

  open IsDecisive ⦃ … ⦄ public

record ⊤′ {a} : Set a where
  instance constructor tt

module Data-Decision {ℓ} (⊥ : Set ℓ) ⦃ _ : ∀ {b} → IsBottom ⊥ b ⦄ where

  data Decision {a} (A : Set a) : Set (a ⊔ ℓ) where
    yes : A → Decision A
    no : (A → ⊥) → Decision A

  open IsDecisive-Module ⊥

  instance dec-equiv : ∀ {a} {A : Set a} → Equivalence (Decision {a} A) a
  (dec-equiv {a} {A} Equivalence.≈ yes x₁) (yes x₂) = ⊤′
  (dec-equiv {a} {A} Equivalence.≈ yes x₁) (no x₂) = ⊥-elim (x₂ x₁)
  (dec-equiv {a} {A} Equivalence.≈ no x₁) (yes x₂) = ⊥-elim (x₁ x₂)
  (dec-equiv {a} {A} Equivalence.≈ no x₁) (no x₂) = ⊤′
  IsEquivalence.reflexivity (Equivalence.isEquivalence (dec-equiv {a} {A})) (yes x₁) = tt
  IsEquivalence.reflexivity (Equivalence.isEquivalence (dec-equiv {a} {A})) (no x₁) = tt
  IsEquivalence.symmetry (Equivalence.isEquivalence (dec-equiv {a} {A})) (yes x₁) (yes x₂) x₃ = x₃
  IsEquivalence.symmetry (Equivalence.isEquivalence (dec-equiv {a} {A})) (yes x₁) (no x₂) x₃ = x₃
  IsEquivalence.symmetry (Equivalence.isEquivalence (dec-equiv {a} {A})) (no x₁) (yes x₂) x₃ = x₃
  IsEquivalence.symmetry (Equivalence.isEquivalence (dec-equiv {a} {A})) (no x₁) (no x₂) x₃ = x₃
  IsEquivalence.transitivity (Equivalence.isEquivalence (dec-equiv {a} {A})) (yes x₁) (yes x₂) (yes x₃) x₄ x₅ = tt
  IsEquivalence.transitivity (Equivalence.isEquivalence (dec-equiv {a} {A})) (yes x₁) (yes x₂) (no x₃) x₄ x₅ = ⊥-elim (x₃ x₂)
  IsEquivalence.transitivity (Equivalence.isEquivalence (dec-equiv {a} {A})) (yes x₁) (no x₂) (yes x₃) x₄ x₅ = tt
  IsEquivalence.transitivity (Equivalence.isEquivalence (dec-equiv {a} {A})) (yes x₁) (no x₂) (no x₃) x₄ x₅ = ⊥-elim (x₂ x₁)
  IsEquivalence.transitivity (Equivalence.isEquivalence (dec-equiv {a} {A})) (no x₁) (yes x₂) (yes x₃) x₄ x₅ = ⊥-elim (x₁ x₂)
  IsEquivalence.transitivity (Equivalence.isEquivalence (dec-equiv {a} {A})) (no x₁) (yes x₂) (no x₃) x₄ x₅ = tt
  IsEquivalence.transitivity (Equivalence.isEquivalence (dec-equiv {a} {A})) (no x₁) (no x₂) (yes x₃) x₄ x₅ = ⊥-elim (x₂ x₃)
  IsEquivalence.transitivity (Equivalence.isEquivalence (dec-equiv {a} {A})) (no x₁) (no x₂) (no x₃) x₄ x₅ = tt

  instance dec-instance : ∀ {a} → IsDecisive (a ⊔ ℓ) (Decision {a ⊔ ℓ}) yes no (a ⊔ ℓ)
  IsDecisive-Module.IsDecisive.yes-correct (dec-instance {a}) {A} (yes x₁) x₂ = tt
  IsDecisive-Module.IsDecisive.yes-correct (dec-instance {a}) {A} (no x₁) x₂ = ⊥-elim (x₁ x₂)
  IsDecisive-Module.IsDecisive.no-correct (dec-instance {a}) {A} (yes x₁) x₂ = ⊥-elim (x₂ x₁)
  IsDecisive-Module.IsDecisive.no-correct (dec-instance {a}) {A} (no x₁) x₂ = tt
  IsDecisive-Module.IsDecisive.yes-no-incompat (dec-instance {a}) x₁ nx x₂ = nx x₁


open Data-⊥


-- module DecisionModule (⊥ : Set) ⦃ _ : ∀ {a} {b} → IsBottom ⊥ a b ⦄ where

--   record IsDecidableEquivalence {a} {A : Set a} {ℓ} (_≈_ : A → A → Set ℓ) : Set (a ⊔ ℓ) where
--     infix 4 _≈?_
--     field
--       isEquivalence : IsEquivalence _≈_
--       _≈?_ : (x y : A) → Decision (x ≈ y)

--   record DecidableEquivalence {a} (A : Set a) ℓ : Set (lsuc (a ⊔ ℓ)) where
--     field
--       ⦃ equivalence ⦄ : Equivalence A ℓ
--     --open Equivalence equivalence
--     infix 4 _≈?_
--     field
--       _≈?_ : (x y : A) → Decision (x ≈ y)

--   open DecidableEquivalence ⦃ … ⦄ public

--   record DecidableEquivalence' {a} (A : Set a) : Set (lsuc a) where
--     field
--       ⦃ equivalence ⦄ : Equivalence A a
--     infix 4 _≈?_
--     field
--       _≈?_ : (x y : A) → Decision (x ≈ y)

-- data ⊥-fake : Set where
--   faker : ⊥-fake

-- ⊥fake-rule : ∀ {a} {A : Set a} → (A → ⊥-fake) → A → ∀ {b} {B : Set b} → B
-- ⊥fake-rule x x₁ with x x₁
-- ⊥fake-rule x x₁ | faker = {!!}

-- open DecisionModule ⊥

-- data Tree (A : Set) : Set where
--   value : A → Tree A
--   leaf : Tree A
--   branch : Tree A → Tree A → Tree A

-- substitute₁List : ∀ {a} {A : Set a} ⦃ _ : DecidableEquivalence A a ⦄ → A → A → List A → List A
-- substitute₁List x₁ y [] = []
-- substitute₁List x₁ y (x₂ ∷ xs) with x₁ ≈? x₂
-- substitute₁List x₁ y (x₂ ∷ xs) | yes x₃ = y ∷ substitute₁List x₁ y xs
-- substitute₁List x₁ y (x₂ ∷ xs) | no x₃ = x₂ ∷ substitute₁List x₁ y xs

-- open import Agda.Builtin.Nat
-- open import Agda.Builtin.Bool

-- instance EquivalenceNat : Equivalence Nat lzero
-- (EquivalenceNat Equivalence.≈ x) x₁ = (x == x₁) ≡ true
-- IsEquivalence.reflexivity (Equivalence.isEquivalence EquivalenceNat) = isrefl where
--   isrefl : ∀ x → (x == x) ≡ true
--   isrefl zero = refl
--   isrefl (suc x) = isrefl x
-- IsEquivalence.symmetry (Equivalence.isEquivalence EquivalenceNat) = issym where
--   issym : (x y : Nat) →
--             EquivalenceNat .Equivalence._≈_ x y →
--             EquivalenceNat .Equivalence._≈_ y x
--   issym zero zero x₁ = refl
--   issym zero (suc y) x₁ = x₁
--   issym (suc x) zero x₁ = x₁
--   issym (suc x) (suc y) x₁ = issym x y x₁
-- IsEquivalence.transitivity (Equivalence.isEquivalence EquivalenceNat) = {!!}

-- instance DecidableEquivalenceNat : DecidableEquivalence Nat lzero
-- DecisionModule.DecidableEquivalence.equivalence DecidableEquivalenceNat = EquivalenceNat
-- (DecidableEquivalenceNat DecisionModule.DecidableEquivalence.≈? zero) zero = yes refl
-- (DecidableEquivalenceNat DecisionModule.DecidableEquivalence.≈? zero) (suc y) = no (λ x → {!!})
-- (DecidableEquivalenceNat DecisionModule.DecidableEquivalence.≈? suc x) zero = {!!}
-- (DecidableEquivalenceNat DecisionModule.DecidableEquivalence.≈? suc x) (suc y) = {!!}


-- {-
-- $&[{}(=*)+]!#
-- ~%7531902468`
-- ;,.
-- :<>
-- -}
