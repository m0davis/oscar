module New where

module _ where

  open import Agda.Primitive

  record IsBottom {ℓ-⊥} (⊥ : Set ℓ-⊥) ℓ-elim : Set (lsuc ℓ-elim ⊔ ℓ-⊥) where
    field
      ⊥-elim : ⊥ → {A : Set ℓ-elim} → A

  open IsBottom ⦃ … ⦄ public

  record Bottom ℓ-⊥ ℓ-elim : Set (lsuc (ℓ-elim ⊔ ℓ-⊥)) where
    field
      ⊥ : Set ℓ-⊥
      instance ⦃ isBottom ⦄ : IsBottom ⊥ ℓ-elim

    ¬_ : ∀ {a} → Set a → Set (a ⊔ ℓ-⊥)
    ¬_ p = p → ⊥

  open Bottom ⦃ … ⦄ public

  record IsEquivalence {a} {A : Set a} {ℓ} (_≈_ : A → A → Set ℓ) : Set (a ⊔ ℓ) where
    field
      reflexivity : ∀ x → x ≈ x
      symmetry : ∀ x y → x ≈ y → y ≈ x
      transitivity : ∀ x y z → x ≈ y → y ≈ z → x ≈ z

  open IsEquivalence ⦃ … ⦄ public

  record Equivalence {a} (A : Set a) ℓ : Set (a ⊔ lsuc ℓ) where
    infix 4 _≈_
    field
      _≈_ : A → A → Set ℓ
      ⦃ isEquivalence ⦄ : IsEquivalence _≈_

  open Equivalence ⦃ … ⦄ public

  {-# DISPLAY Equivalence._≈_ _ = _≈_ #-}

  infix 4 _≉_
  _≉_ : ∀ {a} {A : Set a} {ℓ} ⦃ _ : Equivalence A ℓ ⦄ {b} ⦃ _ : Bottom b ℓ  ⦄ → A → A → Set (b ⊔ ℓ)
  _≉_ {ℓ = ℓ} x y = ¬ (x ≈ y)

  record _and_ {ℓ} (A : Set ℓ) (B : Set ℓ) : Set ℓ where
    field
      and₁ : A
      and₂ : B

  record _NOR_ {ℓ} (A : Set ℓ) (B : Set ℓ) : Set (lsuc ℓ) where
    field
      ⦃ bottom ⦄ : Bottom ℓ ℓ
      nor₁ : A → ⊥
      nor₂ : B → ⊥

  NOT : ∀ {ℓ} (A : Set ℓ) → Set (lsuc ℓ)
  NOT A = A NOR A

  _AND_ : ∀ {ℓ} (A B : Set ℓ) → Set (lsuc (lsuc ℓ))
  _AND_ A B = (NOT A) NOR (NOT B)

  _OR_ : ∀ {ℓ} (A B : Set ℓ) → Set (lsuc (lsuc ℓ))
  _OR_ A B = NOT (A NOR B)

  record Natlike {a} (A : Set a) ℓ b : Set (lsuc (b ⊔ a ⊔ ℓ)) where
    field
      zero : A
      suc : A → A
      ⦃ equivalence ⦄ : Equivalence A ℓ
      ⦃ bottom ⦄ : Bottom b ℓ
      suc-inj : ∀ {x} {y} → suc x ≈ suc y → x ≈ y
      cong-suc : ∀ {x y} → x ≈ y → suc x ≈ suc y
      zero≉one : zero ≉ suc zero
      zero-is-bottommost : ∀ x → suc x ≉ zero

    break-suc1 : suc zero ≉ suc (suc zero)
    break-suc1 x = zero≉one (suc-inj x)

    break-suc : ∀ x → suc x ≉ suc (suc x)
    break-suc x x₁ = {!suc-inj x₁!}

  record Isomorphic {a} (A : Set a) ℓᵃ ⦃ _ : Equivalence A ℓᵃ ⦄ {b} (B : Set b) ℓᵇ ⦃ _ : Equivalence B ℓᵇ ⦄ : Set (a ⊔ ℓᵃ ⊔ b ⊔ ℓᵇ) where
    field
      toB : A → B
      toA : B → A
      isoA : ∀ x → toA (toB x) ≈ x
      isoB : ∀ x → toB (toA x) ≈ x

  open import Agda.Builtin.Nat
  open import Agda.Builtin.Equality
  instance IsEquivalence≡ : ∀ {a} {A : Set a} → IsEquivalence {a} {A} _≡_
  IsEquivalence.reflexivity IsEquivalence≡ x = refl
  IsEquivalence.symmetry IsEquivalence≡ x .x refl = refl
  IsEquivalence.transitivity IsEquivalence≡ x .x z refl x₂ = x₂

  module _ where
    open import Prelude using (it)

    instance EquivalenceNat : Equivalence Nat lzero
    Equivalence._≈_ EquivalenceNat = _≡_

  record NatIso {a} (A : Set a) ℓ : Set (a ⊔ lsuc ℓ) where
    field
      ⦃ equivalence ⦄ : Equivalence A ℓ
      isoNat : Isomorphic A ℓ Nat lzero

  record Op₂ {a} (A : Set a) : Set a where
    infixl 6 _∙_
    field
      _∙_ : A → A → A

  open Op₂ ⦃ … ⦄ public

  record Op₀ {a} (A : Set a) : Set a where
    field
      ε : A

  open Op₀ ⦃ … ⦄ public

  record MonoidWithSuc {a} (A : Set a) : Set a where
    field
      instance op2 : Op₂ A
      op0 : Op₀ A
      ¡ : A → A

  open MonoidWithSuc ⦃ … ⦄ public

  private
   module ZC where
    private
      module ASD where
        open import Prelude.Nat using ()

  instance MonoidWithSucLevel : MonoidWithSuc Level
  Op₂._∙_ (MonoidWithSuc.op2 MonoidWithSucLevel) = _⊔_
  Op₀.ε (MonoidWithSuc.op0 MonoidWithSucLevel) = lzero
  MonoidWithSuc.¡ MonoidWithSucLevel = lsuc

module _ where

  open import Agda.Builtin.Nat

  instance MonoidWithSucNat : MonoidWithSuc Nat
  Op₂._∙_ (MonoidWithSuc.op2 MonoidWithSucNat) = _+_
  Op₀.ε (MonoidWithSuc.op0 MonoidWithSucNat) = 0
  MonoidWithSuc.¡ MonoidWithSucNat = suc

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality

instance op0fromm : ∀ {a} {A : Set a} ⦃ _ : MonoidWithSuc A ⦄ → Op₀ A
op0fromm = op0

module _ where
 private
  foo : Nat → Set (¡ ε)
  foo x = x ∙ x ≡ x → Set

  bar : 4 ∙ 2 ≡ Nat.suc 5
  bar = refl

module _ where

  open import Agda.Primitive

  infix -65536 ℞_
  ℞_ : ∀ ℓ → Set (lsuc ℓ)
  ℞_ ℓ = Set ℓ

module _ where

  open import Agda.Primitive
