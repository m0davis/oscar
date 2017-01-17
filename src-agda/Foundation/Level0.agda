
module Foundation.Level0 where
{-
it : ∀ {a} {A : Set a} {{x : A}} → A
it {{x}} = x
{-# INLINE it #-}
-}
private

  module Data where

    data ⊥ : Set where

module _ where

  open import Foundation.Bottom

  open import Foundation.Primitive

  instance isBottom-Data : ∀ {a} → IsBottom Data.⊥ a
  IsBottom.⊥-elim isBottom-Data ()

  instance Bottom-Data : ∀ {a} → Bottom 𝟘 a
  Bottom.⊥ Bottom-Data = Data.⊥
  Bottom.isBottom Bottom-Data = isBottom-Data

open import Agda.Builtin.Equality

module _ where

  open import Foundation.Equivalence

  isEquivalence-Builtin : ∀ {a} {A : Set a} → IsEquivalence {A = A} _≡_
  IsEquivalence.reflexivity isEquivalence-Builtin x = refl
  IsEquivalence.symmetry isEquivalence-Builtin x .x refl = refl
  IsEquivalence.transitivity isEquivalence-Builtin x .x z refl x₂ = x₂

  instance _ = isEquivalence-Builtin

  equivalence-Builtin : ∀ {a} {A : Set a} → Equivalence A a
  Equivalence._≈_ equivalence-Builtin = _≡_

  instance _ = equivalence-Builtin
