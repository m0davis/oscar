module List where

  open import Level
  open import Relation.Binary
  open import Data.List.Base
  open import Data.Bool.Base
  open import Relation.Nullary

  isSubsequenceOf : ∀ { χ ℓℓ : Level } { A : Set χ } { _≟_ : Rel A ℓℓ } { ide : IsDecEquivalence _≟_ } → List A → List A → Bool
  isSubsequenceOf [] _ = true
  isSubsequenceOf _ [] = false
  isSubsequenceOf { ide = ide } ( x ∷ xs ) ( y ∷ ys ) with (IsDecEquivalence._≟_ ide) x y
  isSubsequenceOf { ide = ide } ( x ∷ xs ) ( y ∷ ys ) | yes _ with isSubsequenceOf { ide = ide } xs ys
  isSubsequenceOf { ide = ide } ( x ∷ xs ) ( y ∷ ys ) | yes _ | true = true
  isSubsequenceOf { ide = ide } ( x ∷ xs ) ( y ∷ ys ) | yes _ | false = isSubsequenceOf { ide = ide } ( x ∷ xs ) ys
  isSubsequenceOf { ide = ide } ( x ∷ xs ) ( y ∷ ys ) | no _ = isSubsequenceOf { ide = ide } ( x ∷ xs ) ys
