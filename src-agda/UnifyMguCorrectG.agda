open import Relation.Binary using (IsDecEquivalence)
open import Agda.Builtin.Equality

module UnifyMguCorrectG (FunctionName : Set) ⦃ isDecEquivalenceA : IsDecEquivalence (_≡_ {A = FunctionName}) ⦄ where


open import UnifyTermF FunctionName
open import UnifyMguF FunctionName
open import UnifyMguCorrectF FunctionName
