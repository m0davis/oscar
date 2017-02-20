
module Foreword where

open import Relation.Binary

--open Setoid ⦃ … ⦄
--open IsEquivalence ⦃ … ⦄

open import Level

record HasEquivalence (A : Set) ℓ : Set (suc ℓ) where
  field
    _≈_ : Rel A ℓ
    ⦃ isEquivalence ⦄ : IsEquivalence _≈_

  setoid : Setoid _ _
  Setoid.Carrier setoid = A
  Setoid._≈_ setoid = _≈_
  Setoid.isEquivalence setoid = isEquivalence

open HasEquivalence ⦃ … ⦄

module TestEquivalence (A : Set) (B : Set) ⦃ _ : HasEquivalence A zero ⦄ ⦃ _ : HasEquivalence B zero ⦄ where
  testA : (x : A) → x ≈ x
  testA = {!!}
