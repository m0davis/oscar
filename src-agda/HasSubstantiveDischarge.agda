
module HasSubstantiveDischarge where

open import OscarPrelude

record HasSubstantiveDischarge (+ : Set) (- : Set) : Set₁
 where
  field
    _≽_ : + → - → Set

  _⋡_ : + → - → Set
  + ⋡ - = ¬ + ≽ -

open HasSubstantiveDischarge ⦃ … ⦄ public

{-# DISPLAY HasSubstantiveDischarge._≽_ _ = _≽_ #-}

open import Membership

instance HasSubstantiveDischargeList : ∀ {A} ⦃ _ : HasSubstantiveDischarge A A ⦄ → HasSubstantiveDischarge (List A) A
HasSubstantiveDischarge._≽_ (HasSubstantiveDischargeList {A}) +s - = ∃ λ (c : A) → (c ∈ +s) × c ≽ -

instance HasSubstantiveDischargeListList : ∀ {A} ⦃ _ : HasSubstantiveDischarge A A ⦄ → HasSubstantiveDischarge (List A) (List A)
HasSubstantiveDischarge._≽_ (HasSubstantiveDischargeListList {A}) +s -s = ∀ (i : A) → i ∈ -s → +s ≽ i
