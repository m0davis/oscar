
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

instance HasSubstantiveDischargeList : ∀ {A} ⦃ _ : HasSubstantiveDischarge A A ⦄ → HasSubstantiveDischarge (List A) A
HasSubstantiveDischarge._≽_ HasSubstantiveDischargeList +s - = {!!} -- ∃ λ c → (c ∈ +s) × c ≽ -

instance HasSubstantiveDischargeListList : ∀ {A} ⦃ _ : HasSubstantiveDischarge A A ⦄ → HasSubstantiveDischarge (List A) (List A)
HasSubstantiveDischarge._≽_ HasSubstantiveDischargeListList +s -s = {!!} -- ∀ i → i ∈ -s → +s ≽ i
