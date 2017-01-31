{-# OPTIONS --allow-unsolved-metas #-}
module HasDecidableSubstantiveDischarge where

open import OscarPrelude
open import HasSubstantiveDischarge

record HasDecidableSubstantiveDischarge (+ : Set) (- : Set) ⦃ _ : HasSubstantiveDischarge (+) (-) ⦄ : Set₁
 where
  field
    _≽?_ : (+ : +) → (- : -) → Dec $ + ≽ -

open HasDecidableSubstantiveDischarge ⦃ … ⦄ public

{-# DISPLAY HasDecidableSubstantiveDischarge._≽?_ _ = _≽?_ #-}

instance HasDecidableSubstantiveDischargeList : ∀ {A} ⦃ _ : HasSubstantiveDischarge A A ⦄ ⦃ _ : HasDecidableSubstantiveDischarge A A ⦄ ⦃ _ : Eq A ⦄ → HasDecidableSubstantiveDischarge (List A) A
HasDecidableSubstantiveDischarge._≽?_ HasDecidableSubstantiveDischargeList +s - = {!!}

instance HasDecidableSubstantiveDischargeListList : ∀ {A} ⦃ _ : HasSubstantiveDischarge A A ⦄ ⦃ _ : HasDecidableSubstantiveDischarge A A ⦄ ⦃ _ : Eq A ⦄ → HasDecidableSubstantiveDischarge (List A) (List A)
HasDecidableSubstantiveDischarge._≽?_ HasDecidableSubstantiveDischargeListList +s -s = {!!}
