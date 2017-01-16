
module SubstantiveDischargeIsReflexive where

open import HasSubstantiveDischarge

record SubstantiveDischargeIsReflexive (A : Set) ⦃ _ : HasSubstantiveDischarge A A ⦄ : Set₁
 where
  field
    ≽-reflexive : (x : A) → x ≽ x

open SubstantiveDischargeIsReflexive ⦃ … ⦄
{-
record SubstantiveDischargeIsReflexive (A : Set) ⦃ _ : HasSubstantiveDischarge A A ⦄ : Set₁
 where
  field
    ≽-reflexive : {x : A} → x ≽ x

open SubstantiveDischargeIsReflexive ⦃ … ⦄
-}
{-# DISPLAY SubstantiveDischargeIsReflexive.≽-reflexive _ = ≽-reflexive #-}
