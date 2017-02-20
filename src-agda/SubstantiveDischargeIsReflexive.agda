
module SubstantiveDischargeIsReflexive where

open import HasSubstantiveDischarge

record SubstantiveDischargeIsReflexive (A : Set) ⦃ _ : HasSubstantiveDischarge A A ⦄ : Set₁
 where
  field
    ≽-reflexive : (x : A) → x ≽ x

{-
record SubstantiveDischargeIsReflexive (A : Set) : Set₁
 where
  field
    overlap ⦃ hasSubstantiveDischarge ⦄ : HasSubstantiveDischarge A A
    ≽-reflexive : (x : A) → x ≽ x
-}
open SubstantiveDischargeIsReflexive ⦃ … ⦄ public
{-
record SubstantiveDischargeIsReflexive (A : Set) ⦃ _ : HasSubstantiveDischarge A A ⦄ : Set₁
 where
  field
    ≽-reflexive : {x : A} → x ≽ x

open SubstantiveDischargeIsReflexive ⦃ … ⦄
-}
{-# DISPLAY SubstantiveDischargeIsReflexive.≽-reflexive _ = ≽-reflexive #-}
