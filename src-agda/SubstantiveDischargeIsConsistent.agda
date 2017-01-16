
module SubstantiveDischargeIsConsistent where

open import HasNegation
open import HasSubstantiveDischarge

record SubstantiveDischargeIsConsistent (+ : Set) (- : Set) ⦃ _ : HasNegation (-) ⦄ ⦃ _ : HasSubstantiveDischarge (+) (-) ⦄ : Set₁
 where
  field
    ≽-consistent : {+ : +} → { - : - } → + ≽ - → + ⋡ ~ -

open SubstantiveDischargeIsConsistent ⦃ … ⦄

{-# DISPLAY SubstantiveDischargeIsConsistent.≽-consistent _ = ≽-consistent #-}
