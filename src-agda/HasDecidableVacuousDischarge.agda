
module HasDecidableVacuousDischarge where

open import OscarPrelude
--open import HasVacuousDischarge
open import HasSubstantiveDischarge
open import HasNegation

record HasDecidableVacuousDischarge (A : Set) : Set₁
 where
  field
    -- ⦃ hasVacuousDischarge ⦄ : HasVacuousDischarge A
    ⦃ hasNegation ⦄ : HasNegation A
    ⦃ hasSubstantiveDischarge ⦄ : HasSubstantiveDischarge A
    ◁?_ : (x : List A) → Dec $ ◁ x

open HasDecidableVacuousDischarge ⦃ … ⦄ public

{-# DISPLAY HasDecidableVacuousDischarge.◁?_ _ = ◁?_ #-}
