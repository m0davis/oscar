
module HasSalvation where

record HasSalvation (A : Set) : Set₁
 where
  field
    -- {isVacuouslyDischargable} : Set
    -- ⦃ hasVacuousDischarge ⦄ : HasVacuousDischarge isVacuouslyDischargable
    ▷_ : A → Set

open HasSalvation ⦃ … ⦄ public

{-# DISPLAY HasSalvation.▷_ _ = ▷_ #-}
