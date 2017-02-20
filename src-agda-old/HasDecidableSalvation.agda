
module HasDecidableSalvation where

open import OscarPrelude
open import HasSalvation

record HasDecidableSalvation (A : Set) : Set₁
 where
  field
    ⦃ hasSalvation ⦄ : HasSalvation A
    ▷?_ : (x : A) → Dec $ ▷ x

open HasDecidableSalvation ⦃ … ⦄ public

{-# DISPLAY HasDecidableSalvation.▷?_ _ = ▷?_ #-}
