
module HasSalvation where

open import OscarPrelude

record HasSalvation (A : Set) : Set₁
 where
  field
    ▷_ : A → Set

open HasSalvation ⦃ … ⦄ public

{-# DISPLAY HasSalvation.▷_ _ = ▷_ #-}

record HasDecidableSalvation (A : Set) : Set₁
 where
  field
    ⦃ hasSalvation ⦄ : HasSalvation A
    ▷?_ : (x : A) → Dec $ ▷ x

open HasDecidableSalvation ⦃ … ⦄ public

{-# DISPLAY HasDecidableSalvation.▷?_ _ = ▷?_ #-}
