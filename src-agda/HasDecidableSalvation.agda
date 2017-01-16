
module HasDecidableSalvation where

open import OscarPrelude
open import HasSalvation

record HasDecidableSalvation (A : Set) ⦃ _ : HasSalvation A ⦄ : Set₁
 where
  field
    ▷?_ : (x : A) → Dec $ ▷_ x

open HasDecidableSalvation ⦃ … ⦄ public

{-# DISPLAY HasDecidableSalvation.▷?_ _ = ▷?_ #-}

record HasDecidableSalvation' (A : Set) : Set₁
 where
  field
    ⦃ hasSalvation ⦄ : HasSalvation A
    ▷'?_ : (x : A) → Dec $ ▷_ x

open HasDecidableSalvation' ⦃ … ⦄ public

{-# DISPLAY HasDecidableSalvation'.▷'?_ _ = ▷'?_ #-}
