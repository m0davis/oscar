
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
