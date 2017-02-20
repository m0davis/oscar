
module HasNegation where

record HasNegation (A : Set) : Set
 where
  field
    ~ : A → A

open HasNegation ⦃ … ⦄ public

{-# DISPLAY HasNegation.~ _ = ~ #-}
