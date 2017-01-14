
module HasNeitherNor where

record HasNeitherNor (A : Set) : Set
 where
  field
    _⊗_ : A → A → A

open HasNeitherNor ⦃ … ⦄ public
