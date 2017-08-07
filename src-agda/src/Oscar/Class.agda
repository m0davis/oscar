
open import Oscar.Prelude
open import Oscar.Data.Constraint

module Oscar.Class where

record ℭlass
  {ℓ}
  {𝔢}
  {CONSTRAINTS : Ø 𝔢}
  (constraints : CONSTRAINTS)
  : Ø ↑̂ ℓ
  where
  constructor ∁
  field
    SET-METHOD : Ø ℓ
  record SET-CLASS
    ⦃ _ : Constraint constraints ⦄
    : Ø ℓ
    where
    field ⋆ : SET-METHOD
  open SET-CLASS public
  GET-CLASS : Ø _
  GET-CLASS = SET-CLASS
  GET-METHOD : ⦃ _ : GET-CLASS ⦄ → SET-METHOD
  GET-METHOD ⦃ ⌶ ⦄ = SET-CLASS.⋆ ⌶

open ℭlass using (⋆) public
