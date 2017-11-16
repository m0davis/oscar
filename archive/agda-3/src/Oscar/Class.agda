
open import Oscar.Prelude
open import Oscar.Data.Constraint

module Oscar.Class where

record InnerClass {ℓ} {𝔢} {CONSTRAINTS : Ø 𝔢} (constraints : CONSTRAINTS) (_ : Constraint constraints) (SET-METHOD : Ø ℓ) : Ø ℓ where
  constructor ∁
  field
    ⋆ : SET-METHOD

open InnerClass public

module ℭLASS
  {ℓ}
  {𝔢}
  {CONSTRAINTS : Ø 𝔢}
  (constraints : CONSTRAINTS)
  (c : Ø ℓ)
  where
  class = InnerClass constraints ∅ c
  type = c
  method : ⦃ _ : class ⦄ → type
  method ⦃ ⌶ ⦄ = InnerClass.⋆ ⌶

record Rℭlass
  {ℓ 𝔯}
  {𝔢}
  {CONSTRAINTS : Ø 𝔢}
  (constraints : CONSTRAINTS)
  : Ø ↑̂ (ℓ ∙̂ 𝔯)
  where
  constructor ∁
  field
    SET-METHOD : Ø ℓ
    SET-R : SET-METHOD → Ø 𝔯
  record SET-CLASS
    ⦃ _ : Constraint constraints ⦄
    : Ø ℓ ∙̂ 𝔯
    where
    constructor ∁
    field ⋆ : SET-METHOD
          ⦃ ⋆⋆ ⦄ : SET-R ⋆
  open SET-CLASS public
  GET-CLASS : Ø _
  GET-CLASS = SET-CLASS
  GET-METHOD : ⦃ _ : GET-CLASS ⦄ → SET-METHOD
  GET-METHOD ⦃ ⌶ ⦄ = SET-CLASS.⋆ ⌶

open Rℭlass using (⋆; ∁) public
