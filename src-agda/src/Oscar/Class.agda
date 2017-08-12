
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
    constructor ∁
    field ⋆ : SET-METHOD
  open SET-CLASS public
  GET-CLASS : Ø _
  GET-CLASS = SET-CLASS
  GET-METHOD : ⦃ _ : GET-CLASS ⦄ → SET-METHOD
  GET-METHOD ⦃ ⌶ ⦄ = SET-CLASS.⋆ ⌶

open ℭlass using (⋆; ∁) public

module ℭLASS
  {ℓ}
  {𝔢}
  {CONSTRAINTS : Ø 𝔢}
  {constraints : CONSTRAINTS}
  (r : ℭlass {ℓ} constraints)
  where
  -- family = r
  open ℭlass r public using () renaming
    (GET-CLASS to class
    ;SET-METHOD to type
    ;GET-METHOD to method)

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
