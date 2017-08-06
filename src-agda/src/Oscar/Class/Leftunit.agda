
open import Oscar.Prelude
open import Oscar.Data.Constraint

module Oscar.Class.Leftunit where

private

  module ℭlass
    {𝔞} {𝔄 : Ø 𝔞} {𝔢} {𝔈 : Ø 𝔢} {ℓ}
    (_↦_ : 𝔄 → 𝔄 → Ø ℓ)
    (ε : 𝔈)
    (_◃_ : 𝔈 → 𝔄 → 𝔄)
    where
    SET-METHOD : Ø 𝔞 ∙̂ ℓ
    SET-METHOD = ∀ {x} → (ε ◃ x) ↦ x
    record SET-CLASS
      ⦃ _ : Constraint ε ⦄
      ⦃ _ : Constraint _◃_ ⦄
      : Ø 𝔞 ∙̂ ℓ
      where
      field ⋆ : SET-METHOD
    open SET-CLASS public
    GET-CLASS : Ø _
    GET-CLASS = SET-CLASS
    GET-METHOD : ⦃ _ : GET-CLASS ⦄ → SET-METHOD
    GET-METHOD ⦃ ⌶ ⦄ = SET-CLASS.⋆ ⌶

open ℭlass using (⋆) public

module _
  {𝔞} {𝔄 : Ø 𝔞} {𝔢} {𝔈 : Ø 𝔢} {ℓ}
  (_↦_ : 𝔄 → 𝔄 → Ø ℓ)
  (ε : 𝔈)
  (_◃_ : 𝔈 → 𝔄 → 𝔄)
  where
  open ℭlass _↦_ ε _◃_
  Leftunit = GET-CLASS
  leftunit⟦_/_/_⟧ : ⦃ _ : GET-CLASS ⦄ → SET-METHOD
  leftunit⟦_/_/_⟧ = GET-METHOD
module _
  {𝔞} {𝔄 : Ø 𝔞} {𝔢} {𝔈 : Ø 𝔢} {ℓ}
  {_↦_ : 𝔄 → 𝔄 → Ø ℓ}
  {ε : 𝔈}
  {_◃_ : 𝔈 → 𝔄 → 𝔄}
  where
  open ℭlass _↦_ ε _◃_
  leftunit : ⦃ _ : GET-CLASS ⦄ → SET-METHOD
  leftunit = GET-METHOD
