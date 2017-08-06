
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
    SET-METHOD = ∀ {x} → (ε ◃ x) ↦ x
    record SET-CLASS
      ⦃ _ : Constraint ε ⦄
      ⦃ _ : Constraint _◃_ ⦄
      : Ø 𝔞 ∙̂ ℓ
      where
      field ⋆ : SET-METHOD
    open SET-CLASS public
    Leftunit : Ø _
    Leftunit = SET-CLASS
    leftunit⟦_/_⟧ : ⦃ _ : Leftunit ⦄ → SET-METHOD
    leftunit⟦_/_⟧ ⦃ ⌶ ⦄ = SET-CLASS.⋆ ⌶
  module Hidden
    {𝔞} {𝔄 : Ø 𝔞} {𝔢} {𝔈 : Ø 𝔢} {ℓ}
    {_↦_ : 𝔄 → 𝔄 → Ø ℓ}
    {ε : 𝔈}
    {_◃_ : 𝔈 → 𝔄 → 𝔄}
    where
    open ℭlass _↦_ ε _◃_
    leftunit : ⦃ _ : Leftunit ⦄ → SET-METHOD
    leftunit = leftunit⟦_/_⟧

open ℭlass using (⋆) public

module 𝔏eftunit = ℭlass
open ℭlass public
open Hidden public
