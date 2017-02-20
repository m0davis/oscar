
module PropositionalFormula where

open import HasNegation
open import IsPropositionalFormula
open import Formula
open import HasNeitherNor

record PropositionalFormula : Set
 where
  constructor ⟨_⟩
  field
    {formula} : Formula
    isPropositionalFormula : IsPropositionalFormula formula

open PropositionalFormula

instance HasNegationPropositionalFormula : HasNegation PropositionalFormula
HasNegation.~ HasNegationPropositionalFormula ⟨ φ ⟩ = ⟨ logical φ φ ⟩

instance HasNeitherNorPropositionalFormula : HasNeitherNor PropositionalFormula
HasNeitherNor._⊗_ HasNeitherNorPropositionalFormula ⟨ φ₁ ⟩ ⟨ φ₂ ⟩ = ⟨ logical φ₁ φ₂ ⟩

{-# DISPLAY IsPropositionalFormula.logical = _⊗_ #-}
