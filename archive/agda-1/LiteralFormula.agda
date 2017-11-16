{-# OPTIONS --allow-unsolved-metas #-}
module LiteralFormula where

open import OscarPrelude

open import IsLiteralFormula
open import HasNegation
open import Formula

record LiteralFormula : Set
 where
  constructor ⟨_⟩
  field
    {formula} : Formula
    isLiteralFormula : IsLiteralFormula formula

open LiteralFormula public

instance EqLiteralFormula : Eq LiteralFormula
Eq._==_ EqLiteralFormula (⟨_⟩ {φ₁} lf₁) (⟨_⟩ {φ₂} lf₂)
 with φ₁ ≟ φ₂
… | no φ₁≢φ₂ = no (λ {refl → φ₁≢φ₂ refl})
Eq._==_ EqLiteralFormula (⟨_⟩ {φ₁} lf₁) (⟨_⟩ {φ₂} lf₂) | yes refl = case (eqIsLiteralFormula lf₁ lf₂) of λ {refl → yes refl}

instance HasNegationLiteralFormula : HasNegation LiteralFormula
HasNegation.~ HasNegationLiteralFormula ⟨ atomic 𝑃 τs ⟩ = ⟨ logical 𝑃 τs ⟩
HasNegation.~ HasNegationLiteralFormula ⟨ logical 𝑃 τs ⟩ = ⟨ atomic 𝑃 τs ⟩

open import Interpretation
open import Vector
open import Term
open import Elements
open import TruthValue

module _ where

  open import HasSatisfaction

  instance HasSatisfactionLiteralFormula : HasSatisfaction LiteralFormula
  HasSatisfaction._⊨_ HasSatisfactionLiteralFormula I ⟨ atomic 𝑃 τs ⟩ = 𝑃⟦ I ⟧ 𝑃 ⟨ ⟨ τ⟦ I ⟧ <$> vector (terms τs) ⟩ ⟩ ≡ ⟨ true ⟩
  HasSatisfaction._⊨_ HasSatisfactionLiteralFormula I ⟨ logical 𝑃 τs ⟩ = 𝑃⟦ I ⟧ 𝑃 ⟨ ⟨ τ⟦ I ⟧ <$> vector (terms τs) ⟩ ⟩ ≡ ⟨ false ⟩

  instance HasDecidableSatisfactionLiteralFormula : HasDecidableSatisfaction LiteralFormula
  HasDecidableSatisfaction._⊨?_ HasDecidableSatisfactionLiteralFormula
    I ⟨ atomic 𝑃 τs ⟩
   with 𝑃⟦ I ⟧ 𝑃 ⟨ ⟨ τ⟦ I ⟧ <$> vector (terms τs) ⟩ ⟩
  … | ⟨ true ⟩ = yes refl
  … | ⟨ false ⟩ = no λ ()
  HasDecidableSatisfaction._⊨?_ HasDecidableSatisfactionLiteralFormula
    I ⟨ logical 𝑃 τs ⟩
    with 𝑃⟦ I ⟧ 𝑃 ⟨ ⟨ τ⟦ I ⟧ <$> vector (terms τs) ⟩ ⟩
  … | ⟨ true ⟩ = no λ ()
  … | ⟨ false ⟩ = yes refl

  instance HasDecidableValidationLiteralFormula : HasDecidableValidation LiteralFormula
  HasDecidableValidation.⊨? HasDecidableValidationLiteralFormula = {!!}

module _ where

  open import HasSubstantiveDischarge

  postulate
    instance cs' : CanonicalSubstitution LiteralFormula
    instance hpu' : HasPairUnification LiteralFormula (CanonicalSubstitution.S cs')

  instance HasSubstantiveDischargeLiteralFormula : HasSubstantiveDischarge LiteralFormula
  --HasSubstantiveDischarge._o≽o_ HasSubstantiveDischargeLiteralFormula φ₁ φ₂ = φ₁ ≡ φ₂
  HasSubstantiveDischarge.hasNegation HasSubstantiveDischargeLiteralFormula = it
  HasSubstantiveDischarge.≽-reflexive HasSubstantiveDischargeLiteralFormula = {!!}
  HasSubstantiveDischarge.≽-consistent HasSubstantiveDischargeLiteralFormula = {!!}
  HasSubstantiveDischarge.≽-contrapositive HasSubstantiveDischargeLiteralFormula = {!!}

  instance HasDecidableSubstantiveDischargeLiteralFormula : HasDecidableSubstantiveDischarge LiteralFormula
  HasDecidableSubstantiveDischarge.hasSubstantiveDischarge HasDecidableSubstantiveDischargeLiteralFormula = it
  HasDecidableSubstantiveDischarge._≽?_ HasDecidableSubstantiveDischargeLiteralFormula φ+ φ- = {!!} -- φ+ ≟ φ-
