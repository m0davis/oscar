{-# OPTIONS --allow-unsolved-metas #-}
module LiteralSequent where

open import Sequent
open import IsLiteralSequent

record LiteralSequent : Set
 where
  constructor ⟨_⟩
  field
    {sequent} : Sequent
    isLiteralSequent : IsLiteralSequent sequent

open LiteralSequent public

open import OscarPrelude

private
  module _ where

    pattern ⟪_,_⟫ h s = ⟨_⟩ {h} s
    pattern ⟪_⟫ h = (⟨_⟩ {h} _)

instance EqLiteralSequent : Eq LiteralSequent
Eq._==_ EqLiteralSequent ⟪ Φ₁ ⟫ ⟪ Φ₂ ⟫   with Φ₁ ≟ Φ₂
Eq._==_ EqLiteralSequent ⟨ !Φ₁ ⟩ ⟨ !Φ₂ ⟩ | yes refl with !Φ₁ ≟ !Φ₂
Eq._==_ EqLiteralSequent _ _             | yes refl | yes refl = yes refl
Eq._==_ EqLiteralSequent ⟨ Φ₁ ⟩ ⟨ Φ₂ ⟩   | yes refl | no !Φ₁≢!Φ₂ = no λ {refl → !Φ₁≢!Φ₂ refl}
Eq._==_ EqLiteralSequent ⟨ Φ₁ ⟩ ⟨ Φ₂ ⟩   | no Φ₁≢Φ₂ = no λ {refl → Φ₁≢Φ₂ refl}

module _ where

  open import HasNegation
  open import IsLiteralFormula

  instance HasNegationLiteralSequent : HasNegation LiteralSequent
  HasNegation.~ HasNegationLiteralSequent ⟨ atomic 𝑃 τs ╱ φˢs ⟩ = ⟨ logical 𝑃 τs ╱ φˢs ⟩
  HasNegation.~ HasNegationLiteralSequent ⟨ logical 𝑃 τs ╱ φˢs ⟩ = ⟨ atomic 𝑃 τs ╱ φˢs ⟩

open import 𝓐ssertion

instance 𝓐ssertionLiteralSequent : 𝓐ssertion LiteralSequent
𝓐ssertionLiteralSequent = record {}

open import HasSatisfaction

instance HasSatisfactionLiteralSequent : HasSatisfaction LiteralSequent
HasSatisfaction._⊨_ HasSatisfactionLiteralSequent I Φ = I ⊨ sequent Φ

open import HasDecidableValidation

instance HasDecidableValidationLiteralSequent : HasDecidableValidation LiteralSequent
HasDecidableValidationLiteralSequent = {!!}
