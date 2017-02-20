{-# OPTIONS --allow-unsolved-metas #-}
module Formula where

module _ where

  open import VariableName
  open import PredicateName
  open import Term

  data Formula : Set
   where
    atomic : PredicateName → Terms → Formula
    logical : Formula →
              Formula →
              Formula
    quantified : VariableName → Formula → Formula

module _ where

  open import OscarPrelude

  formulaAtomic-inj₁ : ∀ {𝑃₁ τs₁ 𝑃₂ τs₂} → atomic 𝑃₁ τs₁ ≡ atomic 𝑃₂ τs₂ → 𝑃₁ ≡ 𝑃₂
  formulaAtomic-inj₁ refl = refl

  formulaAtomic-inj₂ : ∀ {𝑃₁ τs₁ 𝑃₂ τs₂} → atomic 𝑃₁ τs₁ ≡ atomic 𝑃₂ τs₂ → τs₁ ≡ τs₂
  formulaAtomic-inj₂ refl = refl

  formulaLogical-inj₁ : ∀ {φ₁₁ φ₁₂ φ₂₁ φ₂₂} → logical φ₁₁ φ₁₂ ≡ logical φ₂₁ φ₂₂ → φ₁₁ ≡ φ₂₁
  formulaLogical-inj₁ refl = refl

  formulaLogical-inj₂ : ∀ {φ₁₁ φ₁₂ φ₂₁ φ₂₂} → logical φ₁₁ φ₁₂ ≡ logical φ₂₁ φ₂₂ → φ₁₂ ≡ φ₂₂
  formulaLogical-inj₂ refl = refl

  formulaQuantified-inj₁ : ∀ {𝑥₁ φ₁ 𝑥₂ φ₂} → quantified 𝑥₁ φ₁ ≡ quantified 𝑥₂ φ₂ → 𝑥₁ ≡ 𝑥₂
  formulaQuantified-inj₁ refl = refl

  formulaQuantified-inj₂ : ∀ {𝑥₁ φ₁ 𝑥₂ φ₂} → quantified 𝑥₁ φ₁ ≡ quantified 𝑥₂ φ₂ → φ₁ ≡ φ₂
  formulaQuantified-inj₂ refl = refl

  instance EqFormula : Eq Formula
  Eq._==_ EqFormula (atomic 𝑃₁ τs₁)
                    (atomic 𝑃₂ τs₂)
                    = decEq₂ formulaAtomic-inj₁
                             formulaAtomic-inj₂
                             (𝑃₁ ≟ 𝑃₂)
                             (τs₁ ≟ τs₂)
  Eq._==_ EqFormula (logical φ₁₁ φ₁₂)
                    (logical φ₂₁ φ₂₂)
                    = decEq₂ formulaLogical-inj₁ formulaLogical-inj₂ (φ₁₁ ≟ φ₂₁) (φ₁₂ ≟ φ₂₂)
  Eq._==_ EqFormula (quantified 𝑥₁ φ₁) (quantified 𝑥₂ φ₂) = decEq₂ formulaQuantified-inj₁ formulaQuantified-inj₂ (𝑥₁ ≟ 𝑥₂) (φ₁ ≟ φ₂)
  Eq._==_ EqFormula (atomic _ _) (logical _ _) = no λ ()
  Eq._==_ EqFormula (atomic _ _) (quantified _ _) = no λ ()
  Eq._==_ EqFormula (logical _ _) (atomic _ _) = no λ ()
  Eq._==_ EqFormula (logical _ _) (quantified _ _) = no λ ()
  Eq._==_ EqFormula (quantified _ _) (atomic _ _) = no λ ()
  Eq._==_ EqFormula (quantified _ _) (logical _ _) = no λ ()

module _ where

  open import PredicateName
  open import Term

  𝑃[_♭_] : PredicateName → Terms → Formula
  𝑃[_♭_] = atomic

  {-# DISPLAY atomic = 𝑃[_♭_] #-}

module _ where

  open import HasNeitherNor

  instance HasNeitherNorFormula : HasNeitherNor Formula
  HasNeitherNor._⊗_ HasNeitherNorFormula = logical

  {-# DISPLAY logical = _⊗_ #-}

module _ where

  open import HasNeitherNor
  open import HasNegation

  instance HasNegationFormula : HasNegation Formula
  HasNegation.~ HasNegationFormula φ = φ ⊗ φ

module _ where

  open import OscarPrelude
  open import Term
  open import HasSatisfaction
  open import Interpretation
  open import Vector
  open import InterpretationEqualityExceptAtVariableName
  open import Elements
  open import TruthValue

  instance HasSatisfactionFormula : HasSatisfaction Formula
  HasSatisfaction._⊨_ HasSatisfactionFormula I (atomic 𝑃 τs) = 𝑃⟦ I ⟧ 𝑃 ⟨ ⟨ τ⟦ I ⟧ <$> vector (terms τs) ⟩ ⟩ ≡ ⟨ true ⟩
  HasSatisfaction._⊨_ HasSatisfactionFormula I (logical φ₁ φ₂) = ¬ I ⊨ φ₁ × ¬ I ⊨ φ₂
  HasSatisfaction._⊨_ HasSatisfactionFormula I (quantified 𝑥 φ) = (𝓘 : Interpretation) → 𝓘 ≞ I / 𝑥 → 𝓘 ⊨ φ

  instance HasDecidableSatisfactionFormula : HasDecidableSatisfaction Formula
  HasDecidableSatisfaction._⊨?_ HasDecidableSatisfactionFormula I (atomic 𝑃 τs) = {!!}
  HasDecidableSatisfaction._⊨?_ HasDecidableSatisfactionFormula I (logical φ₁ φ₂) = {!!}
  HasDecidableSatisfaction._⊨?_ HasDecidableSatisfactionFormula I (quantified 𝑥 φ) = {!!}

  instance HasDecidableValidationFormula : HasDecidableValidation Formula
  HasDecidableValidation.⊨?_ HasDecidableValidationFormula (atomic 𝑃 τs) = {!!}
  HasDecidableValidation.⊨?_ HasDecidableValidationFormula (logical φ₁ φ₂) = {!!}
  HasDecidableValidation.⊨?_ HasDecidableValidationFormula (quantified 𝑥 φ) = {!!}

module _ where

  open import OscarPrelude
  open import Relation.Binary.Core
  --open import PredicateName
  open import VariableName
  open import Arity
  open import Term
  open import Vector

  mutual

    notationalVariantTerm* : (VariableName → Maybe VariableName) → Term → Term → Set
    notationalVariantTerm* v (variable 𝑥₁) (variable 𝑥₂) = maybe 𝑥₁ id (v 𝑥₁) ≡ 𝑥₂
    notationalVariantTerm* v (function 𝑓₁ τs₁) (function 𝑓₂ τs₂) = 𝑓₁ ≡ 𝑓₂ × notationalVariantTerms* v τs₁ τs₂
    notationalVariantTerm* v (variable x) (function x₁ x₂) = ⊥
    notationalVariantTerm* v (function x x₁) (variable x₂) = ⊥

    notationalVariantTerms* : (VariableName → Maybe VariableName) → Terms → Terms → Set
    notationalVariantTerms* v (⟨_⟩ {a₁} terms₁) (⟨_⟩ {a₂} terms₂) with a₁ ≟ a₂
    notationalVariantTerms* v (⟨_⟩ {⟨ .0 ⟩} ⟨ [] ⟩) (⟨_⟩ {.(⟨ 0 ⟩)} ⟨ [] ⟩) | yes refl = ⊤
    notationalVariantTerms* v (⟨_⟩ {⟨ .(suc _) ⟩} ⟨ x ∷ vector₁ ⟩) (⟨_⟩ {.(⟨ suc _ ⟩)} ⟨ x₁ ∷ vector₂ ⟩) | yes refl = notationalVariantTerm* v x x₁ × notationalVariantTerms* v ⟨ ⟨ vector₁ ⟩ ⟩ ⟨ ⟨ vector₂ ⟩ ⟩
    … | no neq = ⊥

  mutual

    data Term⟦_/_≈_⟧ (v : VariableName → Maybe VariableName) : Term → Term → Set where
      variable : ∀ 𝑥₁ 𝑥₂ → maybe 𝑥₁ id (v 𝑥₁) ≡ 𝑥₂ → Term⟦ v / variable 𝑥₁ ≈ variable 𝑥₂ ⟧
      function : ∀ 𝑓 τs₁ τs₂ → Terms⟦ v / τs₁ ≈ τs₂ ⟧ → Term⟦ v / function 𝑓 τs₁ ≈ function 𝑓 τs₂ ⟧

    data Terms⟦_/_≈_⟧ (v : VariableName → Maybe VariableName) : Terms → Terms → Set where
      [] : Terms⟦ v / ⟨ ⟨ [] ⟩ ⟩ ≈ ⟨ ⟨ [] ⟩ ⟩ ⟧
      _∷_ : ∀ τ₁ τ₂ → Term⟦ v / τ₁ ≈ τ₂ ⟧ → ∀ τs₁ τs₂ → Terms⟦ v / τs₁ ≈ τs₂ ⟧ → Terms⟦ v / ⟨ ⟨ τ₁ ∷ vector (terms τs₁) ⟩ ⟩ ≈ ⟨ ⟨ τ₂ ∷ vector (terms τs₂) ⟩ ⟩ ⟧

  notationalVariantFormula* : (VariableName → Maybe VariableName) → Formula → Formula → Set
  notationalVariantFormula* v (atomic x x₁) (atomic x₂ x₃) = x ≡ x₂ × notationalVariantTerms* v x₁ x₃
  notationalVariantFormula* v (logical φ₁ φ₂) (logical φ₃ φ₄) = notationalVariantFormula* v φ₁ φ₃ × notationalVariantFormula* v φ₂ φ₄
  notationalVariantFormula* v (quantified x φ₁) (quantified x₁ φ₂) = notationalVariantFormula* (λ {v' → ifYes v' ≟ x then just x₁ else v v'}) φ₁ φ₂
  notationalVariantFormula* v (logical φ₁ φ₂) (atomic x x₁) = ⊥
  notationalVariantFormula* v (atomic x x₁) (logical φ₂ φ₃) = ⊥
  notationalVariantFormula* v (atomic x x₁) (quantified x₂ φ₂) = ⊥
  notationalVariantFormula* v (logical φ₁ φ₂) (quantified x φ₃) = ⊥
  notationalVariantFormula* v (quantified x φ₁) (atomic x₁ x₂) = ⊥
  notationalVariantFormula* v (quantified x φ₁) (logical φ₂ φ₃) = ⊥

  notationalVariantFormula : Formula → Formula → Set
  notationalVariantFormula φ₁ φ₂ = notationalVariantFormula* (const nothing) φ₁ φ₂

  private

    refl-notationalVariantTerms* : ∀ x₁ → notationalVariantTerms* (λ x₂ → nothing) ⟨ terms x₁ ⟩ ⟨ terms x₁ ⟩
    refl-notationalVariantTerms* (⟨_⟩ {arity = ⟨ .0 ⟩} ⟨ [] ⟩) = {!!}
    refl-notationalVariantTerms* (⟨_⟩ {arity = ⟨ .(suc _) ⟩} ⟨ _∷_ {n = n} x vector₁ ⟩) = {!!}
    {-
    refl-notationalVariantTerms* ⟨ ⟨ [] ⟩ ⟩ = tt
    refl-notationalVariantTerms* (⟨_⟩ {nx} ⟨ x ∷ vector₁ ⟩) = {!!}
    -}

    refl-notationalVariantFormula : (φ : Formula) → notationalVariantFormula φ φ
    refl-notationalVariantFormula (atomic x x₁) = {!!}
    refl-notationalVariantFormula (logical φ φ₁) = {!!}
    refl-notationalVariantFormula (quantified x φ) = {!!}

  isEquivalenceNotationalVariantFormula : IsEquivalence notationalVariantFormula
  isEquivalenceNotationalVariantFormula =
    record
    { refl = {!!} -- λ { {atomic _ _} → refl , {!!} ; {logical x x₁} → {!!} ; {quantified x x₁} → {!!} }
    ; sym = {!!}
    ; trans = {!!} }

  data Formula⟦_/_≈_⟧ (v : VariableName → Maybe VariableName) : Formula → Formula → Set where
    atomic : ∀ 𝑃 τs₁ τs₂ → Terms⟦ v / τs₁ ≈ τs₂ ⟧ → Formula⟦ v / atomic 𝑃 τs₁ ≈ atomic 𝑃 τs₂ ⟧
    logical : ∀ φ₁₁ φ₁₂ φ₂₁ φ₂₂ → Formula⟦ v / φ₁₁ ≈ φ₂₁ ⟧ → Formula⟦ v / φ₁₂ ≈ φ₂₂ ⟧ → Formula⟦ v / logical φ₁₁ φ₁₂ ≈ logical φ₂₁ φ₂₂ ⟧
    quantified : ∀ 𝑥₁ 𝑥₂ φ₁ φ₂ → Formula⟦ (λ {v' → ifYes v' ≟ 𝑥₁ then just 𝑥₂ else v v'}) / φ₁ ≈ φ₂ ⟧ → Formula⟦ v / quantified 𝑥₁ φ₁ ≈ quantified 𝑥₂ φ₂ ⟧

  data F⟦_NotationalVariant_⟧ : Formula → Formula → Set where
    basic : ∀ φ₁ φ₂ → Formula⟦ const nothing / φ₁ ≈ φ₂ ⟧ → F⟦ φ₁ NotationalVariant φ₂ ⟧

  private

    mutual
      refl-notVarTerms : ∀ x₁ → Terms⟦ const nothing / x₁ ≈ x₁ ⟧
      refl-notVarTerms ⟨ ⟨ [] ⟩ ⟩ = []
      refl-notVarTerms ⟨ ⟨ x ∷ vector₁ ⟩ ⟩ = (x ∷ x) (refl-notVarTerm x) ⟨ ⟨ vector₁ ⟩ ⟩ ⟨ ⟨ vector₁ ⟩ ⟩ (refl-notVarTerms ⟨ ⟨ vector₁ ⟩ ⟩)

      refl-notVarTerm : ∀ x₁ → Term⟦ const nothing / x₁ ≈ x₁ ⟧
      refl-notVarTerm (variable x) = variable x x refl
      refl-notVarTerm (function x x₁) = function x x₁ x₁ (refl-notVarTerms x₁)

    refl-notationalVariant' : (φ : Formula) → F⟦ φ NotationalVariant φ ⟧
    refl-notationalVariant' (atomic x x₁) = basic 𝑃[ x ♭ x₁ ] 𝑃[ x ♭ x₁ ] (atomic x x₁ x₁ (refl-notVarTerms x₁))
    refl-notationalVariant' (logical φ φ₁) = basic (logical φ φ₁) (logical φ φ₁) (logical φ φ₁ φ φ₁ {!!} {!!})
    refl-notationalVariant' (quantified x φ) = basic (quantified x φ) (quantified x φ) (quantified x x φ φ {!!})

  isEquivalenceNotationalVariant' : IsEquivalence F⟦_NotationalVariant_⟧
  isEquivalenceNotationalVariant' =
    record
    { refl = {!!} -- λ { {atomic _ _} → refl , {!!} ; {logical x x₁} → {!!} ; {quantified x x₁} → {!!} }
    ; sym = {!!}
    ; trans = {!!} }

module _ where

  open import HasSubstantiveDischarge
{-
  postulate
    instance cs : CanonicalSubstitution Formula
    instance hpu : HasPairUnification Formula (CanonicalSubstitution.S cs)
-}
  instance HasSubstantiveDischargeFormulaFormula : HasSubstantiveDischarge Formula
  HasSubstantiveDischarge.hasNegation HasSubstantiveDischargeFormulaFormula = {!!}
  --HasSubstantiveDischarge._o≽o_ HasSubstantiveDischargeFormulaFormula φ₁ φ₂ = {!!} -- ∃ λ υ → υ Unifies φ₁ and φ₂
  HasSubstantiveDischarge.≽-reflexive HasSubstantiveDischargeFormulaFormula = {!!}
  HasSubstantiveDischarge.≽-consistent HasSubstantiveDischargeFormulaFormula = {!!}
  HasSubstantiveDischarge.≽-contrapositive HasSubstantiveDischargeFormulaFormula = {!!}

  instance HasDecidableSubstantiveDischargeFormulaFormula : HasDecidableSubstantiveDischarge Formula
  HasDecidableSubstantiveDischarge.hasSubstantiveDischarge HasDecidableSubstantiveDischargeFormulaFormula = {!!}
  HasDecidableSubstantiveDischarge._≽?_ HasDecidableSubstantiveDischargeFormulaFormula = {!!}

module _ where

  open import VariableName

  ∀[_♭_] : VariableName → Formula → Formula
  ∀[_♭_] = quantified

  {-# DISPLAY Formula.quantified = ∀[_♭_] #-}

module _ where

  open import HasNegation
  open import HasNeitherNor

  _∧_ : Formula → Formula → Formula
  φ₁ ∧ φ₂ = ~ φ₁ ⊗ ~ φ₂

  _∨_ : Formula → Formula → Formula
  φ₁ ∨ φ₂ = ~ (φ₁ ⊗ φ₂)

  _⊃_ : Formula → Formula → Formula
  φ₁ ⊃ φ₂ = ~ φ₁ ∨ φ₂

  _⟷_ : Formula → Formula → Formula
  φ₁ ⟷ φ₂ = (φ₁ ⊗ (φ₂ ⊗ φ₂)) ⊗ ((φ₁ ⊗ φ₁) ⊗ φ₂) -- TODO check that this is logically equivalent to the more verbose, (φ₁ ⊃ φ₂) ∧ (φ₂ ⊃ φ₁)
