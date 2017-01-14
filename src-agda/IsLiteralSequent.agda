
module IsLiteralSequent where

open import OscarPrelude
open import Sequent
open import IsLiteralFormula

record IsLiteralSequent (Φ : Sequent) : Set
 where
  constructor _╱_
  field
    isLiteralStatement : IsLiteralFormula (statement Φ)
    isLiteralSuppositions : All IsLiteralFormula (suppositions Φ)

open IsLiteralSequent public

instance EqIsLiteralSequent : ∀ {Φ} → Eq (IsLiteralSequent Φ)
Eq._==_ EqIsLiteralSequent ( φᵗ₁ ╱ φˢs₁ ) ( φᵗ₂ ╱ φˢs₂ ) = decEq₂ (cong isLiteralStatement) (cong isLiteralSuppositions) (φᵗ₁ ≟ φᵗ₂) (φˢs₁ ≟ φˢs₂)
