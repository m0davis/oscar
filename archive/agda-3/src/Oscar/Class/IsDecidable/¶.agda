
open import Oscar.Prelude
open import Oscar.Class.IsDecidable
open import Oscar.Data.¶
open import Oscar.Data.Decidable
open import Oscar.Data.Proposequality

module Oscar.Class.IsDecidable.¶ where

instance

  IsDecidable¶ : IsDecidable ¶
  IsDecidable¶ .IsDecidable._≟_ ∅ ∅ = ↑ ∅
  IsDecidable¶ .IsDecidable._≟_ ∅ (↑ _) = ↓ λ ()
  IsDecidable¶ .IsDecidable._≟_ (↑ _) ∅ = ↓ λ ()
  IsDecidable¶ .IsDecidable._≟_ (↑ x) (↑ y) with x ≟ y
  … | ↑ ∅ = ↑ ∅
  … | ↓ x≢y = ↓ λ {∅ → x≢y ∅}
