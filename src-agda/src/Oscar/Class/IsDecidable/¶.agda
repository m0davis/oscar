
open import Oscar.Prelude
open import Oscar.Class
open import Oscar.Data

module Oscar.Class.IsDecidable.¶ where

instance

  IsDecidable¶ : IsDecidable ¶
  IsDecidable¶ .IsDecidable._≟_ ∅ ∅ = ↑ ∅
  IsDecidable¶ .IsDecidable._≟_ ∅ (↑ _) = ↓ λ ()
  IsDecidable¶ .IsDecidable._≟_ (↑ _) ∅ = ↓ λ ()
  IsDecidable¶ .IsDecidable._≟_ (↑ x) (↑ y) with x ≟ y
  … | ↑ ∅ = ↑ ∅
  … | ↓ x≢y = ↓ λ {∅ → x≢y ∅}
