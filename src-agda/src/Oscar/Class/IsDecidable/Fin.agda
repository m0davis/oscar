
open import Oscar.Prelude
open import Oscar.Class
open import Oscar.Data

module Oscar.Class.IsDecidable.Fin where

instance

  IsDecidableFin : ∀ {n} → IsDecidable (Fin n)
  IsDecidableFin .IsDecidable._≟_ ∅ ∅ = ↑ ∅
  IsDecidableFin .IsDecidable._≟_ ∅ (↑ _) = ↓ λ ()
  IsDecidableFin .IsDecidable._≟_ (↑ _) ∅ = ↓ λ ()
  IsDecidableFin .IsDecidable._≟_ (↑ x) (↑ y) with x ≟ y
  … | ↑ ∅ = ↑ ∅
  … | ↓ x≢y = ↓ λ {∅ → x≢y ∅}
