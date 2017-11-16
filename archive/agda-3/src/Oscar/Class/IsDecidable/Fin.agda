
open import Oscar.Prelude
open import Oscar.Class.IsDecidable
open import Oscar.Data.Fin
open import Oscar.Data.Decidable
open import Oscar.Data.Proposequality

module Oscar.Class.IsDecidable.Fin where

instance

  IsDecidableFin : ∀ {n} → IsDecidable (Fin n)
  IsDecidableFin .IsDecidable._≟_ ∅ ∅ = ↑ ∅
  IsDecidableFin .IsDecidable._≟_ ∅ (↑ _) = ↓ λ ()
  IsDecidableFin .IsDecidable._≟_ (↑ _) ∅ = ↓ λ ()
  IsDecidableFin .IsDecidable._≟_ (↑ x) (↑ y) with x ≟ y
  … | ↑ ∅ = ↑ ∅
  … | ↓ x≢y = ↓ λ {∅ → x≢y ∅}
