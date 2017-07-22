
open import Oscar.Prelude
open import Oscar.Class.[ExtensibleType]
open import Oscar.Data

module Oscar.Class.[ExtensibleType].Proposequality where

instance

  [ExtensibleType]Proposequality : ∀ {a} {b} {A : Set a} {B : A → Set b} → [ExtensibleType] (λ {w} → Proposequality⟦ B w ⟧)
  [ExtensibleType]Proposequality = ∁
