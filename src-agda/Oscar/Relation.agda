
module Oscar.Relation where

open import Oscar.Level

_⟨_⟩→_ : ∀ {a} {A : Set a} {b} → A → (A → Set b) → A → Set b
m ⟨ B ⟩→ n = B m → B n
