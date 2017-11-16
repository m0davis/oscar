
open import Oscar.Prelude

module Oscar.Data.Maybe where

data Maybe {a} (A : Ø a) : Ø a where
  ∅ : Maybe A
  ↑_ : A → Maybe A

-- A dependent eliminator.

maybe : ∀ {a b} {A : Set a} {B : Maybe A → Set b} →
        ((x : A) → B (↑ x)) → B ∅ → (x : Maybe A) → B x
maybe j n (↑ x) = j x
maybe j n ∅  = n

-- A non-dependent eliminator.

maybe′ : ∀ {a b} {A : Set a} {B : Set b} → (A → B) → B → Maybe A → B
maybe′ = maybe
