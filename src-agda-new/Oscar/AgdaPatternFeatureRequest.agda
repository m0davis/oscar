
module Oscar.AgdaPatternFeatureRequest where

open import Agda.Builtin.Equality

record ⊤ : Set where
  constructor tt

data List (A : Set) : Set where
  ∅ : List A
  _∷_ : A → List A → List A

Nat = List ⊤
pattern ‼ xs = tt ∷ xs
syntax ‼ xs = ! xs

data Fin : Nat → Set where
  ∅ : ∀ {n} → Fin (! n)
  ! : ∀ {n} → Fin n → Fin (! n)

-- record ⊤ : Set where
--   constructor tt

-- data List (A : Set) : Set where
--   ∅ : List A
--   _∷_ : A → List A → List A

-- Nat = List ⊤
-- pattern ‼ xs = tt ∷ xs

-- data Fin : Nat → Set where
--   ∅ : ∀ {n} → Fin (‼ n)
--   ! : ∀ {n} → Fin n → Fin (‼ n)
