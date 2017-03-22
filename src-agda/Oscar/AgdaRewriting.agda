{-# OPTIONS --rewriting #-}
module Oscar.AgdaRewriting where

open import Agda.Builtin.Equality

{-# BUILTIN REWRITE _≡_ #-}

record ⊤ : Set where
  constructor tt

data List (A : Set) : Set where
  ∅ : List A
  _∷_ : A → List A → List A

Nat = List ⊤
pattern ‼ xs = tt ∷ xs
syntax ‼ xs = ! xs

open import Agda.Builtin.Nat renaming (Nat to ℕ)

postulate
  Nat≡ℕ : Nat ≡ ℕ

{-# REWRITE Nat≡ℕ #-}

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
