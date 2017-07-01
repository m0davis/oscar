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

open import Agda.Builtin.Nat using (zero; suc) renaming (Nat to ℕ; _+_ to _+ℕ_)

toNat : ℕ → Nat
toNat zero = ∅
toNat (suc x) = tt ∷ toNat x

toℕ : Nat → ℕ
toℕ ∅ = zero
toℕ (x ∷ x₁) = suc (toℕ x₁)

ℕ-iso : ∀ n → toℕ (toNat n) ≡ n
ℕ-iso zero = refl
ℕ-iso (suc n) rewrite ℕ-iso n = refl

Nat-iso : ∀ n → toNat (toℕ n) ≡ n
Nat-iso ∅ = refl
Nat-iso (x ∷ n) rewrite Nat-iso n = refl

--{-# REWRITE ℕ-iso #-}

infixl 6 _+Nat_
_+Nat_ : Nat → Nat → Nat
m +Nat n = toNat (toℕ m +ℕ toℕ n)

infixl 7 _*Nat_
_*Nat_ : Nat → Nat → Nat
∅ *Nat _ = ∅
_ *Nat ∅ = ∅
(_ ∷ m) *Nat (_ ∷ n) = _ ∷ m +Nat n +Nat m *Nat n

NatComputation : Nat
NatComputation = toNat 5 *Nat toNat 7

butnowinℕ : ℕ
butnowinℕ = toℕ NatComputation

showme : ℕ
showme = {!!}

-- postulate
--   Nat≡ℕ : Nat ≡ ℕ

-- {-# REWRITE Nat≡ℕ #-}

-- data Fin : Nat → Set where
--   ∅ : ∀ {n} → Fin (! n)
--   ! : ∀ {n} → Fin n → Fin (! n)

-- -- record ⊤ : Set where
-- --   constructor tt

-- -- data List (A : Set) : Set where
-- --   ∅ : List A
-- --   _∷_ : A → List A → List A

-- -- Nat = List ⊤
-- -- pattern ‼ xs = tt ∷ xs

-- -- data Fin : Nat → Set where
-- --   ∅ : ∀ {n} → Fin (‼ n)
-- --   ! : ∀ {n} → Fin n → Fin (‼ n)
