{-# OPTIONS --show-implicit #-}
module Oscar.TerminationBughunt7 where

open import Agda.Builtin.Nat

id : {A : Set} → A → A
id = λ x → x

data Pat (n : Nat) : Set where
  pzero : Pat n
  psuc : Pat n → Pat n

data Cat : Nat → Set where
  cat : ∀ {n} → Cat (suc n)

postulate
  up : ∀ {n} → (Cat n → Cat n) → Cat (suc n)
  down : ∀ {n} → Cat (suc n) → Cat n
  rectify-works : ∀ {x y} → Pat x → Pat y
  rectify-fails : ∀ {x y} → Pat x → Pat (id y)

test-works : ∀ {n} → Pat n → Cat n → Cat n
test-works (psuc t) acc = down (up (test-works t))
test-works t cat = up (test-works (rectify-works t))

test-fails : ∀ {n} → Pat n → Cat n → Cat n
test-fails (psuc t) acc = down (up (test-fails t))
test-fails t cat = up (test-fails (rectify-fails t))

test-fails' : ∀ {n} → Pat n → Cat n → Cat n
test-fails' {.(suc n₁)} (psuc t) (cat {n = n₁}) = down (up (test-fails' t))
test-fails' {.(suc n₁)} t@pzero (cat {n = n₁}) = up (test-fails' {n = n₁} (rectify-fails t))
