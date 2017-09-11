{-# OPTIONS --show-implicit #-}

module AgdaFeatureTerminationViaExplicitness where

data Nat : Set where
  zero : Nat
  suc  : (n : Nat) → Nat

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

test-works1 : ∀ {n} → Pat n → Cat n → Cat n
test-works1 (psuc t) acc = down (up (test-works1 t))
test-works1 t cat = up (test-works1 (rectify-works t))

{-# TERMINATING #-}
test-fails2 : ∀ {n} → Pat n → Cat n → Cat n
test-fails2 (psuc t) acc = down (up (test-fails2 t))
test-fails2 t cat = up (test-fails2 (rectify-fails t))

test-works3 : ∀ {n} → Pat n → Cat n → Cat n
test-works3 (psuc t) cat = down (up (test-works3 t))
test-works3 t@pzero (cat {n = n}) = up (test-works3 {n = n} (rectify-fails t))
