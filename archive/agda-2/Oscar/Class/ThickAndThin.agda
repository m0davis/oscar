
module Oscar.Class.ThickAndThin where

open import Oscar.Data.Fin
open import Oscar.Data.Equality
open import Oscar.Data.Nat
open import Oscar.Data.Maybe

record ThickAndThin {a} (A : Nat → Set a) : Set a where
  field
    thin : ∀ {m} → Fin (suc m) → A m → A (suc m)
    thin-injective : ∀ {m} (x : Fin (suc m)) {y₁ y₂ : A m} → thin x y₁ ≡ thin x y₂ → y₁ ≡ y₂
    thick : ∀ {m} → A (suc m) → Fin m → A m
    thick∘thin=id : ∀ {m} (x : Fin m) (y : A m) → thick (thin (suc x) y) x ≡ y
    check : ∀ {m} → Fin (suc m) → A (suc m) → Maybe (A m)
    thin-check-id : ∀ {m} (x : Fin (suc m)) y → ∀ y' → thin x y' ≡ y → check x y ≡ just y'

open ThickAndThin ⦃ … ⦄ public

-- open import Oscar.Level

-- record ThickAndThin' {a} {A : Set a} (f : A → A) {b} (B : A → Set b) (g : ∀ {x} → B x → B (f x)) {c} (C : A → Set c) : Set (a ⊔ b ⊔ c) where
--   field
--     thin : ∀ {n} → B (f n) → C n → C (f n)
--     thick : ∀ {n} → C (f n) → B n → C n
--     thin-injective : ∀ {n} (z : B (f n)) {x y : C n} → thin z x ≡ thin z y → x ≡ y
--     thick∘thin=id : ∀ {n} (x : B n) (y : C n) → thick (thin (g x) y) x ≡ y
--     check : ∀ {n} → B (f n) → C (f n) → Maybe (C n)
--     thin-check-id : ∀ {n} (x : B (f n)) y → ∀ y' → thin x y' ≡ y → check x y ≡ just y'

-- --open ThickAndThin' ⦃ … ⦄ public
