module Scratch where

open import Agda.Builtin.List
open import Agda.Builtin.Nat
open import Agda.Builtin.Equality
open import Prelude

[sucNat]+zero=sucNat : ∀ {n} → suc n +N zero ≡ suc n
[sucNat]+zero=sucNat {zero} = refl
[sucNat]+zero=sucNat {(suc n)} = cong suc [sucNat]+zero=sucNat

data ℕ : Set where
  z : ℕ
  s : ℕ → ℕ

toNat : ℕ → Nat
toNat z = zero
toNat (s x) = suc (toNat x)

toℕ : Nat → ℕ
toℕ zero = z
toℕ (suc x) = s (toℕ x)

_+ℕ_ : ℕ → ℕ → ℕ
x +ℕ x₁ = toℕ (toNat x +N toNat x₁)

ℕ-Nat-ℕ-refl : ∀ {n} → toℕ (toNat n) ≡ n
ℕ-Nat-ℕ-refl {z} = refl
ℕ-Nat-ℕ-refl {s n} = cong s ℕ-Nat-ℕ-refl

[sℕ]+z=sℕ : ∀ {n} → s n +ℕ z ≡ s n
[sℕ]+z=sℕ = cong toℕ [sucNat]+zero=sucNat ⟨≡⟩ cong s ℕ-Nat-ℕ-refl
