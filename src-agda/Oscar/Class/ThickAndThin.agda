
module Oscar.Class.ThickAndThin where

open import Data.Fin using (Fin; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Maybe using (Maybe; nothing; just)

record ThickAndThin {a} (A : ℕ → Set a) : Set a where
  field
    thin : ∀ {n} → Fin (suc n) → A n → A (suc n)
    thick : ∀ {n} → A (suc n) → Fin n → A n
    thin-injective : ∀ {n} (z : Fin (suc n)) {x y : A n} → thin z x ≡ thin z y → x ≡ y
    thick∘thin=id : ∀ {n} (x : Fin n) (y : A n) → thick (thin (suc x) y) x ≡ y
    check : ∀ {n} → Fin (suc n) → A (suc n) → Maybe (A n)
    thin-check-id : ∀ {n} (x : Fin (suc n)) y -> ∀ y' -> thin x y' ≡ y -> check x y ≡ just y'

open ThickAndThin ⦃ … ⦄ public
