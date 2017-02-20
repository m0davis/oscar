
data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

data Pos : ℕ → Set where
  n⁺z : Pos (succ zero)
  n⁺ss : ∀ n → Pos n → Pos (succ (succ n))
  n⁺sss : ∀ n → Pos n → Pos (succ (succ (succ n)))

data ℕ¹ : Set where
  one : ℕ¹
  double : ℕ¹ → ℕ¹
  double+1 : ℕ¹ → ℕ¹

data ℕ² : Set where
  zero : ℕ²
  pos : ℕ¹ → ℕ²

conv¹⟶ : ℕ¹ → ℕ
conv¹⟶ one = succ zero
conv¹⟶ (double n) = succ (succ (conv¹⟶ n))
conv¹⟶ (double+1 n) = succ (succ (succ (conv¹⟶ n)))

conv²⟶ : ℕ² → ℕ
conv²⟶ zero = zero
conv²⟶ (pos n) = conv¹⟶ n

data ⊥ : Set where

¬_ : ∀ {ℓ} → Set ℓ → Set ℓ
¬ P = P → ⊥

data Dec {p} (P : Set p) : Set p where
  yes : (p : P) → Dec P
  no  : (¬p : ¬ P) → Dec P

open import Relation.Nullary.Negation

isPos? : (n : ℕ) → Dec (Pos n)
isPos? zero = no (λ ())
isPos? (succ zero) = yes n⁺z
isPos? (succ (succ n')) with isPos? n'
... | yes p = yes (n⁺ss n' p)
... | no ¬p = no (λ x → {!!}) where
  

conv²⟵ : ℕ → ℕ²
conv²⟵ zero = zero
conv²⟵ n = pos ({!!})
