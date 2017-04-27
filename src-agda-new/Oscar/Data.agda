
module Oscar.Data where

open import Agda.Builtin.Unit
open import Oscar.Function
open import Oscar.Level

infixr 20 ∷_
infixr 20 _∷_

data NAT : Set where
  ∅ : NAT
  ∷_ : NAT → NAT

testNAT : NAT
testNAT = ∷ ∷ ∷ ∅

-- List
data ⟦_⟧ {a} (A : Set a) : Set a where
  ∅ : ⟦ A ⟧
  _∷_ : A → ⟦ A ⟧ → ⟦ A ⟧

-- Nat
⟦⟧ = ⟦ ⊤ ⟧

test⟦⟧ : ⟦⟧
test⟦⟧ = {!(tt ∷_) ∅ !}

infix 21 ¡_
pattern ¡_ ⟦A⟧ = tt ∷ ⟦A⟧
--¡ : ⟦⟧ → ⟦⟧
--¡ ⟦A⟧ = tt ∷ ⟦A⟧

-- Fin (with a payload)
data ⟦_⟧[_] {a} (A : ⟦⟧ → Set a) : ⟦⟧ → Set a where
  ∅ : ∀ {n} → ⟦ A ⟧[ ¡ n ]
  _∷_ : ∀ {n} → A n → ⟦ A ⟧[ n ] → ⟦ A ⟧[ ¡ n ]

⟦⟧[_] = ⟦ const ⊤ ⟧[_]

-- Vec (with an (optional) index)
data ⟦_⟧[_₀] {a} (A : ⟦⟧ → Set a) : ⟦⟧ → Set a where
  ∅ : ⟦ A ⟧[ ∅ ₀]
  _∷_ : ∀ {n} → A n → ⟦ A ⟧[ n ₀] → ⟦ A ⟧[ ¡ n ₀]

⟦⟧[_₀] = ⟦ const ⊤ ⟧[_₀]

-- m ≤ n, counting down from n-1 to m
data ⟦_⟧[_≤_↓] {a} (A : ⟦⟧ → Set a) (m : ⟦⟧) : ⟦⟧ → Set a where
  ∅ : ⟦ A ⟧[ m ≤ m ↓]
  _∷_ : ∀ {n} → A n → ⟦ A ⟧[ m ≤ n ↓] → ⟦ A ⟧[ m ≤ ¡ n ↓]

⟦⟧[_≤_↓] = ⟦ const ⊤ ⟧[_≤_↓]

-- m ≤ n, counting up from m to n-1
data ⟦_⟧[↑_≤_] {a} (A : ⟦⟧ → Set a) (m : ⟦⟧) : ⟦⟧ → Set a where
  ∅ : ⟦ A ⟧[↑ m ≤ m ]
  _∷_ : ∀ {n} → A m → ⟦ A ⟧[↑ ¡ m ≤ n ] → ⟦ A ⟧[↑ m ≤ n ]

⟦⟧[↑_≤_] = ⟦ const ⊤ ⟧[↑_≤_]

-- Inj (almost)
data ⟦_⟧[↓_≤_↓] {a} (A : ⟦⟧ → ⟦⟧ → Set a) : ⟦⟧ → ⟦⟧ → Set a where
  ∅ : ∀ {n} → ⟦ A ⟧[↓ ∅ ≤ n ↓]
  _∷_ : ∀ {m n} → A m n → ⟦ A ⟧[↓ m ≤ n ↓] → ⟦ A ⟧[↓ ¡ m ≤ ¡ n ↓]

⟦⟧[↓_≤_↓] = ⟦ const const ⊤ ⟧[↓_≤_↓]

infix 21 ‼_
pattern ‼_ ⟦A⟧ = tt ∷ ⟦A⟧ -- tricky, works for all above _∷_ constructors only because it is defined afterwards, won't work for any later-defined constructors

{-

Function (B m → B n)

Fin
Term
AList (SubstitutionList) Substilist
Step
List

FinTerm (SubstitutionFunction) Substifunction

SubstitutionFunction.internal
SubstitutionFunction.Morphism
SubstitutionFunction.IsSemigroupoid
SubstitutionFunction.IsCategory

IsSemigroupoid
IsCategory



-}
--Nat = ⟦⟧
--Vec :

-- mutual

--   Terms : Nat → Nat → Set 𝔣
--   Terms N m = Vec (Term m) N

--   data Term (m : Nat) : Set 𝔣 where
--     i : (x : Fin m) → Term m
--     leaf : Term m
--     _fork_ : (s t : Term m) → Term m
--     function : FunctionName → ∀ {N} → Terms N m → Term m
