{- revised nomenclature -}
module Oscar.Data4 where

record ⊤ : Set where
  constructor tt

Const_ : ∀ {a} {A : Set a} {b} {B : Set b} → B → A → B
Const_ x _ = x

infixr 20 _∷_

-- List
data ⟦_⟧ {a} (A : Set a) : Set a where
  ∅ : ⟦ A ⟧
  _∷_ : A → ⟦ A ⟧ → ⟦ A ⟧

-- Nat
⟦⟧ = ⟦ ⊤ ⟧

infix 21 ¡_
pattern ¡_ ⟦A⟧ = tt ∷ ⟦A⟧
--¡ : ⟦⟧ → ⟦⟧
--¡ ⟦A⟧ = tt ∷ ⟦A⟧

-- Fin (with a payload)
data ⟦_⟧[_] {a} (A : ⟦⟧ → Set a) : ⟦⟧ → Set a where
  ∅ : ∀ {n} → ⟦ A ⟧[ ¡ n ]
  _∷_ : ∀ {n} → A n → ⟦ A ⟧[ n ] → ⟦ A ⟧[ ¡ n ]

⟦⟧[_] = ⟦ Const ⊤ ⟧[_]

-- Vec (with an (optional) index)
data ⟦_⟧[_₀] {a} (A : ⟦⟧ → Set a) : ⟦⟧ → Set a where
  ∅ : ⟦ A ⟧[ ∅ ₀]
  _∷_ : ∀ {n} → A n → ⟦ A ⟧[ n ₀] → ⟦ A ⟧[ ¡ n ₀]

⟦⟧[_₀] = ⟦ Const ⊤ ⟧[_₀]

-- m ≤ n, counting down from n-1 to m
data ⟦_⟧[_≤_↓] {a} (A : ⟦⟧ → Set a) (m : ⟦⟧) : ⟦⟧ → Set a where
  ∅ : ⟦ A ⟧[ m ≤ m ↓]
  _∷_ : ∀ {n} → A n → ⟦ A ⟧[ m ≤ n ↓] → ⟦ A ⟧[ m ≤ ¡ n ↓]

⟦⟧[_≤_↓] = ⟦ Const ⊤ ⟧[_≤_↓]

-- m ≤ n, counting up from m to n-1
data ⟦_⟧[↑_≤_] {a} (A : ⟦⟧ → Set a) (m : ⟦⟧) : ⟦⟧ → Set a where
  ∅ : ⟦ A ⟧[↑ m ≤ m ]
  _∷_ : ∀ {n} → A m → ⟦ A ⟧[↑ ¡ m ≤ n ] → ⟦ A ⟧[↑ m ≤ n ]

⟦⟧[↑_≤_] = ⟦ Const ⊤ ⟧[↑_≤_]

-- Inj (almost)
data ⟦_⟧[↓_≤_↓] {a} (A : ⟦⟧ → ⟦⟧ → Set a) : ⟦⟧ → ⟦⟧ → Set a where
  ∅ : ∀ {n} → ⟦ A ⟧[↓ ∅ ≤ n ↓]
  _∷_ : ∀ {m n} → A m n → ⟦ A ⟧[↓ m ≤ n ↓] → ⟦ A ⟧[↓ ¡ m ≤ ¡ n ↓]

⟦⟧[↓_≤_↓] = ⟦ Const Const ⊤ ⟧[↓_≤_↓]

infix 21 ‼_
pattern ‼_ ⟦A⟧ = tt ∷ ⟦A⟧ -- tricky, works for all above _∷_ constructors only because it is defined afterwards, won't work for any later-defined constructors

testNat : ⟦⟧
testNat = ¡ ∅

testListNat : ⟦ ⟦⟧ ⟧
testListNat = ¡ ∅ ∷ ‼ ∅ ∷ ‼ ‼ ∅ ∷ ∅ ∷ ¡ ¡ ¡ ∅ ∷ ∅

testFin : ⟦⟧[ ¡ ¡ ∅ ]
testFin = ‼ ∅

test≤↓ : ⟦⟧[ ‼ ‼ ‼ ∅ ≤ ‼ ‼ ‼ ‼ ‼ ∅ ↓]
test≤↓ = ‼ ‼ ∅

⓪ ⑴ ⑵ : ⟦⟧
⓪ = ∅
⑴ = ‼ ∅
⑵ = ‼ ⑴
