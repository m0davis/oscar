{- constructions on ℕ, everything I could think of that seemed interesting -}
-- "interesting"=?
-- maybe some of these should be discarded. e.g. ⟦⟧ is just an instance of ⟦_⟧, namely ⟦ ⊤ ⟧
-- maybe add a record version of ≤
-- categorise
-- what about ≡?
module Oscar.Data1 where

-- Nat
data ⟦⟧ : Set where
  ∅ : ⟦⟧
  ! : ⟦⟧ → ⟦⟧

-- List
data ⟦_⟧ {a} (A : Set a) : Set a where
  ∅ : ⟦ A ⟧
  _∷_ : A → ⟦ A ⟧ → ⟦ A ⟧

-- Fin
data ⟦⟧[_] : ⟦⟧ → Set where
  ∅ : ∀ {n} → ⟦⟧[ ! n ]
  ! : ∀ {n} → ⟦⟧[ n ] → ⟦⟧[ ! n ]

-- same, with payload
data ⟦_⟧[_] {a} (A : ⟦⟧ → Set a) : ⟦⟧ → Set a where
  ∅ : ∀ {n} → ⟦ A ⟧[ ! n ]
  _∷_ : ∀ {n} → A n → ⟦ A ⟧[ n ] → ⟦ A ⟧[ ! n ]

-- m ≤ n, counting down from n-1 to m
data ⟦⟧[_≤↓_] (m : ⟦⟧) : ⟦⟧ → Set where
  ∅ : ⟦⟧[ m ≤↓ m ]
  ! : ∀ {n} → ⟦⟧[ m ≤↓ n ] → ⟦⟧[ m ≤↓ ! n ]

-- same, with payload
data ⟦_⟧[_≤↓_] {a} (A : ⟦⟧ → Set a) (m : ⟦⟧) : ⟦⟧ → Set a where
  ∅ : ⟦ A ⟧[ m ≤↓ m ]
  _∷_ : ∀ {n} → A n → ⟦ A ⟧[ m ≤↓ n ] → ⟦ A ⟧[ m ≤↓ ! n ]

-- m ≤ n, counting up from m to n-1
data ⟦⟧[_↑≤_] (m : ⟦⟧) : ⟦⟧ → Set where
  ∅ : ⟦⟧[ m ↑≤ m ]
  ! : ∀ {n} → ⟦⟧[ ! m ↑≤ n ] → ⟦⟧[ m ↑≤ n ]

-- same, with payload
data ⟦_⟧[_↑≤_] {a} (A : ⟦⟧ → Set a) (m : ⟦⟧) : ⟦⟧ → Set a where
  ∅ : ⟦ A ⟧[ m ↑≤ m ]
  _∷_ : ∀ {n} → A m → ⟦ A ⟧[ ! m ↑≤ n ] → ⟦ A ⟧[ m ↑≤ n ]

-- Inj
data ⟦⟧[_↓≤↓_] : ⟦⟧ → ⟦⟧ → Set where
  ∅ : ∀ {n} → ⟦⟧[ ∅ ↓≤↓ n ]
  ! : ∀ {m n} → ⟦⟧[ m ↓≤↓ n ] → ⟦⟧[ ! m ↓≤↓ ! n ]

-- same, with payload
data ⟦_⟧[_↓≤↓_] {a} (A : ⟦⟧ → ⟦⟧ → Set a) : ⟦⟧ → ⟦⟧ → Set a where
  ∅ : ∀ {n} → ⟦ A ⟧[ ∅ ↓≤↓ n ]
  ! : ∀ {m n} → A m n → ⟦ A ⟧[ m ↓≤↓ n ] → ⟦ A ⟧[ ! m ↓≤↓ ! n ]
