{- defining Nat as a kind of List -}
-- the need for ‼ is unfortunate
module Oscar.Data2 where

record ⊤ : Set where
  constructor tt

-- List
data ⟦_⟧ {a} (A : Set a) : Set a where
  ∅ : ⟦ A ⟧
  _∷_ : A → ⟦ A ⟧ → ⟦ A ⟧

-- Nat
⟦⟧ = ⟦ ⊤ ⟧
pattern ‼ ⟦A⟧ = tt ∷ ⟦A⟧

-- Fin
data ⟦⟧[_] : ⟦⟧ → Set where
  ∅ : ∀ {n} → ⟦⟧[ ‼ n ]
  ! : ∀ {n} → ⟦⟧[ n ] → ⟦⟧[ ‼ n ]

test : ⟦⟧[ ‼ (‼ ∅) ]
test = ! ∅
