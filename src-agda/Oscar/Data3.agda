{- trying (and failing) to create a univesal "successor" -}
-- types with and without payloads defined dependently, those w/o payloads in terms of those with (using ⊤ as a trivial payload)
-- this complicates the successor constructor, `!`, so we use use pattern (OR function?), `¡`
module Oscar.Data3 where

record ⊤ : Set where
  constructor tt

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

-- Fin, with payload
data ⟦_⟧[_] {a} (A : ⟦⟧ → Set a) : ⟦⟧ → Set a where
  ∅ : ∀ {n} → ⟦ A ⟧[ ¡ n ]
  _∷_ : ∀ {n} → A n → ⟦ A ⟧[ n ] → ⟦ A ⟧[ ¡ n ]

data ⟦_⟧[_₀] {a} (A : ⟦⟧ → Set a) : ⟦⟧ → Set a where
  ∅ : ⟦ A ⟧[ ∅ ₀]
  _∷_ : ∀ {n} → A n → ⟦ A ⟧[ n ₀] → ⟦ A ⟧[ ¡ n ₀]

Const_ : ∀ {a} {A : Set a} {b} {B : Set b} → B → A → B
Const_ x _ = x

⟦⟧[_₀] = ⟦ Const ⊤ ⟧[_₀]

-- Fin
⟦⟧[_] = ⟦ Const ⊤ ⟧[_]

-- m ≤ n, counting down from n-1 to m
data ⟦_⟧[_≤↓_] {a} (A : ⟦⟧ → Set a) (m : ⟦⟧) : ⟦⟧ → Set a where
  ∅ : ⟦ A ⟧[ m ≤↓ m ]
  _∷_ : ∀ {n} → A n → ⟦ A ⟧[ m ≤↓ n ] → ⟦ A ⟧[ m ≤↓ ¡ n ]

infix 21 ‼_
pattern ‼_ ⟦A⟧ = tt ∷ ⟦A⟧ -- tricky, works for all above _∷_ constructors only because it is defined afterwards, won't work for later-defined constructors

testNat : ⟦⟧
testNat = ¡ ∅

testListNat : ⟦ ⟦⟧ ⟧
testListNat = ¡ ∅ ∷ ‼ ∅ ∷ ‼ ‼ ∅ ∷ ∅ ∷ ¡ ¡ ¡ ∅ ∷ ∅

testFin : ⟦⟧[ ¡ ¡ ∅ ]
testFin = ‼ ∅

⟦⟧[_≤↓_] = ⟦ Const ⊤ ⟧[_≤↓_]

test≤↓ : ⟦⟧[ ‼ ‼ ‼ ∅ ≤↓ ‼ ‼ ‼ ‼ ‼ ∅ ]
test≤↓ = ‼ ‼ ∅

-- m ≤ n, counting up from m to n-1
data ⟦_⟧[_↑≤_] {a} (A : ⟦⟧ → Set a) (m : ⟦⟧) : ⟦⟧ → Set a where
  ∅ : ⟦ A ⟧[ m ↑≤ m ]
  _∷_ : ∀ {n} → A m → ⟦ A ⟧[ ¡ m ↑≤ n ] → ⟦ A ⟧[ m ↑≤ n ]

⟦⟧[_↑≤_] = ⟦ Const ⊤ ⟧[_↑≤_]

-- Inj (almost)
data ⟦_⟧[_↓≤↓_] {a} (A : ⟦⟧ → ⟦⟧ → Set a) : ⟦⟧ → ⟦⟧ → Set a where
  ∅ : ∀ {n} → ⟦ A ⟧[ ∅ ↓≤↓ n ]
  _∷_ : ∀ {m n} → A m n → ⟦ A ⟧[ m ↓≤↓ n ] → ⟦ A ⟧[ ¡ m ↓≤↓ ¡ n ]

⟦⟧[_↓≤↓_] = ⟦ Const Const ⊤ ⟧[_↓≤↓_]

⓪ ⑴ ⑵ : ⟦⟧
⓪ = ∅
⑴ = ‼ ∅
⑵ = ‼ ⑴

data D : ⟦⟧ → ⟦⟧ → Set where
  List : D ⓪ ⓪
  Fin : D ⑴ ⑴
  Vec : D ⑴ ⑴
  Descend : D ⑴ ⑵
  Ascend : D ⑴ ⑵
  Inj : D ⑵ ⑵

open import Oscar.Level
theA : ∀ ℓ → ⟦⟧ → Set (lsuc ℓ)
theA ℓ ∅ = Set ℓ
theA ℓ (tt ∷ x₁) = ⟦⟧ → theA ℓ x₁

theIndices : ⟦⟧ → Set
theIndices x = ⟦ Const ⟦⟧ ⟧[ x ₀]

μ : ∀ {p i} → D p i → ∀ {a} → theA a p → theIndices i → Set a
μ List A _ = ⟦ A ⟧
μ Fin A (n ∷ _) = ⟦ A ⟧[ n ]
μ Vec A (n ∷ _) = ⟦ A ⟧[ n ₀]
μ Descend A (m ∷ n ∷ _) = ⟦ A ⟧[ m ≤↓ n ]
μ Ascend A (m ∷ n ∷ _) = ⟦ A ⟧[ m ↑≤ n ]
μ Inj A (m ∷ n ∷ ∅) = ⟦ A ⟧[ m ↓≤↓ n ]

μ¡ : ∀ {p i} → D p i → theIndices i → Set
μ¡ List _ = ⟦⟧ → ⟦⟧
μ¡ Fin (n ∷ _) = ⟦⟧[ n ] → ⟦⟧[ ¡ n ]
μ¡ Vec (n ∷ _) = ⟦⟧[ n ₀] → ⟦⟧[ ¡ n ₀]
μ¡ Descend (m ∷ n ∷ _) = ⟦⟧[ m ≤↓ n ] → ⟦⟧[ m ≤↓ ¡ n ]
μ¡ Ascend (m ∷ n ∷ _) = ⟦⟧[ ¡ m ↑≤ n ] → ⟦⟧[ m ↑≤ n ]
μ¡ Inj (m ∷ n ∷ _) = ⟦⟧[ m ↓≤↓ n ] → ⟦⟧[ ¡ m ↓≤↓ ¡ n ]

μ¡↑ : ∀ {p i} → D p i → Set
μ¡↑ List = ⟦⟧ → ⟦⟧
μ¡↑ Fin = {!!}
μ¡↑ Vec = {!!}
μ¡↑ Descend = {!!}
μ¡↑ Ascend = {!!}
μ¡↑ Inj = {!!}

theArguments : ∀ {p i} → (d : D p i) → Set
theArguments List = μ¡ List ∅
theArguments Fin = {n : ⟦⟧} → μ¡ Fin (n ∷ ∅)
theArguments Vec = {n : ⟦⟧} → μ¡ Vec (n ∷ ∅)
theArguments Descend = {m : ⟦⟧} → {n : ⟦⟧} → μ¡ Descend (m ∷ n ∷ ∅)
theArguments Ascend = {m : ⟦⟧} → {n : ⟦⟧} → μ¡ Ascend (m ∷ n ∷ ∅)
theArguments Inj = {m : ⟦⟧} → {n : ⟦⟧} → μ¡ Inj (m ∷ n ∷ ∅)

infix 21 ↑_
↑_ : ∀ {p i} → {d : D p i} → {I : theIndices i} → μ¡ d I
↑_ {d = List} = ‼_
↑_ {d = Fin} {x ∷ I} = ‼_
↑_ {d = Vec} {x ∷ I} = ‼_
↑_ {d = Descend} {x ∷ x₁ ∷ I} = ‼_
↑_ {d = Ascend} {x ∷ x₁ ∷ I} = tt ∷_
↑_ {d = Inj} {x ∷ x₁ ∷ I} = tt ∷_

↑↑ : ∀ {p i} → {d : D p i} → theArguments d
↑↑ {d = List} = {!‼_!}
↑↑ {d = Fin} = ‼_
↑↑ {d = Vec} = ‼_
↑↑ {d = Descend} = ‼_
↑↑ {d = Ascend} = tt ∷_
↑↑ {d = Inj} = tt ∷_

record BANG {p i} (d : D p i) : Set where
  field
    ⟰ : theArguments d

open BANG ⦃ … ⦄

instance BANGFin : BANG Fin
BANG.⟰ BANGFin {n} = ‼_


testμ : μ Fin (Const ⊤) (‼ ‼ ‼ ‼ ∅ ∷ ∅)
testμ = ⟰ {d = Fin} {!!}  -- ↑↑ {d = Fin} {!!}
-- ↑_ {d = Fin} {I = _ ∷ {!!}} ∅
-- ↑_ {d = Fin} {I = {!!} ∷ {!!}} {!!}
{-
data ⟦_⟧ {a} (A : Set a) : Set a where
data ⟦_⟧[_] {a} (A : ⟦⟧ → Set a) : ⟦⟧ → Set a where
data ⟦_⟧[_≤↓_] {a} (A : ⟦⟧ → Set a) (m : ⟦⟧) : ⟦⟧ → Set a where
data ⟦_⟧[_↑≤_] {a} (A : ⟦⟧ → Set a) (m : ⟦⟧) : ⟦⟧ → Set a where
data ⟦_⟧[_↓≤↓_] {a} (A : ⟦⟧ → ⟦⟧ → Set a) : ⟦⟧ → ⟦⟧ → Set a where
-}
