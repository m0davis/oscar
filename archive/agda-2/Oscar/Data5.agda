{- wip, coming to realise that the instance of IsSetoid defined in Data.Equality.properties is over-eager (defining _≡_ for all (A : Set (a : Level)), _≡̇_ for ∀ (x : A : Set (a : Level)) → (B : A → Set (b : Level)) x -}
-- add samples of stuff from unification (AList, etc.)
module Oscar.Data5 where

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

⟦_⟧[_⇒_]∞ : ∀ {a} (A : ⟦⟧ → Set a) → ⟦⟧ → ⟦⟧ → Set a
⟦ A ⟧[ m ⇒ n ]∞ = A m → A n

open import Oscar.Category.Semigroupoid
open import Oscar.Category.Category
open import Oscar.Category.Morphism
open import Oscar.Category.Setoid
--open import Oscar.Data.Equality
--open import Oscar.Data.Equality.properties
open import Oscar.Function

module _ {𝔬 𝔪 𝔮} (G : Semigroupoid 𝔬 𝔪 𝔮) where
  open Semigroupoid G


{-
  _≋̇_ : ∀ {a} {A : ⋆ → Set a} {m n : ⋆} → (A m → A n) → (A m → A n) → Set 𝔮
  _≋̇_ {A = A} {m = m} m→n₁ m→n₂ = {!∀ (am : A m) → m→n₁ am ≋ m→n₂ am!}



  cat2 : ∀ {a} (A : ⋆ → Set a) → Category {!!} {!!} {!!}
  Semigroupoid.⋆ (Category.semigroupoid (cat2 A)) = ⋆
  Setoid.⋆ ((Semigroupoid.𝔐 (Category.semigroupoid (cat2 A)) Morphism.⇒ m) n) = A m → A n
  IsSetoid._≋_ (Setoid.isSetoid ((Semigroupoid.𝔐 (Category.semigroupoid (cat2 A)) Morphism.⇒ m) n)) = _≡̇_
  IsSetoid.isEquivalence (Setoid.isSetoid ((Semigroupoid.𝔐 (Category.semigroupoid (cat2 A)) Morphism.⇒ m) n)) = it
  Semigroupoid._∙_ (Category.semigroupoid (cat2 A)) g f = g ∘ f
  Semigroupoid.isSemigroupoid (Category.semigroupoid (cat2 A)) = it
  Category.ε (cat2 A) = id
  Category.isCategory (cat2 A) = it
-}

  cat2G : ∀ {a} (A : ⋆ → Set a) → ∀ ℓ ⦃ _ : ∀ {n : ⋆} → IsSetoid (A n) ℓ ⦄ → Category {!!} {!!} {!!}
  Semigroupoid.⋆ (Category.semigroupoid (cat2G A ℓ)) = ⋆
  Setoid.⋆ ((Semigroupoid.𝔐 (Category.semigroupoid (cat2G A ℓ)) Morphism.⇒ m) n) = A m → A n
  IsSetoid._≋_ (Setoid.isSetoid ((Semigroupoid.𝔐 (Category.semigroupoid (cat2G A ℓ)) Morphism.⇒ m) n)) m↦n₁ m↦n₂ = ∀ (am : A m) → m↦n₁ am ≋ m↦n₂ am
  -- ∀ (am : A m) → m↦n₁ am ≋ m↦n₂ am
  {-
  _≋̇_ : ∀ {a} {A : ⋆ → Set a} {m n : ⋆} → (A m → A n) → (A m → A n) → Set 𝔮
  _≋̇_ {A = A} {m = m} m→n₁ m→n₂ = {!∀ (am : A m) → m→n₁ am ≋ m→n₂ am!}
  -}
  IsSetoid.isEquivalence (Setoid.isSetoid ((Semigroupoid.𝔐 (Category.semigroupoid (cat2G A ℓ)) Morphism.⇒ m) n)) = {!it!}
  Semigroupoid._∙_ (Category.semigroupoid (cat2G A ℓ)) g f = g ∘ f
  Semigroupoid.isSemigroupoid (Category.semigroupoid (cat2G A ℓ)) = {!it!}
  Category.ε (cat2G A ℓ) = id
  Category.isCategory (cat2G A ℓ) = {!it!}


infix 21 ‼_
pattern ‼_ ⟦A⟧ = tt ∷ ⟦A⟧ -- tricky, works for all above _∷_ constructors only because it is defined afterwards, won't work for any later-defined constructors

open import Agda.Primitive
open import Oscar.Data.Product
open import Oscar.Function

postulate
  ℓ : Level
  Term : ⟦⟧ → Set ℓ
  Step : ⟦⟧ → Set ℓ

Fin = ⟦⟧[_]

Inj = ⟦ Const Fin ⟧[↓_≤_↓]

Terms = λ N n → ⟦ Const (Term n) ⟧[ N ₀]

AList = ⟦ (λ n → Term n × Fin (¡ n)) ⟧[_≤_↓]

Fx : ∀ {a} {A : Set a} → A → A → ∀ {b₁} (B₁ : A → Set b₁) → ∀ {b₂} (B₂ : A → Set b₂) → Set (b₁ ⊔ b₂)
Fx m n B₁ B₂ = B₁ m → B₂ n

Fx₁ : ∀ {a} {A : Set a} → A → ∀ {b₁} (B₁ : A → Set b₁) → ∀ {b₂} (B₂ : A → Set b₂) → Set (b₁ ⊔ b₂)
Fx₁ n B₁ B₂ = Fx n n B₁ B₂

ListStep = λ n → ⟦ Step n ⟧

Rel : ∀ {a} {A : Set a} {b₁} (B₁ : A → Set b₁) {b₂} (B₂ : A → Set b₂) {c₁} (C₁ : A → Set c₁) {c₂} (C₂ : A → Set c₂) → Set (a ⊔ b₁ ⊔ b₂ ⊔ c₁ ⊔ c₂)
Rel B₁ B₂ C₁ C₂ = ∀ {m n} → Fx m n B₁ B₂ → Fx m n C₁ C₂

Morph : ∀ {a} {A : Set a} {b₁} {b₂} (B : (A → Set b₁) × (A → Set b₂)) {c₁} {c₂} (C₂ : (A → Set c₁) × (A → Set c₂)) → Set (a ⊔ b₁ ⊔ b₂ ⊔ c₁ ⊔ c₂)
Morph (B₁ , B₂) (C₁ , C₂) = ∀ {m n} → Fx m n B₁ B₂ → Fx m n C₁ C₂

-- functor mappings
postulate
  _◃_ : Morph (Fin , Term) (Term , Term)
  _◃s_ : ∀ N → Morph (Fin , Term) (Terms N , Terms N)
  sub : ∀ {m n} → AList m n → Fx m n Fin Term
  fmapS : Morph (Term , Term) (Step , Step)
  _◃S_ : Morph (Fin , Term) (ListStep , ListStep)

-- ?
postulate
  _⊹_ : ∀ {n} → ⟦ Step n ⟧ → Fx₁ n Term Term

testNat : ⟦⟧
testNat = ¡ ∅

testListNat : ⟦ ⟦⟧ ⟧
testListNat = ¡ ∅ ∷ ‼ ∅ ∷ ‼ ‼ ∅ ∷ ∅ ∷ ¡ ¡ ¡ ∅ ∷ ∅

testFin : ⟦⟧[ ¡ ¡ ∅ ]
testFin = ‼ ∅

test≤↓ : ⟦⟧[ ‼ ‼ ‼ ∅ ≤ ‼ ‼ ‼ ‼ ‼ ∅ ↓]
test≤↓ = ‼ ‼ ∅

⓪ ⑴ ⑵ ⑶ : ⟦⟧
⓪ = ∅
⑴ = ‼ ∅
⑵ = ‼ ⑴
⑶ = ‼ ⑵

testInj : Inj ⑵ ⑶
testInj = ‼ ∅ ∷ ∅ ∷ ∅
