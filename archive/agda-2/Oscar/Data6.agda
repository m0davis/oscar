{-  -}
-- starting from builtins
-- forgot what the point of this was...
module Oscar.Data6 where

open import Oscar.Category.Semigroupoid
open import Oscar.Category.Category
open import Oscar.Category.Morphism
open import Oscar.Category.Setoid
open import Oscar.Function

open import Agda.Builtin.Unit using () renaming (⊤ to 𝟙; tt to ∅)
open import Agda.Builtin.Nat using () renaming (Nat to ℕ; zero to ∅; suc to ↑_)
open import Agda.Builtin.List using () renaming (List to [_]ℕ; [] to ∅; _∷_ to _+_)

open import Oscar.Level

⟦_⟧ℕ[<_↓]
⟦_⟧ℕ[_≤_↓]
⟦_⟧ℕ[↥_≤_]
⟦_⟧ℕ[↓_≤_↓]

-- Fin (with a payload)
data ⟦_⟧ℕ[0…_-1] {a} (A : ℕ → Set a) : ℕ → Set a where
  ∅ : ∀ {n} → ⟦ A ⟧ℕ[<↑ ↑ n ]
  _∷_ : ∀ {n} → A n → ⟦ A ⟧ℕ[ n ] → ⟦ A ⟧ℕ[<↑ ↑ n ]



-- Vec (with an (optional) index)
data ⟦_⟧ℕ[≤_] {a} (A : ℕ → Set a) : ℕ → Set a where
  ∅ : ⟦ A ⟧ℕ[ ∅ ₀]
  _∷_ : ∀ {n} → A n → ⟦ A ⟧ℕ[ n ₀] → ⟦ A ⟧ℕ[ ¡ n ₀]

-- m ≤ n, counting down from n-1 to m
data ⟦_⟧ℕ[_≤_↓] {a} (A : ℕ → Set a) (m : ℕ) : ℕ → Set a where
  ∅ : ⟦ A ⟧ℕ[ m ≤ m ↓]
  _∷_ : ∀ {n} → A n → ⟦ A ⟧ℕ[ m ≤ n ↓] → ⟦ A ⟧ℕ[ m ≤ ¡ n ↓]

-- m ≤ n, counting up from m to n-1
data ⟦_⟧ℕ[↑_≤_] {a} (A : ℕ → Set a) (m : ℕ) : ℕ → Set a where
  ∅ : ⟦ A ⟧ℕ[↑ m ≤ m ]
  _∷_ : ∀ {n} → A m → ⟦ A ⟧ℕ[↑ ¡ m ≤ n ] → ⟦ A ⟧ℕ[↑ m ≤ n ]

-- Inj (almost)
data ⟦_⟧ℕ[↓_≤_↓] {a} (A : ℕ → ℕ → Set a) : ℕ → ℕ → Set a where
  ∅ : ∀ {n} → ⟦ A ⟧ℕ[↓ ∅ ≤ n ↓]
  _∷_ : ∀ {m n} → A m n → ⟦ A ⟧ℕ[↓ m ≤ n ↓] → ⟦ A ⟧ℕ[↓ ¡ m ≤ ¡ n ↓]

⟦_⟧ℕ[_⇒_]∞ : ∀ {a} (A : ℕ → Set a) → ℕ → ℕ → Set a
⟦ A ⟧ℕ[ m ⇒ n ]∞ = A m → A n


-- Fin (with a payload)
data ⟦_⟧ℕ[<_↓] {a} (A : ℕ → Set a) : ℕ → Set a where
  ∅ : ∀ {n} → ⟦ A ⟧[< ↑ n ↓]
  _∷_ : ∀ {n} → A n → ⟦ A ⟧ℕ[< n ] → ⟦ A ⟧[< ↑ n ↓]

-- -- Vec (with an (optional) index)
data ℕ[_]=_ {a} (A : ℕ → Set a) : ℕ → Set a where
  ∅ : ℕ[ A ]= ∅
  _∷_ : ∀ {n} → A n → ℕ[ A ]= ↑ n → ℕ[ A ]= ↑ n

ℕ=_ = ℕ[ const 𝟙 ]=_

-- m ≤ n, counting down from n-1 to m

data ℕ[_]≥_<↓_ {a} (A : ℕ → Set a) (m : ℕ) : ℕ → Set a where
  ∅ : ℕ[ A ]≥ m <↓ m
  _∷_ : ∀ {n} → A n → ℕ[ A ]≥ m <↓ n → ℕ[ A ]≥ m <↓ ↑ n

ℕ≥_<↓_ = ℕ[ const 𝟙 ]≥_<↓_

-- m ≤ n, counting up from m to n-1
data ℕ[_]≥↑_<_ {a} (A : ℕ → Set a) (m : ℕ) : ℕ → Set a where
  ∅ : ℕ[ A ]≥↑ m < m
  _∷_ : ∀ {n} → A m → ℕ[ A ]≥↑ ↑ m < n → ℕ[ A ]≥↑ m < n

ℕ≥↑_<_ = ℕ[ const 𝟙 ]≥↑_<_

-- -- Inj (almost)
-- data ⟦_⟧[↓_≤_↓] {a} (A : ⟦⟧ → ⟦⟧ → Set a) : ⟦⟧ → ⟦⟧ → Set a where
--   ∅ : ∀ {n} → ⟦ A ⟧[↓ ∅ ≤ n ↓]
--   _∷_ : ∀ {m n} → A m n → ⟦ A ⟧[↓ m ≤ n ↓] → ⟦ A ⟧[↓ ¡ m ≤ ¡ n ↓]

-- ⟦⟧[↓_≤_↓] = ⟦ Const Const ⊤ ⟧[↓_≤_↓]

-- ⟦_⟧[_⇒_]∞ : ∀ {a} (A : ⟦⟧ → Set a) → ⟦⟧ → ⟦⟧ → Set a
-- ⟦ A ⟧[ m ⇒ n ]∞ = A m → A n

-- --open import Oscar.Data.Equality
-- --open import Oscar.Data.Equality.properties

-- module _ {𝔬 𝔪 𝔮} (G : Semigroupoid 𝔬 𝔪 𝔮) where
--   open Semigroupoid G

-- {-
--   _≋̇_ : ∀ {a} {A : ⋆ → Set a} {m n : ⋆} → (A m → A n) → (A m → A n) → Set 𝔮
--   _≋̇_ {A = A} {m = m} m→n₁ m→n₂ = {!∀ (am : A m) → m→n₁ am ≋ m→n₂ am!}



--   cat2 : ∀ {a} (A : ⋆ → Set a) → Category {!!} {!!} {!!}
--   Semigroupoid.⋆ (Category.semigroupoid (cat2 A)) = ⋆
--   Setoid.⋆ ((Semigroupoid.𝔐 (Category.semigroupoid (cat2 A)) Morphism.⇒ m) n) = A m → A n
--   IsSetoid._≋_ (Setoid.isSetoid ((Semigroupoid.𝔐 (Category.semigroupoid (cat2 A)) Morphism.⇒ m) n)) = _≡̇_
--   IsSetoid.isEquivalence (Setoid.isSetoid ((Semigroupoid.𝔐 (Category.semigroupoid (cat2 A)) Morphism.⇒ m) n)) = it
--   Semigroupoid._∙_ (Category.semigroupoid (cat2 A)) g f = g ∘ f
--   Semigroupoid.isSemigroupoid (Category.semigroupoid (cat2 A)) = it
--   Category.ε (cat2 A) = id
--   Category.isCategory (cat2 A) = it

--   cat2G : ∀ {a} (A : ⋆ → Set a) → ∀ ℓ ⦃ _ : ∀ {n : ⋆} → IsSetoid (A n) ℓ ⦄ → Category {!!} {!!} {!!}
--   Semigroupoid.⋆ (Category.semigroupoid (cat2G A ℓ)) = ⋆
--   Setoid.⋆ ((Semigroupoid.𝔐 (Category.semigroupoid (cat2G A ℓ)) Morphism.⇒ m) n) = A m → A n
--   IsSetoid._≋_ (Setoid.isSetoid ((Semigroupoid.𝔐 (Category.semigroupoid (cat2G A ℓ)) Morphism.⇒ m) n)) m↦n₁ m↦n₂ = ∀ (am : A m) → m↦n₁ am ≋ m↦n₂ am
--   -- ∀ (am : A m) → m↦n₁ am ≋ m↦n₂ am
--   {-
--   _≋̇_ : ∀ {a} {A : ⋆ → Set a} {m n : ⋆} → (A m → A n) → (A m → A n) → Set 𝔮
--   _≋̇_ {A = A} {m = m} m→n₁ m→n₂ = {!∀ (am : A m) → m→n₁ am ≋ m→n₂ am!}
--   -}
--   IsSetoid.isEquivalence (Setoid.isSetoid ((Semigroupoid.𝔐 (Category.semigroupoid (cat2G A ℓ)) Morphism.⇒ m) n)) = {!it!}
--   Semigroupoid._∙_ (Category.semigroupoid (cat2G A ℓ)) g f = g ∘ f
--   Semigroupoid.isSemigroupoid (Category.semigroupoid (cat2G A ℓ)) = {!it!}
--   Category.ε (cat2G A ℓ) = id
--   Category.isCategory (cat2G A ℓ) = {!it!}
-- -}


-- infix 21 ‼_
-- pattern ‼_ ⟦A⟧ = tt ∷ ⟦A⟧ -- tricky, works for all above _∷_ constructors only because it is defined afterwards, won't work for any later-defined constructors

-- open import Agda.Primitive
-- open import Oscar.Data.Product
-- open import Oscar.Function

-- postulate
--   ℓ : Level
--   Term : ⟦⟧ → Set ℓ
--   Step : ⟦⟧ → Set ℓ

-- Fin = ⟦⟧[_]

-- Inj = ⟦ Const Fin ⟧[↓_≤_↓]

-- Terms = λ N n → ⟦ Const (Term n) ⟧[ N ₀]

-- AList = ⟦ (λ n → Term n × Fin (¡ n)) ⟧[_≤_↓]

-- Fx : ∀ {a} {A : Set a} → A → A → ∀ {b₁} (B₁ : A → Set b₁) → ∀ {b₂} (B₂ : A → Set b₂) → Set (b₁ ⊔ b₂)
-- Fx m n B₁ B₂ = B₁ m → B₂ n

-- Fx₁ : ∀ {a} {A : Set a} → A → ∀ {b₁} (B₁ : A → Set b₁) → ∀ {b₂} (B₂ : A → Set b₂) → Set (b₁ ⊔ b₂)
-- Fx₁ n B₁ B₂ = Fx n n B₁ B₂

-- ListStep = λ n → ⟦ Step n ⟧

-- Rel : ∀ {a} {A : Set a} {b₁} (B₁ : A → Set b₁) {b₂} (B₂ : A → Set b₂) {c₁} (C₁ : A → Set c₁) {c₂} (C₂ : A → Set c₂) → Set (a ⊔ b₁ ⊔ b₂ ⊔ c₁ ⊔ c₂)
-- Rel B₁ B₂ C₁ C₂ = ∀ {m n} → Fx m n B₁ B₂ → Fx m n C₁ C₂

-- Morph : ∀ {a} {A : Set a} {b₁} {b₂} (B : (A → Set b₁) × (A → Set b₂)) {c₁} {c₂} (C₂ : (A → Set c₁) × (A → Set c₂)) → Set (a ⊔ b₁ ⊔ b₂ ⊔ c₁ ⊔ c₂)
-- Morph (B₁ , B₂) (C₁ , C₂) = ∀ {m n} → Fx m n B₁ B₂ → Fx m n C₁ C₂

-- -- functor mappings
-- postulate
--   _◃_ : Morph (Fin , Term) (Term , Term)
--   _◃s_ : ∀ N → Morph (Fin , Term) (Terms N , Terms N)
--   sub : ∀ {m n} → AList m n → Fx m n Fin Term
--   fmapS : Morph (Term , Term) (Step , Step)
--   _◃S_ : Morph (Fin , Term) (ListStep , ListStep)

-- -- ?
-- postulate
--   _⊹_ : ∀ {n} → ⟦ Step n ⟧ → Fx₁ n Term Term

-- testNat : ⟦⟧
-- testNat = ¡ ∅

-- testListNat : ⟦ ⟦⟧ ⟧
-- testListNat = ¡ ∅ ∷ ‼ ∅ ∷ ‼ ‼ ∅ ∷ ∅ ∷ ¡ ¡ ¡ ∅ ∷ ∅

-- testFin : ⟦⟧[ ¡ ¡ ∅ ]
-- testFin = ‼ ∅

-- test≤↓ : ⟦⟧[ ‼ ‼ ‼ ∅ ≤ ‼ ‼ ‼ ‼ ‼ ∅ ↓]
-- test≤↓ = ‼ ‼ ∅

-- ⓪ ⑴ ⑵ ⑶ : ⟦⟧
-- ⓪ = ∅
-- ⑴ = ‼ ∅
-- ⑵ = ‼ ⑴
-- ⑶ = ‼ ⑵

-- testInj : Inj ⑵ ⑶
-- testInj = ‼ ∅ ∷ ∅ ∷ ∅
