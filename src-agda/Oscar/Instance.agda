
module Oscar.Instance where

open import Oscar.Class.Associativity
open import Oscar.Class.Congruity
open import Oscar.Class.Equivalence
open import Oscar.Class.Extensionality
open import Oscar.Class.Injectivity
open import Oscar.Class.Preservativity
open import Oscar.Class.Reflexivity
open import Oscar.Class.Semifunctor
open import Oscar.Class.Semigroup
open import Oscar.Class.Symmetry
open import Oscar.Class.Transitivity
open import Oscar.Data.Equality
open import Oscar.Data.Fin
open import Oscar.Data.Nat
open import Oscar.Function
open import Oscar.Relation

open import Oscar.Data.Equality.properties
  using (≡̇-sym; ≡̇-trans)
  renaming (sym to ≡-sym
           ;trans to ≡-trans)

instance InjectivityFinSuc : ∀ {n} → Injectivity _≡_ _≡_ (Fin.suc {n}) suc
Injectivity.injectivity InjectivityFinSuc refl = refl

data D : Set where
  d1 : Nat → D
  d2 : Nat → Nat → D

pattern d2l r l = d2 l r

instance InjectivityDd1 : Injectivity _≡_ _≡_ d1 d1
Injectivity.injectivity InjectivityDd1 refl = refl

instance InjectivityD2l : ∀ {r1 r2} → Injectivity _≡_ _≡_ (d2l r1) (flip d2 r2)
Injectivity.injectivity InjectivityD2l refl = refl

instance InjectivityoidD2l : ∀ {r1} {r2} → Injectivityoid _ _ _ _ _
Injectivityoid.A InjectivityoidD2l = D
Injectivityoid.B InjectivityoidD2l = D
Injectivityoid._≋₁_ InjectivityoidD2l = _≡_
Injectivityoid.I InjectivityoidD2l = Nat
Injectivityoid._≋₂_ InjectivityoidD2l = _≡_
Injectivityoid.μₗ (InjectivityoidD2l {r1} {r2}) = d2l r1
Injectivityoid.μᵣ (InjectivityoidD2l {r1} {r2}) = flip d2 r2
Injectivityoid.`injectivity InjectivityoidD2l refl = refl

instance InjectivityoidD2r : ∀ {r1} {r2} → Injectivityoid _ _ _ _ _
Injectivityoid.A InjectivityoidD2r = D
Injectivityoid.B InjectivityoidD2r = D
Injectivityoid._≋₁_ InjectivityoidD2r = _≡_
Injectivityoid.I InjectivityoidD2r = Nat
Injectivityoid._≋₂_ InjectivityoidD2r = _≡_
Injectivityoid.μₗ (InjectivityoidD2r {r1} {r2}) = d2 r1
Injectivityoid.μᵣ (InjectivityoidD2r {r1} {r2}) = d2 r2
Injectivityoid.`injectivity InjectivityoidD2r refl = refl

open Injectivityoid ⦃ … ⦄ using (`injectivity)

instance InjectivityD2r : ∀ {l1 l2} → Injectivity _≡_ _≡_ (d2 l1) (d2 l2)
Injectivity.injectivity InjectivityD2r refl = refl

pattern d2' {l} r = d2 l r

injectivity-test : (k l m n : Nat) → (d2 k m ≡ d2 l n) → (d1 k ≡ d1 l)  → Set
injectivity-test k l m n eq1 eq2 with injectivity {_≋₁_ = _≡_} {_≋₂_ = _≡_} {f = d2'} eq1
injectivity-test k l m n eq1 eq2 | ref with injectivity {_≋₁_ = _≡_} {_≋₂_ = _≡_} {f = d1} eq2
… | ref2 = {!!}
-- with `injectivity ⦃ ? ⦄ eq2
-- … | ref3 = {!ref!}

instance

  ≡-Reflexivity : ∀
    {a} {A : Set a}
    → Reflexivity (_≡_ {A = A})
  Reflexivity.reflexivity ≡-Reflexivity = refl

  ≡̇-Reflexivity : ∀
    {a} {A : Set a} {b} {B : A → Set b}
    → Reflexivity (_≡̇_ {B = B})
  Reflexivity.reflexivity ≡̇-Reflexivity _ = refl

  ≡-flip≡-Extensionality : ∀
    {a} {A : Set a}
    → Extensionality {B = const A} _≡_ (λ ⋆ → flip _≡_ ⋆) id id
  Extensionality.extensionality ≡-flip≡-Extensionality = ≡-sym

  ≡̇-flip≡̇-Extensionality : ∀
    {a} {A : Set a} {b} {B : A → Set b}
    → Extensionality {B = const ((x : A) → B x)} _≡̇_ (λ ⋆ → flip _≡̇_ ⋆) id id
  Extensionality.extensionality ≡̇-flip≡̇-Extensionality = ≡̇-sym

  ≡-Transitivity : ∀ {a} {A : Set a} → Transitivity {A = A} _≡_
  Transitivity.transitivity ≡-Transitivity = λ ⋆ → ≡-trans ⋆

  ≡̇-Transitivity : ∀ {a} {A : Set a} {b} {B : A → Set b} → Transitivity {A = (x : A) → B x} _≡̇_
  Transitivity.transitivity ≡̇-Transitivity = ≡̇-trans

  ≡-Congruity : ∀
    {a} {A : Set a} {b} {B : Set b} {ℓ₂} {_≋₂_ : B → B → Set ℓ₂}
    ⦃ _ : Reflexivity _≋₂_ ⦄
    → Congruity (_≡_ {A = A}) _≋₂_
  Congruity.congruity ≡-Congruity μ refl = reflexivity

module Term {𝔣} (FunctionName : Set 𝔣) where

  open import Oscar.Data.Term FunctionName
  open import Oscar.Data.Term.internal.SubstituteAndSubstitution FunctionName as ⋆

  instance

    ◇-≡̇-Associativity : Associativity _◇_ _≡̇_
    Associativity.associativity ◇-≡̇-Associativity = ◇-associativity

    ∘-≡̇-Associativity : ∀ {a} {A : Set a} {b} {B : A → Set b} → Associativity {_►_ = _⟨ B ⟩→_} (λ ⋆ → _∘_ ⋆) _≡̇_
    Associativity.associativity ∘-≡̇-Associativity _ _ _ _ = refl

    ◇-∘-≡̇-◃-◃-◃-Preservativity : ∀ {l m n} → Preservativity (λ ⋆ → _◇_ (m ⊸ n ∋ ⋆)) (_∘′_ {A = Term l}) _≡̇_ _◃_ _◃_ _◃_
    Preservativity.preservativity ◇-∘-≡̇-◃-◃-◃-Preservativity g f τ = symmetry (◃-associativity τ f g)

    ≡̇-≡̇-◃-◃-Extensionality : ∀ {m n} → Extensionality _≡̇_ (λ ⋆ → _≡̇_ ⋆) (_◃_ {m} {n}) (λ ⋆ → _◃_ ⋆)
    Extensionality.extensionality ≡̇-≡̇-◃-◃-Extensionality = ◃-extensionality

  semifunctor-◃ : Semifunctor _◇_ _≡̇_ (λ ⋆ → _∘_ ⋆) _≡̇_ id _◃_
  semifunctor-◃ = it

  open import Oscar.Data.AList FunctionName

  postulate
    _++_ : ∀ {m n} → AList m n → ∀ {l} → AList l m → AList l n
    sub : ∀ {m n} → AList m n → m ⊸ n
    ++-assoc : ∀ {l m n o} (ρ : AList l m) (σ : AList n _) (τ : AList o _) → ρ ++ (σ ++ τ) ≡ (ρ ++ σ) ++ τ
    subfact1 : ∀ {l m n} (ρ : AList m n) (σ : AList l m) → sub (ρ ++ σ) ≡̇ (sub ρ ◇ sub σ)

  instance

    ++-≡-Associativity : Associativity _++_ _≡_
    Associativity.associativity ++-≡-Associativity f g h = ++-assoc h g f

    ++-◇-sub-sub-sub : ∀ {l m n} → Preservativity (λ ⋆ → _++_ (AList m n ∋ ⋆)) (λ ⋆ → _◇_ ⋆ {l = l}) _≡̇_ sub sub sub
    Preservativity.preservativity ++-◇-sub-sub-sub = subfact1

  semifunctor-sub : Semifunctor _++_ _≡_ _◇_ _≡̇_ id sub
  semifunctor-sub = it

--   ≡̇-extension : ∀
--       {a} {A : Set a} {b} {B : A → Set b}
--       {ℓ₁} {_≤₁_ : (x : A) → B x → Set ℓ₁}
--       {c} {C : Set c}
--       {d} {D : C → Set d}
--       {μ₁ : A → (z : C) → D z}
--       {μ₂ : ∀ {x} → B x → (z : C) → D z}
--     ⦃ _ : Extensionality _≤₁_ (λ ⋆ → _≡̇_ ⋆) μ₁ μ₂ ⦄
--       {x} {y : B x}
--     → x ≤₁ y → μ₁ x ≡̇ μ₂ y
--   ≡̇-extension = extension (λ ⋆ → _≡̇_ ⋆)

--   test-◃-extensionality : ∀ {m n} {f g : m ⊸ n} → f ≡̇ g → f ◃_ ≡̇ g ◃_
--   test-◃-extensionality = ≡̇-extension -- ≡̇-extension -- ⦃ ? ⦄ -- extension (λ ⋆ → _≡̇_ ⋆)

--   postulate
--     R : Set
--     S : Set
--     _◀_ : ∀ {m n} → m ⊸ n → R → S
--     _◀'_ : ∀ {m n} → m ⊸ n → R → S
--     _◆_ : ∀ {m n} → m ⊸ n → ∀ {l} → l ⊸ m → l ⊸ n

--     instance ≡̇-≡̇-◀-◀'-Extensionality : ∀ {m n} → Extensionality _≡̇_ (λ ⋆ → _≡̇_ ⋆) ((m ⊸ n → _) ∋ _◀_) _◀'_
--     instance ≡̇-≡̇-◀-◀-Extensionality : ∀ {m n} → Extensionality _≡̇_ (λ ⋆ → _≡̇_ ⋆) ((m ⊸ n → _) ∋ _◀_) _◀_
--     instance ◆-◇-≡̇-Associativity : ∀ {k} → Associativity _◆_ (λ ⋆ → _◇_ ⋆) ((k ⊸ _ → _) ∋ _≡̇_)
--     instance ◆-◇-≡̇-Associativity' : ∀ {k} → Associativity _◇_ (λ ⋆ → _◆_ ⋆) ((k ⊸ _ → _) ∋ _≡̇_)

--   test-◀-extensionality : ∀ {m n} {f g : m ⊸ n} → f ≡̇ g → f ◀_ ≡̇ g ◀_
--   test-◀-extensionality {m} {n} = ≡̇-extension
--   -- extensionality {_≤₁_ = _≡̇_} {μ₁ = ((m ⊸ n → _) ∋ _◀_)} {μ₂ = _◀_}

--   test-◀'-extensionality : ∀ {m n} {f g : m ⊸ n} → f ≡̇ g → f ◀_ ≡̇ g ◀'_
--   test-◀'-extensionality = ≡̇-extension

--   test-◃-associativity : ∀ {l} (t : Term l) {m} (f : l ⊸ m) {n} (g : m ⊸ n) → g ◃ (f ◃ t) ≡ (g ◇ f) ◃ t
--   test-◃-associativity = association _◇_ _≡_

--   test-◇-associativity : ∀ {k l} (f : k ⊸ l) {m} (g : l ⊸ m) {n} (h : m ⊸ n) → h ◇ (g ◇ f) ≡̇ (h ◇ g) ◇ f
--   test-◇-associativity = association _◇_ _≡̇_

--   test-◆-associativity : ∀ {k l} (f : k ⊸ l) {m} (g : l ⊸ m) {n} (h : m ⊸ n) → h ◇ (g ◇ f) ≡̇ (h ◆ g) ◇ f
--   test-◆-associativity = association _◆_ _≡̇_

--   test-◆-associativity' : ∀ {k l} (f : k ⊸ l) {m} (g : l ⊸ m) {n} (h : m ⊸ n) → h ◆ (g ◆ f) ≡̇ (h ◇ g) ◆ f
--   test-◆-associativity' = association _◇_ _≡̇_
