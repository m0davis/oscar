
# Visindex: a study of the (in)visibility of indexed sets in Agda

```agda
module Visindex where
```

```agda
open import Prelude
open import Type.Common
```

```
data _ctx⋖_ : Nat → Complexity → Set where

-- abstract
_ctx : Nat → Set
N ctx = ∃ (N ctx⋖_)

-- Γ ⊢ a : A ⋖ χ = a proves A given Γ, with complexity χ
data _⊢_∶_⋖_ {N χ} (Γ : N ctx⋖ χ) : Term N → Term N → Complexity → Set where

-- Γ ⊢ a : A = a is a proof of A given Γ
_⊢_∶_ : ∀ {N χ} (Γ : N ctx⋖ χ) → Term N → Term N → Set
Γ ⊢ a ∶ A = ∃ (Γ ⊢ a ∶ A ⋖_)

-- Γ ⊢ A = there is a proof of A given Γ
_⊢_ : ∀ {N χ} (Γ : N ctx⋖ χ) → Term N → Set
Γ ⊢ A = ∃ (Γ ⊢_∶ A)

infixr 1 _,_
record Σ' {a b} (A : Set a) (B : A → Set b) : Set (a ⊔ b) where
  constructor _,_
  field
    fst : A
    snd : B fst

_⊢'_ : ∀ {N} (Γ : N ctx) → Term N → Set
(χ , Γ) ⊢' A = Σ' _ (Γ ⊢_∶ A)
```

```agda
_⊢y_ : ∀ {N} (Γ : N ctx) → Term N → Set
(χ , Γ) ⊢y A = Σ' _ (Γ ⊢_∶ A)

thingy : ∀ {N} (Γ : N ctx) → Term N → Set
thingy Γ A = Σ _ (snd Γ ⊢_∶ A)

-- it turns out to help a lot to use a datatype rather than a function, _⊢'_, insofar as Agda's ability to typecheck. why?
data _⊢''_ {N} (Γ : N ctx) (τ : Term N) : Set where
  evidence : Γ ⊢' τ → Γ ⊢'' τ

record _⊢'''_ {N} (Γ : N ctx) (τ : Term N) : Set where
  constructor evidence
  field
    -- the-term
    the-type : Γ ⊢' τ
```

```agda
data _∋_⊣0_∧_ {N} (B : Term (suc N)) (A : Term N)
             : ∀ {Γ : N ctx} {Δ : suc N ctx}
             → Γ ⊢' A → Δ ⊢' B → Set where

data _∋_⊣_∧_ {N} (B : Term (suc N)) (A : Term N)
             : ∀ {Γ : N ctx} {Δ : suc N ctx}
             → Γ ⊢'' A → Δ ⊢'' B → Set where

data _∋_⊣'''_∧_ {N} (B : Term (suc N)) (A : Term N)
             : ∀ {Γ : N ctx} {Δ : suc N ctx}
             → Γ ⊢''' A → Δ ⊢''' B → Set where
```

Why does it help Agda's typechecker to use _⊢''_ instead of _⊢'_? Why is _⊢'_ displayed as is but other types are normalised to Σ?

The hole for Δ⊢B fails to fill. See what happens when _ctx is defined using Σ' instead of Σ.

```agda
postulate
  substitute0 : ∀ {N} {B : Term (suc N)} {A : Term N}
             → ∀ {Γ : N ctx} {Δ : suc N ctx}
             → {Γ⊢A' : thingy Γ A} {Γ⊢A : Γ ⊢' A} {Δ⊢B : (fst Δ , snd Δ) ⊢' B}
             → B ∋ A ⊣0 Γ⊢A ∧ Δ⊢B
             → _∋_⊣0_∧_ B A {Γ = Γ} {Δ = Δ} Γ⊢A {!Δ⊢B!}
             → Term N
  substitute : ∀ {N} {B : Term (suc N)} {A : Term N}
             → ∀ {Γ : N ctx} {Δ : suc N ctx}
             → {Γ⊢A : Γ ⊢'' A} {Δ⊢B : Δ ⊢'' B}
             → B ∋ A ⊣ Γ⊢A ∧ Δ⊢B
             → _∋_⊣_∧_ B A {Γ = Γ} Γ⊢A Δ⊢B
             → Term N
  substitute3 : ∀ {N} {B : Term (suc N)} {A : Term N}
             → ∀ {Γ : N ctx} {Δ : suc N ctx}
             → {Γ⊢A : Γ ⊢''' A} {Δ⊢B : Δ ⊢''' B}
             → B ∋ A ⊣''' Γ⊢A ∧ Δ⊢B
             → Term N
```
