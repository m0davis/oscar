
# Wherein I do a normal thing.

```agda
module YAF9 where
```

## Some preliminaries that could be put elsewhere.

```agda
module Preliminary where

  open import Prelude public

  ∃_ : ∀ {a b} {A : Set a} (B : A → Set b) → Set (a ⊔ b)
  ∃_ = Σ _

  data IsYes {a} {P : Set a} : Dec P → Set a where
    yes : (p : P) → IsYes (yes p)

  getProof : ∀ {a} {P : Set a} → {d : Dec P} → IsYes d → P
  getProof (yes p) = p

  add-zero : ∀ n → n ≡ n +N 0
  add-zero zero = refl
  add-zero (suc n) = cong suc (add-zero n)
```



So, here's the idea.

```agda


module WorkingIdea1 where

  open Preliminary

  data Context : Nat → Set

  data Type {N : Nat} (Γ : Context N) : Nat → Set

  data Term {N : Nat} (Γ : Context N) : {ℓ : Nat} → Type Γ ℓ → Set

  infixl 5 _,,_
  data Context where
    [] : Context zero
    _,,_ : {N : Nat} (Γ : Context N) {ℓ : Nat} → Type Γ ℓ → Context (suc N)

  -- data _∈Context_ :

  -- getCtx : {N : Nat} (Γ : Context N) → Fin N → ∃ λ Type Γ
  -- getCtx (Γ ,, x) zero = {!!} , {!!}
  -- getCtx Γ (suc x) = {!!}

  record Π-Type {N : Nat} (Γ : Context N) (ℓ : Nat) : Set where
    inductive
    constructor _,_
    field
      dom : Type Γ ℓ
      rng : Type (Γ ,, dom) ℓ

  -- record =-Type {N : Nat}

  data Type {N : Nat} (Γ : Context N) where
    𝒰-intro : (ℓ : Nat) → Type Γ (suc ℓ)
    𝒰-cumul : {ℓ : Nat} → Type Γ ℓ → Type Γ (suc ℓ)
    Π-form : {ℓ : Nat} → Π-Type Γ ℓ → Type Γ ℓ
    ℕ-form : Type Γ zero
    =-form : {ℓ : Nat} {A : Type Γ ℓ} → Term Γ A → Term Γ A → Type Γ ℓ

  data Term {N : Nat} (Γ : Context N) where
    -- variable₀ :
    -- variable : Fin N → Term Γ {!!}
    Π-intro : {ℓ : Nat} (A : Type Γ ℓ) (B : Type (Γ ,, A) ℓ) → Term Γ (Π-form (A , B))
    ℕ-intro-zero : Term Γ ℕ-form
    ℕ-intro-succ : Term Γ ℕ-form → Term Γ ℕ-form
    ℕ-elim : {ℓ : Nat} (C : Type (Γ ,, ℕ-form) ℓ)
                       {C₀ : Type Γ ℓ}
                       (c₀ : Term Γ C₀)
                       {Cₛ : Type (Γ ,, ℕ-form ,, C) ℓ}
                       (cₛ : Term (Γ ,, ℕ-form ,, C) Cₛ)
                       (n : Term Γ ℕ-form)
                       (Cₙ : Type Γ ℓ)
                       {- now we need to provide assertions that
                          C₀ ≡ C[0/x]
                          Cₛ ≡ C[succ x/x]
                          Cₙ ≡ C[n/x]
                       -}
             → Term Γ Cₙ

  extendHead : {N : Nat} (Γ : Context N) {ℓ : Nat} (σ : Type Γ ℓ) → Type (Γ ,, σ) ℓ
  extendHead Γ (𝒰-intro ℓ) = 𝒰-intro ℓ
  extendHead Γ (𝒰-cumul σ) = 𝒰-cumul {!extendHead Γ (𝒰-cumul σ)!}
  extendHead Γ (Π-form (dom , rng)) = {!!}
  extendHead Γ ℕ-form = {!!}
  extendHead Γ (=-form x x₁) = {!!}

  -- this is the Vble rule
  data VariableTerm : {N : Nat} (Γ : Context N) {ℓ : Nat} → Type Γ ℓ → Set where
    head : {N : Nat} (Γ : Context N) {ℓ : Nat} (σ : Type Γ ℓ) → VariableTerm (Γ ,, σ) (extendHead Γ σ)

{-
  -- how to form judgements that types are inhabited by terms
  data _⊢_∋_ : {N : Nat} (Γ : Context N) {ℓ : Nat} (σ : Type Γ ℓ) → Term Γ σ → Set where
    term : {N : Nat} (Γ : Context N) {ℓ : Nat} (σ : Type Γ ℓ) (τ : Term Γ σ) → Γ ⊢ σ ∋ τ
    -- vble₀ : {N : Nat} (Γ : Context N) {ℓ : Nat} (σ : Type Γ ℓ) →
    -- vble : {N : Nat} (Γ : Context N) (i : Fin N) →
-}
```

The above has a problem. I wanted to represent all ways that a type is inhabited via the `Term` datatype, but I am unable to show that this can happen via supposition.

See YAF10.
