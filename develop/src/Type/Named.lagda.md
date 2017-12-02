
```agda
{-# OPTIONS --allow-unsolved-metas #-}
```

# Type theory with named variables

```agda
module Type.Named where
```

I would like to use the type-checker to prevent mistakes when renaming and substituting DeBruijn-indexed variables.

```agda
-- I will repurpose _,_
open import Prelude renaming (_,_ to _,,_)
```

```agda
open import Tactic.Nat
```

```agda
open import Type.Common hiding (Term)
```

I shall take the notion of a symbol to be a primitive concept, except insofar as I think of a symbol as something that can be written down, strung together, moved around. A term is an arrangement of symbols that have been given meta-theoretic semantics. A term is called lexically-checked if it is guaranteed to be in a suitable arrangement to have some meta-theoretically-denoted meaning. A term is called scope-checked if ...

An `STerm` is a scope-checked term, indexed by the number of elements in its (meta-theoretic) context.

```agda
open import Type.Common using () renaming (Term to STerm)
```

```agda
infix 10 ⊣_
data _ctx : Nat → Set

-- scoped-checked types
record ⊣_ {N : Nat} (Γ : N ctx) : Set

infixl 30 _,_
data _ctx where
  ε : zero ctx
  _,_ : ∀ {N} → (Γ : N ctx) → ⊣ Γ → suc N ctx

-- universe inhabitation: that is, the types
data _⊢_∈_ : ∀ {N} (Γ : N ctx) → STerm N → Universe → Set

record ⊣_ {N : Nat} (Γ : N ctx) where
  constructor ⟨_⟩
  inductive
  field
    {universe} : Universe
    {sterm} : STerm N
    type : Γ ⊢ sterm ∈ universe
open ⊣_

-- sort-indexed, scope-checked types
record _⊣_ (ℓ : Universe) {N : Nat} (Γ : N ctx) : Set where
  constructor ⟨_⟩
  inductive
  field
    {sterm} : STerm N
    type : Γ ⊢ sterm ∈ ℓ
open _⊣_

-- type inhabitation: that is, the terms (not to be confused with `STerm`s
data _⊢_∋_ {N} (Γ : N ctx) : STerm N → STerm N → Set

data _⊢_∈_ where
  suppose : ∀ {N} {Γ : N ctx} {𝑨 ℓ}
          → (γ : ⊣ Γ)
          → Γ ⊢ 𝑨 ∈ ℓ
          → Γ , γ ⊢ weakenTermFrom zero 𝑨 ∈ ℓ
  𝒰ⁱ : ∀ {N} {Γ : N ctx}
     → Γ ⊢ 𝒰 zero ∈ suc zero
  𝒰ᶜ : ∀ {N} {Γ : N ctx}
     → ∀ {𝑨 ℓ}
     → Γ ⊢ 𝑨 ∈ ℓ → Γ ⊢ 𝑨 ∈ suc ℓ
  ⟨_⟩ : ∀ {N} {Γ : N ctx}
      → ∀ {𝑨 ℓ}
      → Γ ⊢ 𝒰 ℓ ∋ 𝑨
      → Γ ⊢ 𝑨 ∈ ℓ
  ΠF : ∀ {N} {Γ : N ctx}
     → ∀ {𝑨 𝑩 ℓ}
     → (A : Γ ⊢ 𝑨 ∈ ℓ)
     → Γ , ⟨ A ⟩ ⊢ 𝑩 ∈ ℓ
     → Γ ⊢ ΠF 𝑨 𝑩 ∈ ℓ
  ΣF : ∀ {N} {Γ : N ctx}
     → ∀ {𝑨 𝑩 ℓ}
     → (A : Γ ⊢ 𝑨 ∈ ℓ)
     → Γ , ⟨ A ⟩ ⊢ 𝑩 ∈ ℓ
     → Γ ⊢ ΣF 𝑨 𝑩 ∈ ℓ
  =F : ∀ {N} {Γ : N ctx}
     → ∀ {𝑨 𝒂 𝒃 ℓ}
     → Γ ⊢ 𝑨 ∈ ℓ
     → Γ ⊢ 𝑨 ∋ 𝒂
     → Γ ⊢ 𝑨 ∋ 𝒃
     → Γ ⊢ =F 𝑨 𝒂 𝒃 ∈ ℓ

-- term witnesses
record _⊢_ {N} (Γ : N ctx) (𝒀 : STerm N) : Set where
  constructor ⟨_⟩
  inductive
  field
    {sterm} : STerm N
    term : Γ ⊢ 𝒀 ∋ sterm
open _⊢_

_at_ : ∀ {N} → (Γ : N ctx) → Fin N → ⊣ Γ
_ , γ at zero = ⟨ suppose γ (γ .type) ⟩
Γ , γ at suc x = ⟨ suppose γ ((Γ at x) .type) ⟩

{-
-- named variables
data _∶_ {N} {Γ : (suc N) ctx} : (x : Fin (suc N)) → ∀ {γ : STerm (suc N)} {ℓ} → Γ ⊢ γ ∈ ℓ → Set where
  ⟨_⟩ : ∀ (x : Fin (suc N)) → x ∶ type (Γ at x)

-- application
[_$$_] : ∀ {N} {Γ : N ctx} {γ₀ : ⊣ Γ} {γ₁ : ⊣ Γ , γ₀}
       → (τ₁ : Γ , γ₀ ⊢ γ₁ .sterm)
       → (τ₀ : Γ ⊢ γ₀ .sterm)
       → Σ (STerm N) λ τ → Γ ⊢ applyTerm (γ₁ .sterm) (γ₀ .sterm) ∋ τ
[_$$_] τ₁ τ₀ = applyTerm (τ₁ .sterm) (τ₀ .sterm) ,, {!!}

-- substitution
data _xtc_ {N} (Γ : N ctx) : Nat → Set where
  [] : Γ xtc zero
  _∷_ : (γ : ⊣ Γ) → ∀ {M} → Γ , γ xtc M → Γ xtc suc M

infixl 25 _<><_ -- h/t Conor McBride
_<><_ : ∀ {N} (Γ : N ctx) → ∀ {M} → Γ xtc M → (M + N) ctx
Γ <>< [] = Γ
Γ <>< (γ ∷ Δ) = transport _ctx auto (Γ , γ <>< Δ)
{-
sub : ∀ {N} {Γ : N ctx} {M} (γ : ⊣ Γ) → Γ , γ xtc M → Γ xtc M
sub _ [] = []
sub γ (δ ∷ Δ) = {!δ!} ∷ {!!}
-}
[_↤_] : ∀ {N} {Γ : N ctx} {M} {γ₀ : ⊣ Γ} {Δ : Γ , γ₀ xtc M} {γ₁ : ⊣ Γ , γ₀ <>< Δ}
       → (τ₁ : Γ , γ₀ <>< Δ ⊢ γ₁ .sterm)
       → (τ₀ : Γ ⊢ γ₀ .sterm)
       → {-Σ-} (STerm (M + N)) -- λ τ → Γ <>< {!Δ!} ⊢ substituteTerm {M = M} (transport STerm auto (γ₁ .sterm)) (γ₀ .sterm) ∋ τ
[_↤_] {M = M} τ₁ τ₀ = substituteTerm {M = M} (transport STerm auto (τ₁ .sterm)) ((τ₀ .sterm)) -- ,, {!!} --  ,, {!!}
-}

data _⊢_∋_ {N} (Γ : N ctx) where
  variable : (x : Fin N)
           → Γ ⊢ (Γ at x) .sterm ∋ 𝓋 x
  ⟨_⟩ : ∀ {𝑨 ℓ}
      → Γ ⊢ 𝑨 ∈ ℓ
      → Γ ⊢ 𝒰 ℓ ∋ 𝑨
  ΠI : ∀ {𝑩}
     → (A : ⊣ Γ)
     → (b : Γ , A ⊢ 𝑩)
     → Γ ⊢ ΠF (A .sterm) 𝑩 ∋ ΠI (b .sterm)
  ΠE : ∀ {𝑨 𝑩}
     → (f : Γ ⊢ ΠF 𝑨 𝑩)
     → (a : Γ ⊢ 𝑨)
     → Γ ⊢ applyTerm 𝑩 (a .sterm) ∋ ΠE (f .sterm) (a .sterm)
  ΣI : ∀ {ℓ}
     → (A : ℓ ⊣ Γ)
     → (B : ℓ ⊣ Γ , ⟨ A .type ⟩)
     → (a : Γ ⊢ A .sterm)
     → (b : Γ ⊢ applyTerm (B .sterm) (a .sterm))
     → Γ ⊢ ΣF (A .sterm) (B .sterm) ∋ ΣI (a .sterm) (b .sterm)
  ΣE : ∀ {ℓ}
     → (A : ℓ ⊣ Γ)
     → (B : ℓ ⊣ Γ , ⟨ A .type ⟩)
     → (C : ⊣ Γ , ⟨ ΣF (A .type) (B .type) ⟩)
     → (g : Γ , ⟨ A .type ⟩ , ⟨ B .type ⟩ ⊢ applyTerm (weakenTermByFrom 2 1 (C .sterm)) (ΣI (𝓋 1) (𝓋 0)))
     → (p : Γ ⊢ ΣF (A .sterm) (B .sterm))
     → Γ ⊢ applyTerm (C .sterm) (p .sterm) ∋ ΣE (C .sterm) (g .sterm) (p .sterm)
  𝟙I : Γ ⊢ 𝟙F ∋ 𝟙I

data _⊢_≝_∶_ {N} (Γ : N ctx) : STerm N → STerm N → STerm N → Set where
```
