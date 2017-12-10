
```agda
{-# OPTIONS --allow-unsolved-metas #-}
```

# Type theory with named variables

```agda
module Type.Named where
```

I would like to use the type-checker to prevent mistakes when renaming and substituting DeBruijn-indexed variables.

```agda
open import Type.Prelude
```

```agda
open import Type.Universe
```

I shall take the notion of a symbol to be a primitive concept, except insofar as I think of a symbol as something that can be written down, strung together, moved around. A term is an arrangement of symbols that have been given meta-theoretic semantics. A term is called lexically-checked if it is guaranteed to be in a suitable arrangement to have some meta-theoretically-denoted meaning. A term is called scope-checked if ...

An `STerm` is a scope-checked term, indexed by the number of elements in its (meta-theoretic) context.

```agda
open import Type.SCTerm renaming (Term to STerm)
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

record Supposition : Set where
  constructor ⟨_⟩
  field
    {size} : Nat
    context : size ctx
open Supposition

record Proposition : Set where
  constructor ⟨_⟩
  field
    {size} : Nat
    {context} : size ctx
    {universe} : Universe
    {sterm} : STerm size
    type : context ⊢ sterm ∈ universe
open Proposition

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
```

The current approach to naming a variable...

```agda
record Name {N} {Γ : N ctx} (τ : ⊣ Γ) : Set where

infix 40 named-syntax
named-syntax : ∀ {N} {Γ : N ctx} (τ : ⊣ Γ) → Name τ → ⊣ Γ
named-syntax τ 𝓍 = τ
syntax named-syntax τ 𝓍 = 𝓍 ∶ τ
```

Another approach was something like

data _∶_ {N} {Γ : (suc N) ctx} : (x : Fin (suc N)) → ∀ {γ : STerm (suc N)} {ℓ} → Γ ⊢ γ ∈ ℓ → Set where
  ⟨_⟩ : ∀ (x : Fin (suc N)) → x ∶ type (Γ at x)

A pattern I notice about application is:

Γ,Δ ⊢ F ∋ f
Γ ⊢ X ∋ x

Γ , (z:S) ⊢ C ∈ ℓ
Γ , Δ     ⊢ S ∋ s
Γ , Δ     ⊢ C [ s / z ]

Γ , (n:N) ⊢ C ∈ ℓ
Γ , C     ⊢ N ∋ succ n
Γ , C     ⊢ C [ succ n / n ]

Γ , (x:A) ⊢ B ∈ ℓ
Γ         ⊢ A ∋ a
Γ         ⊢ B [ a / x ]

```agda
data _xtc_ {N} (Γ : N ctx) : Nat → Set where
  [] : Γ xtc zero
  _∷_ : (γ : ⊣ Γ) → ∀ {M} → Γ , γ xtc M → Γ xtc suc M

infixl 25 _<><_ -- pronounced "fish", h/t Conor McBride
_<><_ : ∀ {N} (Γ : N ctx) → ∀ {M} → Γ xtc M → (M + N) ctx
Γ <>< [] = Γ
Γ <>< (γ ∷ Δ) = transport _ctx auto (Γ , γ <>< Δ)

_[_↤_] : ∀ {N} {Γ : N ctx} {A : ⊣ Γ} {M} {Δ : Γ xtc M}
       → (B : ⊣ (Γ , A))
       → (x : Γ <>< Δ ⊢ (weakenTermByFrom M 0 (A .sterm)))
       → Fin (suc N)
       → STerm (M + N)
_[_↤_] {M = M} f a x = applyTerm (transport STerm auto (weakenTermByFrom M (suc x) (f .sterm))) (a .sterm)
```

A testing ground for developing named substitutions.

Notice there are two ways of doing the same thing.

```agda
private
  data _⊢'_∋_ {N} (Γ : N ctx) : STerm N → STerm N → Set where
    -- Γ , a , b , z // z ⟶ ΣI a b        weaken C from 1 by 2, then instantiate 0 with ΣI 1 0 in ctx Γ , a , b
    ΣE₁ : ∀ {ℓ}
       → (A : ℓ ⊣ Γ)
       → (B : ℓ ⊣ Γ , ⟨ A .type ⟩)
       → (C : ⊣ Γ , ⟨ ΣF (A .type) (B .type) ⟩)
       → (g : Γ , ⟨ A .type ⟩ , ⟨ B .type ⟩ ⊢ applyTerm (weakenTermByFrom 2 1 (C .sterm)) (ΣI (𝓋 1) (𝓋 0)))
       → (p : Γ ⊢ ΣF (A .sterm) (B .sterm))
       → Γ ⊢' applyTerm (C .sterm) (p .sterm) ∋ ΣE (C .sterm) (g .sterm) (p .sterm)
    -- Γ , z , a , b // z ⟶ ΣI a b        weaken C from 0 by 2, then instantiate 2 with ΣI 1 0 in ctx Γ , z , a , b minus z
    ΣE₂ : ∀ {ℓ}
       → (A : ℓ ⊣ Γ)
       → (B : ℓ ⊣ Γ , ⟨ A .type ⟩)
       → (C : ⊣ Γ , ⟨ ΣF (A .type) (B .type) ⟩)
       → (g : Γ , ⟨ A .type ⟩ , ⟨ B .type ⟩ ⊢ instantiateTerm 2 (ΣI (𝓋 1) (𝓋 0)) (weakenTermByFrom 2 0 (C .sterm)))
       → (p : Γ ⊢ ΣF (A .sterm) (B .sterm))
       → Γ ⊢' applyTerm (C .sterm) (p .sterm) ∋ ΣE (C .sterm) (g .sterm) (p .sterm)
```

In both of the g's above, the variables 1 and 0 refer (morally) to types A and B in a context where spaces for those types have been made available by weakening.

It may be important that instantiateTerm 0 X (weakenTermByFrom 2 1 F) ≡ instantiateTerm 2 X (weakenTermByFrom 2 0 F). Is this true in general?

```agda
private -- module InstantiateWeakenEquivalence where
  lemma-ln : ∀ M N → M < N → true ≡ lessNat M N
  lemma-ln zero .(suc (k + 0)) (diff! k) = refl
  lemma-ln (suc M) .(suc (k + suc M)) (diff! k) = lemma-ln M (_+_ k (suc M)) auto

  equiv : ∀ {N M} (F : STerm (suc N)) (X : STerm (M + N))
        → instantiateTerm 0 X (transport STerm auto $ weakenTermByFrom M 1 F) ≡ instantiateTerm (natToFin M ⦃ transport IsTrue (lemma-ln M (suc (M + N)) auto) true ⦄) X (transport STerm auto $ weakenTermByFrom M 0 F)
  equiv {N} {zero} F X = refl
  equiv {N} {suc M} F X = {!!}
```

It is troublingly difficult to prove, I think due to the presence of green slime.

Ignoring that for the time-being, I was inspired by McBride to imagine:

lambda λ a → lambda λ b → apply (C .sterm) (ΣI (𝓋 a) (𝓋 b)) ≡ instantiateTerm 2 (ΣI (𝓋 1) (𝓋 0)) (weakenTermByFrom 2 0 (C .sterm))) : STerm (suc (suc N))

where

C .sterm : Fin (suc N)

We have a goal, `STerm (suc (suc N))` and I imagine the two `suc`s are put there by the `lambda`s.

Some other examples:

lambda λ x → ΠI (𝓋 x) ≡ weakenTermFrom zero (ΠI (𝓋 (suc zero))) : STerm (suc (suc N))
                      ≡ ΠI (𝓋 weakenFinFrom zero zero)

So, `x` is not exactly a `Fin _` but a function to a `Fin _` that fills-in `_` automagically. `lambda` must apply its given function to zero.

```agda
lambda : ∀ {N} → (Fin (suc N) → STerm N) → STerm (suc N)
lambda f = weakenTermFrom zero (f zero)

private
  data _⊢''_∋_ {N} (Γ : N ctx) : STerm N → STerm N → Set where
    ΣE : ∀ {ℓ}
       → (A : ℓ ⊣ Γ)
       → (B : ℓ ⊣ Γ , ⟨ A .type ⟩)
       → (C : ⊣ Γ , ⟨ ΣF (A .type) (B .type) ⟩)
       → ∀ {a b}
       → (g : Γ , a ∶ ⟨ A .type ⟩ , b ∶ ⟨ B .type ⟩ ⊢ instantiateTerm 2 (ΣI (𝓋 (suc zero)) (𝓋 zero)) (lambda λ a → lambda λ b → C .sterm))
       → (p : Γ ⊢ ΣF (A .sterm) (B .sterm))
       → Γ ⊢'' applyTerm (C .sterm) (p .sterm) ∋ ΣE (C .sterm) (g .sterm) (p .sterm)
```

That's still not quite what I want, because I am in no way checking that `𝓋 (suc zero)` refers to the correct thing.

```agda
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
     → ∀ {a b}
     → (g : Γ , a ∶ ⟨ A .type ⟩ , b ∶ ⟨ B .type ⟩ ⊢ {!!})
     → (p : Γ ⊢ ΣF (A .sterm) (B .sterm))
     → Γ ⊢ applyTerm (C .sterm) (p .sterm) ∋ ΣE (C .sterm) (g .sterm) (p .sterm)
  𝟙I : Γ ⊢ 𝟙F ∋ 𝟙I

data _⊢_≝_∶_ {N} (Γ : N ctx) : STerm N → STerm N → STerm N → Set where
```
