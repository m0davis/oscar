
```agda
{-# OPTIONS --allow-unsolved-metas #-}
```

```agda
module Type.deprecated.Term.Layer0.Slimdex where
```

```agda
open import Type.Prelude
```

```agda
open import Type.deprecated.Term.Layer-1.SCTerm renaming (Term to STerm)
open import Type.Universe
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
  eta-equality
  constructor ⟨_⟩
  inductive
  field
    {universe} : Universe
    {sterm} : STerm N
    type : Γ ⊢ sterm ∈ universe
open ⊣_

⊣eq : ∀ {N} {Γ : N ctx} (A : ⊣ Γ) → A ≡ ⟨ A .type ⟩
⊣eq ⟨ type₁ ⟩ = refl

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

-- type inhabitation: that is, the terms (not to be confused with `STerm`s)
data _⊢_∋_ {N} (Γ : N ctx) : ∀ {𝑻 ℓ} → (τ : Γ ⊢ 𝑻 ∈ ℓ) → STerm N → Set

data _⊢_∈_ where
  suppose : ∀ {N} {Γ : N ctx} {𝑨 ℓ}
          → (γ : ⊣ Γ)
          → Γ ⊢ 𝑨 ∈ ℓ
          → Γ , γ ⊢ weakenTermFrom zero 𝑨 ∈ ℓ
  apply : ∀ {N} {Γ : N ctx} {ℓ 𝑨 𝑩 𝒂}
        → {A : Γ ⊢ 𝑨 ∈ ℓ}
        → (B : Γ , ⟨ A ⟩ ⊢ 𝑩 ∈ ℓ)
        → (a : Γ ⊢ A ∋ 𝒂)
        → Γ ⊢ applyTerm 𝑩 𝒂 ∈ ℓ
  𝒰ⁱ : ∀ {N} {Γ : N ctx}
     → Γ ⊢ 𝒰 zero ∈ suc zero
  𝒰ᶜ : ∀ {N} {Γ : N ctx}
     → ∀ {𝑨 ℓ}
     → Γ ⊢ 𝑨 ∈ ℓ → Γ ⊢ 𝑨 ∈ suc ℓ
  ⟨_⟩ : ∀ {N} {Γ : N ctx}
      → ∀ {𝑨 ℓ} {τ : Γ ⊢ 𝑨 ∈ ℓ}
      → Γ ⊢ τ ∋ 𝑨
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
     → (A : Γ ⊢ 𝑨 ∈ ℓ)
     → Γ ⊢ A ∋ 𝒂
     → Γ ⊢ A ∋ 𝒃
     → Γ ⊢ =F 𝑨 𝒂 𝒃 ∈ ℓ

-- term witnesses
record _⊢_ {N} (Γ : N ctx) (𝒀 : STerm N) : Set where
  constructor ⟨_⟩
  inductive
  field
    {sterm} : STerm N
    term : Γ ⊢ {!𝒀!} ∋ sterm
open _⊢_

record _⊢ {N} {Γ : N ctx} {𝒀 : STerm N} {ℓ : Universe} (Y : Γ ⊢ 𝒀 ∈ ℓ) : Set where
  constructor ⟨_⟩
  inductive
  field
    {sterm} : STerm N
    term : Γ ⊢ Y ∋ sterm
open _⊢

_at_ : ∀ {N} → (Γ : N ctx) → Fin N → ⊣ Γ
_ , γ at zero = ⟨ suppose γ (γ .type) ⟩
Γ , γ at suc x = ⟨ suppose γ ((Γ at x) .type) ⟩
```

```agda
data _⊢_∋_ {N} (Γ : N ctx) where
  variable : (x : Fin N)
           → Γ ⊢ (Γ at x) .type ∋ 𝓋 x
  ⟨_⟩ : ∀ {𝑨 ℓ}
      → (A : Γ ⊢ 𝑨 ∈ ℓ)
      → Γ ⊢ A ∋ 𝑨
  ΠI : ∀ {ℓ 𝑨 𝑩}
     → (A : Γ ⊢ 𝑨 ∈ ℓ)
     → (B : Γ , ⟨ A ⟩ ⊢ 𝑩 ∈ ℓ )
     → (b : B ⊢)
     → Γ ⊢ ΠF A B ∋ ΠI (b .sterm)
  ΠE : ∀ {ℓ 𝑨 𝑩}
     → {A : Γ ⊢ 𝑨 ∈ ℓ}
     → {B : Γ , ⟨ A ⟩ ⊢ 𝑩 ∈ ℓ}
     → (f : ΠF A B ⊢)
     → (a : A ⊢)
     → Γ ⊢ apply B (a .term) ∋ ΠE (f .sterm) (a .sterm)
  ΣI : ∀ {ℓ 𝑨 𝑩}
     → {A : Γ ⊢ 𝑨 ∈ ℓ}
     → {B : Γ , ⟨ A ⟩ ⊢ 𝑩 ∈ ℓ}
     → (a : A ⊢)
     → (b : apply B (a .term) ⊢)
     → Γ ⊢ ΣF A B ∋ ΣI (a .sterm) (b .sterm)
  ΣE : ∀ {ℓ 𝑨 𝑩 𝑪 𝒈}
     → (A : Γ ⊢ 𝑨 ∈ ℓ)
     → (B : Γ , ⟨ A ⟩ ⊢ 𝑩 ∈ ℓ)
     → (C : Γ , ⟨ ΣF A B ⟩ ⊢ 𝑪 ∈ ℓ)
     → (g : Γ , ⟨ A ⟩ , ⟨ B ⟩ ⊢ apply (suppose ⟨ {!!} ⟩ {!!}) (ΣI ⟨ variable (suc zero) ⟩ ⟨ variable {!zero!} ⟩) ∋ 𝒈)
     -- → -- (g : Γ , ⟨ A .type ⟩ , ⟨ B .type ⟩ ⊢ {!!})
     -- → (let
     -- → (let C' : ℓ ⊣ Γ , ⟨ ΣF (A .type) (B .type) ⟩ ,
     {-
     → (let 𝑨 = A .sterm
            𝑩 = B .sterm
            Γ⊢A∈ℓ : Γ ⊢ A ∈ ℓ
            Γ⊢A∈ℓ = ?
            Γ,A
            A/B : Γ ,
       )
     -}
     -- → (g : apply (suppose {!!} (suppose ⟨ suppose ⟨ ΣF (A .type) (B .type) ⟩ (A .type) ⟩ (C .type))) {!!} ⊢)
     -- → (g : suppose ⟨ B .type ⟩ (suppose ⟨ A .type ⟩ (apply (C .type) (ΣI ⟨ {!variable !} ⟩ {!!}))) ⊢)
     → (p : Γ ⊢ ΣF 𝑨 𝑩)
     → Γ ⊢ {!applyTerm (C .sterm) (p .sterm)!} ∋ ΣE {!(C .sterm)!} {!g!} (p .sterm)
  𝟙I : Γ ⊢ {!𝟙F!} ∋ 𝟙I

data _⊢_≝_∶_ {N} (Γ : N ctx) : STerm N → STerm N → STerm N → Set where
```
