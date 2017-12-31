
```agda
{-# OPTIONS --allow-unsolved-metas #-}
```

```agda
module Type.deprecated.Term.Layer0.Building where
```

```agda
open import Type.Prelude
```

```agda
Universe = Nat
Variable = Nat
```

Some of the terminology here borrows from Dr. Gergő Érdi in [Universe of scope- and type-safe syntaxes](https://raw.githubusercontent.com/gergoerdi/universe-of-syntax/d7d5952cce76be551ff5869914b273be2d398069/README.md).

Formulas are syntactically-valid things.

```agda
record Binder : Set

data Formula : Set where
  𝒰 : Universe → Formula
  𝓋 : Variable → Formula
  ΠF : Binder → Formula → Formula
  ΠI : Binder → Formula → Formula
  ΠE : Formula → Formula → Formula
  ΣF : Formula → Formula → Formula
  ΣI : Formula → Formula → Formula
  ΣE : Formula → Formula → Formula → Formula
  +F : Formula → Formula → Formula
  +Iˡ : Formula → Formula
  +Iʳ : Formula → Formula
  +E : Formula → Formula → Formula → Formula → Formula
  𝟘F : Formula
  𝟘E : Formula → Formula → Formula
  𝟙F : Formula
  𝟙I : Formula
  𝟙E : Formula → Formula → Formula → Formula
  ℕF : Formula
  ℕIᶻ : Formula
  ℕIˢ : Formula → Formula
  ℕE : Formula → Formula → Formula → Formula → Formula
  =F : Formula → Formula → Formula → Formula
  =I : Formula → Formula
  =E : Formula → Formula → Formula → Formula → Formula → Formula
```

```agda
infix 20 _∶_
record Binder where
  constructor _∶_
  inductive
  field
    variable : Variable
    formula : Formula
open Binder
```

```agda
record Context : Set where
  constructor ⟨_⟩
  field
    {size} : Nat
    binders : Vec Binder size
open Context
```

Combinators for contexts.

```agda
record Contextinator (C : Set) : Set where
  infixl 15 _,_
  field
    _,_ : Context → C → Context
open Contextinator ⦃ … ⦄

instance

  ContextinatorBinder : Contextinator Binder
  ContextinatorBinder .Contextinator._,_ Γ binder = ⟨ binder ∷ Γ .binders ⟩

  ContextinatorContext : Contextinator Context
  ContextinatorContext .Contextinator._,_ Γ Δ = ⟨ vreverse (Δ .binders) v++ Γ .binders ⟩
```

Appendix A.2 appeals to a side-condition on `ctx-EXT` that the added variable be distinct from the other variables listed in the context.

```agda
record Distinctness (D : Set) : Set₁ where
  field
    _∉_ : Variable → D → Set
open Distinctness ⦃ … ⦄

instance

  DistinctnessContext : Distinctness Context
  DistinctnessContext .Distinctness._∉_ x ⟨ [] ⟩ = ⊤
  DistinctnessContext .Distinctness._∉_ x ⟨ (y ∶ formula) ∷ binders ⟩ = x ≢ y × x ∉ ⟨ binders ⟩
```

I mutually-define well-formed contexts with well-typed (and?) well-scoped formulas in such contexts.

Contexts, well-typed.

```agda
data _ctx : Context → Set
```

Formulas, well-typed relative to one another.

```
infix 5 _⊢_∶_
data _⊢_∶_ (Γ : Context) : Formula → Formula → Set
infix 5 _⊢_≝_∶_
data _⊢_≝_∶_ (Γ : Context) : Formula → Formula → Formula → Set
```

```agda
data _ctx where
  ctx-EMP : ⟨ [] ⟩ ctx
  ctx-EXT : ∀ {Γ : Context} {Aₙ : Formula} {ℓ}
          → Γ ⊢ Aₙ ∶ 𝒰 ℓ
          → ∀ {xₙ}
          → xₙ ∉ Γ
          → ⟨ (xₙ ∶ Aₙ) ∷ Γ .binders ⟩ ctx
```

(I wonder in the above if the orange slime is as toxic as the green.)

simultaneous substitution

```agda

data DistinctFromVariables {N} (x : Variable) (xs : Vec Variable N) : Set where
  ⟨_⟩ : ((p : Fin N) → indexVec xs p ≢ x) → DistinctFromVariables x xs

instance

  DistinctnessVariables : ∀ {N} → Distinctness (Vec Variable N)
  DistinctnessVariables .Distinctness._∉_ = DistinctFromVariables

data Distinct : ∀ {N} → Vec Variable N → Set where
  [] : Distinct []
  _⊀_∷_ : (x : Variable)
        → ∀ {N} {xs : Vec Variable N}
        → x ∉ xs → Distinct xs → Distinct (x ∷ xs)
```

```agda
_[_←_] : Formula → ∀ {N} → Vec Formula N → {vars : Vec Variable N} → Distinct vars → Formula
𝒰 ℓ [ σs ← vs ] = 𝒰 ℓ
𝓋 x [ σs ← vs ] = {!!}
ΠF (x ∶ A) B [ σs ← vs ] = {!!}
ΠI x φ [ σs ← vs ] = {!!}
ΠE φ φ₁ [ σs ← vs ] = {!!}
ΣF φ φ₁ [ σs ← vs ] = {!!}
ΣI φ φ₁ [ σs ← vs ] = {!!}
ΣE φ φ₁ φ₂ [ σs ← vs ] = {!!}
+F φ φ₁ [ σs ← vs ] = {!!}
+Iˡ φ [ σs ← vs ] = {!!}
+Iʳ φ [ σs ← vs ] = {!!}
+E φ φ₁ φ₂ φ₃ [ σs ← vs ] = {!!}
𝟘F [ σs ← vs ] = {!!}
𝟘E φ φ₁ [ σs ← vs ] = {!!}
𝟙F [ σs ← vs ] = {!!}
𝟙I [ σs ← vs ] = {!!}
𝟙E φ φ₁ φ₂ [ σs ← vs ] = {!!}
ℕF [ σs ← vs ] = {!!}
ℕIᶻ [ σs ← vs ] = {!!}
ℕIˢ φ [ σs ← vs ] = {!!}
ℕE φ φ₁ φ₂ φ₃ [ σs ← vs ] = {!!}
=F φ φ₁ φ₂ [ σs ← vs ] = {!!}
=I φ [ σs ← vs ] = {!!}
=E φ φ₁ φ₂ φ₃ φ₄ [ σs ← vs ] = {!!}
```

admissable rules (mutually, to be proven)

```agda
wkg₁ : ∀ {Γ} {Δ : Context} {x A B b ℓ}
     → Γ ⊢ A ∶ 𝒰 ℓ
     → Γ , Δ ⊢ b ∶ B
     → x ∉ Γ -- the weakening variable must not be confused for anything in its suffix
     → Γ , x ∶ A , Δ ⊢ b ∶ B

wkg₂ : ∀ {Γ} {Δ : Context} {x A B b c ℓ}
     → Γ ⊢ A ∶ 𝒰 ℓ
     → Γ , Δ ⊢ b ≝ c ∶ B
     → x ∉ Γ
     → Γ , x ∶ A , Δ ⊢ b ≝ c ∶ B

-- subst₁ :
```

```agda
data _⊢_∶_ (Γ : Context) where
  var : Γ ctx
      → (i : Fin (Γ .size))
      → (let binder = indexVec (Γ .binders) i)
      → Γ ⊢ 𝓋 (binder .variable) ∶ binder .formula
  ≝-subst
    : ∀ {a A B ℓ}
    → Γ ⊢ a ∶ A
    → Γ ⊢ A ≝ B ∶ 𝒰 ℓ
    → Γ ⊢ a ∶ B
  𝒰I : Γ ctx
     → ∀ {ℓ}
     → Γ ⊢ 𝒰 ℓ ∶ 𝒰 (suc ℓ)
  𝒰C : ∀ {A ℓ}
     → Γ ⊢ A ∶ 𝒰 ℓ
     → Γ ⊢ A ∶ 𝒰 (suc ℓ)
  ΠF : ∀ {A x B ℓ}
     → Γ ⊢ A ∶ 𝒰 ℓ
     → Γ , x ∶ A ⊢ B ∶ 𝒰 ℓ
     → Γ ⊢ ΠF (x ∶ A) B ∶ 𝒰 ℓ
  ΠI : ∀ {x A b B}
     → Γ , x ∶ A ⊢ b ∶ B
     → Γ ⊢ ΠI (x ∶ A) b ∶ ΠF (x ∶ A) B
  ΠE : ∀ {f x A B a}
     → Γ ⊢ f ∶ ΠF (x ∶ A) B
     → Γ ⊢ a ∶ A
     → Γ ⊢ ΠE f a ∶ B [ a ∷ [] ← x ⊀ ⟨ (λ { () refl}) ⟩ ∷ []  ] -- putting a `refl` in the absurdity proof makes the proof of wkg₁ easier for case `ΠE`.
```

```agda
data _⊢_≝_∶_ (Γ : Context) where
  ≝-reflexivity
    : ∀ {a A}
    → Γ ⊢ a ∶ A
    → Γ ⊢ a ≝ a ∶ A
  ≝-symmetry
    : ∀ {a b A}
    → Γ ⊢ a ≝ b ∶ A
    → Γ ⊢ b ≝ a ∶ A
  ≝-transitivity
    : ∀ {a b c A}
    → Γ ⊢ a ≝ b ∶ A
    → Γ ⊢ b ≝ c ∶ A
    → Γ ⊢ a ≝ c ∶ A
  ≝-subst
    : ∀ {a b A B ℓ}
    → Γ ⊢ a ≝ b ∶ A
    → Γ ⊢ A ≝ B ∶ 𝒰 ℓ
    → Γ ⊢ a ≝ b ∶ B
  ΠC
    : ∀ {x a A b B}
    → Γ , x ∶ A ⊢ b ∶ B
    → Γ ⊢ a ∶ A
    → Γ ⊢ ΠE (ΠI (x ∶ A) b) a ≝ b [ a ∷ [] ← x ⊀ ⟨ (λ ()) ⟩ ∷ [] ] ∶ B [ a ∷ [] ← x ⊀ ⟨ (λ ()) ⟩ ∷ [] ]
  ΠU
    : ∀ {x A B f}
    → Γ ⊢ f ∶ ΠF (x ∶ A) B
    → Γ ⊢ f ≝ ΠI (x ∶ A) (ΠE f (𝓋 x)) ∶ ΠF (x ∶ A) B
  ΠI : ∀ {x A b b' B}
     → Γ , x ∶ A ⊢ b ≝ b' ∶ B
     → Γ ⊢ ΠI (x ∶ A) b ≝ ΠI (x ∶ A) b' ∶ ΠF (x ∶ A) B
```

```agda
wkg₁ {⟨ [] ⟩} {⟨ [] ⟩} x₁ (var x₂ ()) x₃
wkg₁ {⟨ [] ⟩} {⟨ [] ⟩} {x} {X} {B} {b} []⊢X∶𝒰 []⊢b∶B@(≝-subst {A = A} []⊢b∶A []⊢A=B∶𝒰) _ = ≝-subst {A = A} (wkg₁ {_} {⟨ [] ⟩} []⊢X∶𝒰 []⊢b∶A _) (wkg₂ {_} {⟨ [] ⟩} []⊢X∶𝒰 []⊢A=B∶𝒰 _)
wkg₁ {⟨ [] ⟩} {⟨ [] ⟩} x₁ (𝒰I x₂) x₃ = 𝒰I (ctx-EXT x₁ unit)
wkg₁ {⟨ [] ⟩} {⟨ [] ⟩} x₁ (𝒰C x₂) x₃ = 𝒰C (wkg₁ {Δ = ⟨ [] ⟩} x₁ x₂ _)
wkg₁ {⟨ [] ⟩} {⟨ [] ⟩} {x} {X} []⊢X∶𝒰 (ΠF {A} {a} []⊢A∶𝒰 B) x₃ = ΠF (wkg₁ {Δ = ⟨ [] ⟩} []⊢X∶𝒰 []⊢A∶𝒰 _) (wkg₁ {⟨ [] ⟩} {Δ = ⟨ a ∶ A ∷ [] ⟩} {x} {X} []⊢X∶𝒰 B _)
wkg₁ {⟨ [] ⟩} {⟨ [] ⟩} x₁ (ΠI x₂) x₃ = ΠI (wkg₁ {Δ = ⟨ _ ∶ _ ∷ [] ⟩} x₁ x₂ _)
wkg₁ {⟨ [] ⟩} {⟨ [] ⟩} {x} {X} []⊢X∶𝒰 (ΠE {f} {y} {A} {B} {a} []⊢f∶ΠFy∶AB []⊢a∶A) _ = _⊢_∶_.ΠE {Γ = {!!}} {f = f} {y} {A} {{!B!}} {a} {!!} {!!}
-- _⊢_∶_.ΠE {Γ = ⟨ x ∶ X ∷ [] ⟩} {f = f} {y} {A} {B} {a} {!!} {!!}
-- _⊢_∶_.ΠE {Γ = ⟨ x ∶ X ∷ [] ⟩} {f = f} {y} {A} {B} {a} {!(wkg₁ {Δ = ⟨ [] ⟩} []⊢X∶𝒰 []⊢f∶ΠFy∶AB _)!} {!{!wkg₁ {⟨ [] ⟩} {⟨ [] ⟩} []⊢X∶𝒰 []⊢a∶A _!}!}
-- {Γ = ⟨ x ∶ X ∷ [] ⟩} {Δ = ⟨ [] ⟩}
-- _⊢_∶_.ΠE  {Γ = ⟨ x ∶ X ∷ [] ⟩}
-- _⊢_∶_.ΠE {Γ = ⟨ _ ∶ _ ∷ [] ⟩} (wkg₁ {Δ = ⟨ {![]!} ⟩} {![]⊢X∶𝒰!} {![]⊢f∶ΠFx∶AB!} _) {!!}
-- ΠE {x = {!!}} {{!!}} {{!!}} {!(wkg₁ {Δ = ⟨ [] ⟩} x₁ x₂ _)!} {!wkg₁ {Δ = ⟨ [] ⟩} x₁ x₅ _!}
wkg₁ {⟨ x ∷ binders₁ ⟩} {Δ = ⟨ [] ⟩} x₁ x₂ x₃ = {!!}
wkg₁ {Γ} {⟨ x ∷ binders₁ ⟩} x₁ x₂ x₃ = {!!}

wkg₂ = {!!}
```
