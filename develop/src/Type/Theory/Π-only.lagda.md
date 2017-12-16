
```agda
{-# OPTIONS --allow-unsolved-metas #-}
```

```agda
module Type.Theory.Π-only where
```

```agda
open import Type.Prelude
```

```agda
module #1 where
```

```agda
  Universe = Nat
  NamedVariable = Nat
  IndexedVariable = Fin
```

```agda
  data IndexedExpression (N : Nat) : Set where
    𝒰 : Universe → IndexedExpression N
    𝓋 : IndexedVariable N → IndexedExpression N
    ΠF : IndexedExpression N → IndexedExpression (suc N) → IndexedExpression N
    ΠI : IndexedExpression N → IndexedExpression (suc N) → IndexedExpression N
    ΠE : IndexedExpression N → IndexedExpression N → IndexedExpression N

  data AbnormalIndexedExpression (N : Nat) : Set where
    𝒰 : Universe → AbnormalIndexedExpression N
    𝓋 : IndexedVariable N → AbnormalIndexedExpression N
    ΠF : AbnormalIndexedExpression N → AbnormalIndexedExpression (suc N) → AbnormalIndexedExpression N
    ΠI : AbnormalIndexedExpression N → AbnormalIndexedExpression (suc N) → AbnormalIndexedExpression N
    ΠE : AbnormalIndexedExpression N → AbnormalIndexedExpression N → AbnormalIndexedExpression N
    -- N simultaneous substitutions in an expression with N free variables
    β : Vec (AbnormalIndexedExpression N) N → AbnormalIndexedExpression N → AbnormalIndexedExpression N

  data ScopedNamedExpression {N} (Δ : Vec NamedVariable N) : Set where
    𝒰 : Universe → ScopedNamedExpression Δ
    𝓋 : Fin N → ScopedNamedExpression Δ
    ΠF : ScopedNamedExpression Δ → ∀ x → ScopedNamedExpression (x ∷ Δ) → ScopedNamedExpression Δ
    ΠI : ScopedNamedExpression Δ → ∀ x → ScopedNamedExpression (x ∷ Δ) → ScopedNamedExpression Δ
    ΠE : ScopedNamedExpression Δ → ScopedNamedExpression Δ → ScopedNamedExpression Δ

  data NamedExpression : Nat → Set where
    𝒰 : Universe → NamedExpression 0
    𝓋 : NamedVariable → NamedExpression 0
    _↦_ : ∀ {N} → Vec NamedVariable N → NamedExpression 0 → NamedExpression N
    ΠF : NamedExpression 0 → NamedExpression 1 → NamedExpression 0
    ΠI : NamedExpression 0 → NamedExpression 1 → NamedExpression 0
    ΠE : NamedExpression 0 → NamedExpression 0 → NamedExpression 0
```

```agda
  infix 10 _↦₁_
  pattern _↦₁_ x A = (x ∷ []) ↦ A
```

```agda
  infixl 15 _,_∶_
  data NamedContext : Nat → Set where
    ε : NamedContext 0
    _,_∶_ : ∀ {N} → NamedContext N → NamedVariable → NamedExpression 0 → NamedContext (suc N)

  data IndexedContext : Nat → Set where
    ε : IndexedContext 0
    _,_ : ∀ {N} → IndexedContext N → IndexedExpression N → IndexedContext (suc N)
```

```agda
  substituteNamed : ∀ {M} → NamedContext M → ∀ {N} → NamedExpression N → NamedExpression N
  substituteNamed σ (𝒰 x₁) = {!!}
  substituteNamed σ (𝓋 x₁) = {!!}
  substituteNamed σ ([] ↦ x₂) = substituteNamed σ x₂
  substituteNamed σ ((x ∷ x₁) ↦ x₂) = substituteNamed (σ , x ∶ 𝓋 x) ({!!} ↦ x₂)
  substituteNamed σ (ΠF x₁ x₂) = ΠF {!!} (substituteNamed σ x₂)
  substituteNamed σ (ΠI x₁ x₂) = {!!}
  substituteNamed σ (ΠE x₁ x₂) = {!!}
```

record WellScopedNamedExpression {N} (Γ : NamedContext N) : Set where
  field
    expression : NamedExpression 0

data _nctx : NamedContext → Set
  where
infix 5 _⊢_∶_
data _⊢_∶_ (Γ : NamedContext) : NamedExpression 0 → NamedExpression 0 → Set
  where
infix 5 _⊢_≝_∶_
data _⊢_≝_∶_ (Γ : NamedContext) : NamedExpression 0 → NamedExpression 0 → NamedExpression 0 → Set
  where

well-scoped context
well-typed context

data _[_←_]→_
data _⊢_∶_ :
data CExpression {N} (Δ :  N) : Set where

```agda
module #2 where
```

```agda
  Universe = Nat
  Variable = Nat
  data Formula : Set
  record Abstraction (#binders : Nat) : Set
  data Signature : ∀ {N} → Vec Nat N → Set
  data Formula where
    𝒰 : Universe → Formula
    𝓋 : Variable → Formula
    ΠF : Signature (0 ∷ 1 ∷ []) → Formula
    ΠI : Signature (0 ∷ 1 ∷ []) → Formula
    ΠE : Signature (0 ∷ 0 ∷ []) → Formula
    ΣF : Signature (0 ∷ 1 ∷ []) → Formula
    ΣI : Signature (0 ∷ 0 ∷ []) → Formula
    ΣE : Signature (1 ∷ 2 ∷ 0 ∷ []) → Formula
  record Abstraction (#binders : Nat) where
    constructor _↦_
    inductive
    field
      binders : Vec Variable #binders
      formula : Formula

  data Signature where
    [] : Signature []
    -- FIXME I would like this next constructor to be named `_∷_` but there is a problem with `agda2-refine` (see agda issue #2873.
    _∷∷_ : ∀ {v} → Abstraction v
         → ∀ {N} {vs : Vec Nat N} → Signature vs
         → Signature (v ∷ vs)
```

```agda
  testFormula₁ : Formula
  testFormula₁ = ΠF (([] ↦ 𝒰 0) ∷∷ (((1 ∷ []) ↦ 𝓋 1) ∷∷ []))

  testFormula₂ : Formula
  testFormula₂ = ΠF (([] ↦ 𝒰 0) ∷∷ (((0 ∷ []) ↦ 𝓋 0) ∷∷ []))
```

```agda
  postulate
    _α≡_ : Formula → Formula → Set

  testα≡ : testFormula₁ α≡ testFormula₂
  testα≡ = {!!}
```


```agda
module #3 where
```

```agda
  open import Type.DeBruijn

  Universe = Nat
  Variable = Nat
  data Formula (N : Nat) : Set
  data Signature (N : Nat) : ∀ {M} → Vec Nat M → Set
  data Formula (N : Nat) where
    𝒰 : Universe → Formula N
    𝓋 : Fin N → Formula N
    ΠF : Signature N (0 ∷ 1 ∷ []) → Formula N
    ΠI : Signature N (0 ∷ 1 ∷ []) → Formula N
    ΠE : Signature N (0 ∷ 0 ∷ []) → Formula N
    ΣF : Signature N (0 ∷ 1 ∷ []) → Formula N
    ΣI : Signature N (0 ∷ 0 ∷ []) → Formula N
    ΣE : Signature N (1 ∷ 2 ∷ 0 ∷ []) → Formula N
  data Signature (N : Nat) where
    [] : Signature N []
    -- FIXME I would like this next constructor to be named `_∷_` but there is a problem with `agda2-refine` (see agda issue #2873.
    _∷∷_ : ∀ {v} → Formula (v + N)
         → ∀ {M} {vs : Vec Nat M} → Signature N vs
         → Signature N (v ∷ vs)
```

```agda
  testFormula₁ : Formula 0
  testFormula₁ = ΠF (𝒰 0 ∷∷ (𝓋 0 ∷∷ []))

  testFormula₂ : Formula 1
  testFormula₂ = ΠF (𝒰 0 ∷∷ (𝓋 0 ∷∷ []))

  testFormula₃ : Formula 1
  testFormula₃ = ΠF (𝒰 0 ∷∷ (𝓋 1 ∷∷ []))

  testFormula₄ : Formula 2
  testFormula₄ = ΠF (𝒰 0 ∷∷ (𝓋 2 ∷∷ []))
```

```agda
  weakenFormulaFrom : ∀ {N} → Fin (suc N) → Formula N → Formula (suc N)
  weakenSignatureFrom : ∀ {N} → Fin (suc N) → ∀ {M} {xs : Vec Nat M} → Signature N xs → Signature (suc N) xs

  weakenFormulaFrom from (𝒰 ℓ) = 𝒰 ℓ
  weakenFormulaFrom from (𝓋 x) = 𝓋 (weakenFinFrom from x)
  weakenFormulaFrom from (ΠF s) = ΠF (weakenSignatureFrom from s)
  weakenFormulaFrom from (ΠI s) = ΠI (weakenSignatureFrom from s)
  weakenFormulaFrom from (ΠE s) = ΠE (weakenSignatureFrom from s)
  weakenFormulaFrom from (ΣF s) = ΣF (weakenSignatureFrom from s)
  weakenFormulaFrom from (ΣI s) = ΣI (weakenSignatureFrom from s)
  weakenFormulaFrom from (ΣE s) = ΣE (weakenSignatureFrom from s)

  weakenSignatureFrom from [] = []
  weakenSignatureFrom from (_∷∷_ {v} φ s) = (transport Formula auto $ weakenFormulaFrom (transport Fin auto $ weakenFinByFrom v zero from) φ) ∷∷ weakenSignatureFrom from s

  weakenFormulaByFrom : ∀ M {N} → Fin (suc N) → Formula N → Formula (M + N)
  weakenFormulaByFrom zero from = id
  weakenFormulaByFrom (suc by) from φ = transport Formula auto $ weakenFormulaByFrom by (weakenFinFrom zero from) (weakenFormulaFrom from φ)
```

```agda
  testWeaken₁/₂ : weakenFormulaFrom zero testFormula₁ ≡ testFormula₂
  testWeaken₁/₂ = refl

  testWeaken₃/₄ : weakenFormulaFrom zero testFormula₃ ≡ testFormula₄
  testWeaken₃/₄ = refl
```

```agda
  instantiateFormulaAt : ∀ {N} → Fin (suc N) → Formula (suc N) → Formula N → Formula N
  instantiateSignatureAt : ∀ {N} → Fin (suc N) → ∀ {M} {vs : Vec Nat M} → Signature (suc N) vs → Formula N → Signature N vs

  instantiateFormulaAt α (𝒰 ℓ) _ = 𝒰 ℓ
  instantiateFormulaAt α (𝓋 x) φ with α == x
  … | yes _ = φ
  … | no α≢x = 𝓋 (instantiateFinAt α≢x)
  instantiateFormulaAt α (ΠF s) φ = ΠF (instantiateSignatureAt α s φ)
  instantiateFormulaAt α (ΠI s) φ = ΠI (instantiateSignatureAt α s φ)
  instantiateFormulaAt α (ΠE s) φ = ΠE (instantiateSignatureAt α s φ)
  instantiateFormulaAt α (ΣF s) φ = ΣF (instantiateSignatureAt α s φ)
  instantiateFormulaAt α (ΣI s) φ = ΣI (instantiateSignatureAt α s φ)
  instantiateFormulaAt α (ΣE (x ∷∷ x₁ ∷∷ x₂ ∷∷ [])) φ =
    ΣE (instantiateFormulaAt (weakenFinByFrom 1 zero α) x (weakenFormulaByFrom 1 zero φ) ∷∷
        instantiateFormulaAt (weakenFinByFrom 2 zero α) x₁ (weakenFormulaByFrom 2 zero φ) ∷∷
        instantiateFormulaAt α x₂ φ ∷∷ [])
  -- ΣE (instantiateSignatureAt α s φ)
{-
  instantiateFormulaBy : ∀ v → ∀ {N} →
                         Fin (suc N) →
                         Formula (v + suc N) → Formula N → Formula (v + N)
  instantiateFormulaBy zero α x φ = {!instantiateFormulaAt α x φ!}
  instantiateFormulaBy (suc v) α x φ = transport Formula auto $ instantiateFormulaBy v (suc α) (transport Formula auto x) (weakenFormulaFrom zero φ)
-}
  instantiateSignatureAt α [] φ = []
  -- instantiateSignatureAt α (_∷∷_ {v} x s) φ = instantiateFormulaBy v α x φ ∷∷ instantiateSignatureAt α s φ
  {-
  instantiateSignatureAt α (_∷∷_ {zero} x s) φ = instantiateFormulaAt α x φ ∷∷ instantiateSignatureAt α s φ
  instantiateSignatureAt α (_∷∷_ {suc v} x s) φ = instantiateFormulaAt {!!} {!!} {!!} ∷∷ instantiateSignatureAt α s φ
  -}
  instantiateSignatureAt α (_∷∷_ {v} x s) φ =
    instantiateFormulaAt (transport Fin auto $ weakenFinByFrom v zero α)
                         {!(case (auto ofType (v + suc _ ≡ suc (v + _))) of λ {refl → x}) ofType Formula (suc (v + _))!}
                         (weakenFormulaByFrom v zero φ) ∷∷
    instantiateSignatureAt α s φ
  {-
  instantiateSignatureAt α (_∷∷_ {v} x s) φ =
    instantiateFormulaAt (transport Fin auto $ weakenFinByFrom v zero α)
                         {!(transport Formula auto x)!}
                         (weakenFormulaByFrom v zero φ) ∷∷
    instantiateSignatureAt α s φ
  -}
```

```agda
  data Context : Nat → Set
  data _⊢_∶_ {N} (Γ : Context N) : Formula N → Formula N → Set
  data _⊢_≝_∶_ {N} (Γ : Context N) : Formula N → Formula N → Formula N → Set
  data _⇒_ : ∀ {M} {Γ : Context M} {a A : Formula M}
               {N} {Δ : Context N} {b B : Formula N}
             → Γ ⊢ a ∶ A → Δ ⊢ b ∶ B
             → Set

  infixr 5 _∷∷_
  -- Context N has N formulas, with the outermost formula being of context N - 1
  data Context where
    [] : Context 0
    _∷∷_ : ∀ {N} → Formula N → Context N → Context (suc N)

  -- a sub-context from M to N elements, outermost is N elements
  data Delta : Nat → Nat → Set where
    [] : ∀ {N} → Delta N N
    _∷∷_ : ∀ {M N} → Formula N → Delta M N → Delta M (suc N)

  -- A sub-context from M to N elements, outermost is M elements
  data Atled : Nat → Nat → Set where
    [] : ∀ {M} → Atled M M
    _∷∷_ : ∀ {M N} → Formula M → Atled (suc M) N → Atled M N

  D2C : ∀ {N} → Delta 0 N → Context N
  D2C [] = []
  D2C (δ ∷∷ Δ) = δ ∷∷ D2C Δ

  C2D : ∀ {N} → Context N → Delta 0 N
  C2D [] = []
  C2D (x ∷∷ x₁) = x ∷∷ C2D x₁

  appendAtled : ∀ {M N} → Formula N → Atled M N → Atled M (suc N)
  appendAtled x [] = x ∷∷ []
  appendAtled x (x₁ ∷∷ x₂) = x₁ ∷∷ appendAtled x x₂

  C2A : ∀ {N} → Context N → Atled 0 N
  C2A [] = []
  C2A (γ ∷∷ Γ) = appendAtled γ (C2A Γ)

  _∙_ : ∀ {M N O} → Delta N O → Delta M N → Delta M O
  [] ∙ X = X
  (z ∷∷ Y) ∙ X = z ∷∷ (Y ∙ X)

  toAtled : ∀ {M N} → Delta M N → Atled M N
  toAtled {M} {.M} [] = []
  toAtled {M} {.(suc _)} (x ∷∷ x₁) = appendAtled x (toAtled x₁)

  wkAtled : ∀ {M N} → Atled M N → Atled (suc M) (suc N)
  wkAtled [] = []
  wkAtled (x ∷∷ x₁) = weakenFormulaFrom zero x ∷∷ wkAtled x₁

  wkAtledBy : ∀ by {M N} → Atled M N → Atled (by + M) (by + N)
  wkAtledBy zero x = x
  wkAtledBy (suc by) x = transport₂ Atled auto auto $ wkAtledBy by (wkAtled x)

  toDelta : ∀ {M N} → Atled M N → Delta M N
  toDelta [] = []
  toDelta (x ∷∷ x₁) = toDelta x₁ ∙ (x Delta.∷∷ [])

  _++++_ : ∀ {M N} → Context M → Atled M N → Context N
  Γ ++++ [] = Γ
  Γ ++++ (δ ∷∷ Δ) = (δ ∷∷ Γ) ++++ Δ

  _at_ : ∀ {N} → Context N → Fin N → Formula N
  (φ ∷∷ Γ) at zero = weakenFormulaFrom zero φ
  (_ ∷∷ Γ) at suc n = weakenFormulaFrom zero (Γ at n)

  wkTyped : ∀ {N} {Γ : Context N} {a A Δ}
          → Γ ⊢ a ∶ A
          → ∀ {a' A'}
          → weakenFormulaFrom zero a ≡ a'
          → weakenFormulaFrom zero A ≡ A'
          → (Δ ∷∷ Γ) ⊢ a' ∶ A'
  wkTyped x x₁ x₂ = {!!}

  getFinFromDelta : ∀ {M N} → Delta M N → Fin (suc N)
  getFinFromDelta [] = zero
  getFinFromDelta (x ∷∷ x₁) = suc (getFinFromDelta x₁)

  testDelta : Delta 1 0 → ⊥
  testDelta ()

  wkTypedByFrom
    : ∀ d
    → ∀ {M N}
    → {Γ : Context M} {Δ : Delta M N}
    → {Ξ : Delta M (d + M)}
    → ∀ {a A}
    → (Γ ++++ toAtled Δ) ⊢ a ∶ A
    → (let Δ' = toDelta (wkAtledBy d (toAtled Δ)))
    → (Γ ++++ toAtled (Δ' ∙ Ξ)) ⊢ weakenFormulaByFrom d (getFinFromDelta Δ) a ∶ weakenFormulaByFrom d (getFinFromDelta Δ) A
  wkTypedByFrom zero {Ξ = []} x = {!x!}
  wkTypedByFrom zero {Ξ = x₁ ∷∷ _∷∷_ {N = zero} x₂ ()} x
  wkTypedByFrom zero {Ξ = x₁ ∷∷ _∷∷_ {N = suc zero} x₂ (x₃ ∷∷ ())} x
  wkTypedByFrom zero {Ξ = x₁ ∷∷ _∷∷_ {N = suc (suc .(suc (suc _)))} x₂ (x₃ ∷∷ x₄ ∷∷ x₅ ∷∷ x₆ ∷∷ Ξ)} x = {!!}
  wkTypedByFrom (suc d) x = {!!}

  weakenThroughDelta : ∀ {M N} → Formula M → Delta M N → Formula N
  weakenThroughDelta x [] = x
  weakenThroughDelta x (x₁ ∷∷ x₂) = weakenFormulaFrom zero $ weakenThroughDelta x x₂

  tcInstantiateAt :
    ∀ {M} {Γ : Context M}
      {N} {Δ : Delta M N}
      {a A}
      {b B}
    → ((A ∷∷ Γ) ++++ wkAtled (toAtled Δ)) ⊢ b ∶ B
    → (Γ ++++ toAtled Δ) ⊢ a ∶ weakenThroughDelta A Δ
    → Formula N
  tcInstantiateAt {Δ = Δ} {a = a} {b = b} x x₁ = instantiateFormulaAt (getFinFromDelta Δ) b a

  tcApplyTerm :
    ∀ {N} {Γ : Context N} {a A b B}
    → (A ∷∷ Γ) ⊢ b ∶ B
    → Γ ⊢ a ∶ A
    → Formula N
  tcApplyTerm {a = a} {b = b} _ _ = instantiateFormulaAt zero b a

  tcApplyType :
    ∀ {N} {Γ : Context N} {a A b B}
    → (A ∷∷ Γ) ⊢ b ∶ B
    → Γ ⊢ a ∶ A
    → Formula N
  tcApplyType {a = a} {B = B} _ _ = instantiateFormulaAt zero B a

  tcApplyCorrect :
    ∀ {N} {Γ : Context N} {a A b B}
    → (Γ,A⊢b∶B : (A ∷∷ Γ) ⊢ b ∶ B)
    → (Γ⊢a∶A : Γ ⊢ a ∶ A)
    → Γ ⊢ tcApplyTerm Γ,A⊢b∶B Γ⊢a∶A ∶ tcApplyType Γ,A⊢b∶B Γ⊢a∶A
  tcApplyCorrect = {!!}

  data _⊢_∶_ {N} (Γ : Context N) where
    𝒰 : ∀ {ℓ} → Γ ⊢ 𝒰 ℓ ∶ 𝒰 (suc ℓ)
    𝓋 : ∀ v {φ} → Γ at v ≡ φ → Γ ⊢ 𝓋 v ∶ φ
    ΠF : ∀ {A B ℓ}
       → Γ ⊢ A ∶ 𝒰 ℓ
       → (A ∷∷ Γ) ⊢ B ∶ 𝒰 ℓ
       → Γ ⊢ ΠF (A ∷∷ B ∷∷ []) ∶ 𝒰 ℓ
    ΠI : ∀ {A B b}
       → (A ∷∷ Γ) ⊢ b ∶ B
       → Γ ⊢ ΠI (A ∷∷ b ∷∷ []) ∶ ΠF (A ∷∷ B ∷∷ [])
    ΠE : ∀ {f A B a}
       → Γ ⊢ f ∶ ΠF (A ∷∷ B ∷∷ [])
       → (⊢a : Γ ⊢ a ∶ A)
       → (let ⊢B : ∃ λ ℓ → (A ∷∷ Γ) ⊢ B ∶ 𝒰 ℓ
              ⊢B = {!!})
       → Γ ⊢ ΠE (f ∷∷ a ∷∷ []) ∶ tcInstantiateAt {Δ = []} (snd ⊢B) ⊢a
    ΣF : ∀ {A B ℓ}
       → Γ ⊢ A ∶ 𝒰 ℓ
       → (A ∷∷ Γ) ⊢ B ∶ 𝒰 ℓ
       → Γ ⊢ ΣF (A ∷∷ B ∷∷ []) ∶ 𝒰 ℓ
    ΣI : ∀ {A B a b}
       → ∀ {ℓ} {⊢B : (A ∷∷ Γ) ⊢ B ∶ 𝒰 ℓ}
       → (⊢a : Γ ⊢ a ∶ A)
       → Γ ⊢ b ∶ tcInstantiateAt {Δ = []} ⊢B ⊢a
       → Γ ⊢ ΣI (a ∷∷ b ∷∷ []) ∶ ΣF (A ∷∷ B ∷∷ [])
    ΣE : ∀ {A B C ℓ g p}
       → (⊢C : (ΣF (A ∷∷ B ∷∷ []) ∷∷ Γ) ⊢ C ∶ 𝒰 ℓ)
       → ∀ {C[ΣIab]}
       → (let C[ΣIab]F₁ : Formula (suc (suc N))
              C[ΣIab]F₁ = instantiateFormulaAt 0 (weakenFormulaByFrom 2 1 C) (ΣI (𝓋 1 ∷∷ 𝓋 0 ∷∷ [])))
       → (let C[ΣIab]F₂ : Formula (suc (suc N))
              C[ΣIab]F₂ = instantiateFormulaAt 2 (weakenFormulaByFrom 2 0 C) (ΣI (𝓋 1 ∷∷ 𝓋 0 ∷∷ [])))
       → (let C[ΣIab]F₃ : Formula (suc (suc N))
              C[ΣIab]F₃ = tcInstantiateAt {Γ = Γ} {Δ = B ∷∷ A ∷∷ []} {A = ΣF (A ∷∷ B ∷∷ [])} (wkTyped (wkTyped ⊢C refl refl) refl refl) (ΣI {ℓ = ℓ} {{!!}} (𝓋 1 refl) (𝓋 0 {!refl!})))
       → (let C[ΣIab]F₄ : Formula (suc (suc N))
              C[ΣIab]F₄ = tcInstantiateAt {Γ = B ∷∷ A ∷∷ Γ} {Δ = []} {A = weakenThroughDelta (ΣF (A ∷∷ B ∷∷ [])) (B ∷∷ A ∷∷ [])} (wkTypedByFrom 2 {Γ = Γ} {Δ = ΣF (A ∷∷ B ∷∷ []) ∷∷ []} {Ξ = B ∷∷ A ∷∷ []} ⊢C) (ΣI {ℓ = ℓ} {{!!}} (𝓋 1 refl) (𝓋 0 {!!})))
       → (let C[ΣIab]⊢ : (B ∷∷ A ∷∷ Γ) ⊢ C[ΣIab]F₃ ∶ 𝒰 ℓ
              C[ΣIab]⊢ = {!ΠE {!!} (ΣI (𝓋 1 {!!}) (𝓋 0 {!!}))!})
       → (let C[ΣIab]⊢' : (B ∷∷ A ∷∷ Γ) ⊢ C[ΣIab]F₄ ∶ 𝒰 ℓ
              C[ΣIab]⊢' = {!ΠE {!!} (ΣI (𝓋 1 {!!}) (𝓋 0 {!!}))!})
       → (let sanity : C[ΣIab]F₁ ≡ C[ΣIab]F₂
              sanity = {!!})
       → (let C-function : Formula N
              C-function = ΠI (ΣF (A ∷∷ B ∷∷ []) ∷∷ C ∷∷ []))
       → (B ∷∷ A ∷∷ Γ) ⊢ ΠE (weakenFormulaByFrom 2 0 C-function ∷∷ ΣI (𝓋 1 ∷∷ 𝓋 0 ∷∷ []) ∷∷ []) ≝ C[ΣIab] ∶ 𝒰 ℓ
       → (B ∷∷ A ∷∷ Γ) ⊢ {!!} ≝ C[ΣIab] ∶ 𝒰 ℓ
       {- λ a b → ΠE C (ΣI a b) -}
       → (B ∷∷ A ∷∷ Γ) ⊢ g ∶ C[ΣIab]F₁
       {-
          λ z → C
          λ a b → g
          λ a b → ΣI a b
       -}
       → Γ ⊢ p ∶ ΣF (A ∷∷ B ∷∷ [])
       → Γ ⊢ ΣE (C ∷∷ g ∷∷ p ∷∷ []) ∶ {!!} -- [_//_] C p

  data _⊢_≝_∶_ {N} (Γ : Context N) where

  data _⇒_ where
    {-
        Γ ⊢ a ∶ A
      → Γ ⊢ γ ∶ 𝒰 ℓ
      → (γ ∷ Γ) ⊢ weakenFormulaFrom zero a ∶ weakenFormulaFrom zero A
    -}
    {-
      (A ∷ Γ) ⊢ b ∶ B
    → Γ ⊢ a ∶ A
    → Γ ⊢ instantiateFormulaAt zero b a ∶ instantiateFormulaAt zero B a
    -}
```
