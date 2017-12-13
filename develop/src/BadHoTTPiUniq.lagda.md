
In the HoTT book, in Appendix 2 (Formal Type Theory), the Π-UNIQ rule is given as:

        Γ ⊢ f : Π (x : A) B
    -------------------------------
    Γ ⊢ f ≡ (λx.f(x)) : Π (x : A) B

I believe a side-condition should be added, saying that `x` does not occur free in `f`. In the below I demonstrate that, without this condition, I can construct the perverse judgement:

    (x₀ : U₀ ⟶ U₀) ⊢ (λ (x₀ : U₀) . x₀ (x₀)) : U₀ ⟶ U₀

```agda
module BadHoTTPiUniq where
```

Imports from the Agda Standard Library.

```agda
open import Data.Vec
open import Data.Fin
open import Data.Empty
open import Data.Unit
open import Data.Nat
open import Relation.Binary.PropositionalEquality
open import Data.Product renaming (_,_ to _,,_)
```

In this abridged type theory, expressions and abstractions include universes, variables, and constructors for pi-types.

```agda
Universe = ℕ
Variable = ℕ

record Abstraction (N : ℕ) : Set

data Expression : Set where
  U : Universe → Expression
  var : Variable → Expression
  -- Π formation
  ΠF : Expression → Abstraction 1 → Expression
  -- Π introduction (lambda)
  ΠI : Expression → Abstraction 1 → Expression
  -- Π elimination (application)
  ΠE : Expression → Expression → Expression

record Abstraction (N : ℕ) where
  constructor _↦_
  inductive
  field
    binders : Vec Variable N
    expression : Expression

infix 10 _↦₁_
pattern _↦₁_ x A = (x ∷ []) ↦ A
```

Contexts (not necessarily well-formed) are snoc-lists of contextual elements, which are themselves pairs of variables and expressions.

```agda
infix 18 _∶_
record ContextualElement : Set where
  constructor _∶_
  field
    variable : Variable
    expression : Expression
open ContextualElement

infixl 15 _,_
data Context : Set where
  ε : Context
  _,_ : Context → ContextualElement → Context
```

Some utilities for contexts.

```agda
lengthContext : Context → ℕ
lengthContext ε = zero
lengthContext (Γ , (_ ∶ _)) = suc (lengthContext Γ)

indexContext : (Γ : Context) → Fin (lengthContext Γ) → ContextualElement
indexContext Γ x with lengthContext Γ | inspect lengthContext Γ
indexContext ε () | _ | [ refl ]
indexContext (Γ , x ∶ φ) zero    | _ | [ refl ] = x ∶ φ
indexContext (Γ , _ ∶ _) (suc i) | _ | [ refl ] = indexContext Γ i
```

Ensuring that a variable is not already listed in a context.

```agda
_∉C_ : Variable → Context → Set
_∉C_ v ε = ⊤
_∉C_ v (Γ , x ∶ A) = v ≢ x × v ∉C Γ
```

Mutually-defined judgements.

```agda
data _ctx : Context → Set

infix 5 _⊢_∶_
data _⊢_∶_ (Γ : Context) : Expression → Expression → Set

infix 5 _⊢_≝_∶_
data _⊢_≝_∶_ (Γ : Context) : Expression → Expression → Expression → Set
```

Well-formed contexts.

```agda
infix 10 _ctx
data _ctx where
  ctx-EMP : ε ctx
  ctx-EXT : ∀ {Γ : Context} {Aₙ : Expression} {ℓ}
          → Γ ⊢ Aₙ ∶ U ℓ
          → ∀ {xₙ}
          → xₙ ∉C Γ
          → Γ , xₙ ∶ Aₙ ctx
```

Typing judgements.

```agda
data _⊢_∶_ (Γ : Context) where
  vble : Γ ctx
       → (i : Fin (lengthContext Γ))
       → ∀ {binder}
       → indexContext Γ i ≡ binder
       → Γ ⊢ var (variable binder) ∶ expression binder
  U-INTRO : Γ ctx
          → ∀ {ℓ}
          → Γ ⊢ U ℓ ∶ U (suc ℓ)
  Π-FORM : ∀ {A x B ℓ}
         → Γ ⊢ A ∶ U ℓ
         → Γ , x ∶ A ⊢ B ∶ U ℓ
         → Γ ⊢ ΠF A (x ↦₁ B) ∶ U ℓ
```

Definitional equality.

```agda
data _⊢_≝_∶_ (Γ : Context) where
  ΠU
    : ∀ {x A B f}
    → Γ ⊢ f ∶ ΠF A (x ↦₁ B)
    → Γ ⊢ f ≝ ΠI A (x ↦₁ ΠE f (var x)) ∶ ΠF A (x ↦₁ B)
```

An admissable rule (according to Appendix 2), here postulated.

```agda
postulate
  ≝-project₂ : ∀ {Γ a b A}
            → Γ ⊢ a ≝ b ∶ A
            → Γ ⊢ b ∶ A
```

Given the above, I can construct

    (x₀ : U₀ ⟶ U₀) ⊢ (λ (x₀ : U₀) . x₀ (x₀)) : U₀ ⟶ U₀

which is weird, as it involves applying a member of U₀ to itself.

```agda
weird : ε , 0 ∶ ΠF (U 0) (0 ↦₁ U 0)
      ⊢ ΠI (U 0) (0 ↦₁ ΠE (var 0) (var 0))
      ∶ ΠF (U 0) (0 ↦₁ U 0)
weird = ≝-project₂ (ΠU (vble (ctx-EXT (Π-FORM (U-INTRO ctx-EMP)
                                              (U-INTRO (ctx-EXT (U-INTRO ctx-EMP)
                                                                tt)))
                                      tt)
                             zero
                             refl))
```
