
```agda
{-# OPTIONS --allow-unsolved-metas #-}
```

```agda
module Type.deprecated.Term.Layer0.HoTTer where
```

```agda
open import Type.Prelude
```

Borrowing from Dr. Gergő Érdi in [Universe of scope- and type-safe syntaxes](https://raw.githubusercontent.com/gergoerdi/universe-of-syntax/d7d5952cce76be551ff5869914b273be2d398069/README.md), an expression is a well-scoped formula.

```agda
open import Type.deprecated.Term.Layer-1.SCTerm
  hiding
    (applyTerm
    ;weakenTermFrom
    ;weakenTermByFrom
    ;instantiateTerm
    ;substituteTerm
    )
  renaming
    (Term to Expr)
  renaming
    (+IL to +Iˡ
    ;+IR to +Iʳ
    ;ℕIZ to ℕIᶻ
    ;ℕIS to ℕIˢ
    )
```

Renaming to make more in-line with the names of rules in Appendix 2 of the HoTT book.

```agda
wkgExpr : ∀ {N} → Fin (suc N) → Expr N → Expr (suc N)
wkgExpr = Type.deprecated.Term.Layer-1.SCTerm.weakenTermFrom
```

It's somewhat troubling that I have need to mention a hidden argument here.

```agda
substExpr : ∀ {M N} → Expr N → Expr (M + suc N) → Expr (M + N)
substExpr {M} a b = Type.deprecated.Term.Layer-1.SCTerm.substituteTerm {M} (transport Expr auto b) a
```

It feels a bit backwards to me to take a well-scoped thing and demote it to a syntactically valid one but my idea is that it will be easier to work with proofs with lessened requirements. The requirement of well-scopedness will be inserted at the appropriate junctures.

```agda
record Form : Set where
  constructor ⟨_⟩
  field
    {size} : Nat
    expr : Expr size
open Form
```

```agda
record Environment : Set where
  constructor ⟨_⟩
  field
    {size} : Nat
    context : Vec Form size
open Environment
```

```agda
data _ctx : Environment → Set
data _⊢_∶_ : Environment → Form → Form → Set where
```

...and in fact it does not work: the "demotion" being really just a wrapper does not have the kind of equality property I would expect out of a true demotion. `Form`s which should be equivalent are distinct per their `size`. So, something like this can't make sense because the `b` in the output is actually of a greater `size` than the `b` in the input.

    wkg₁ : ∀ {...}
         → (x : Γ ⊢ A ∶ 𝒰 ℓ)
         → Γ ++ Δ ⊢ b ∶ B
         → Γ , x ++ Δ ⊢ b ∶ B

Also, the act of defining a valid context (a type-checked `Environment`) is made more difficult because of the need to specify a `size` for the universe `Form` (as I have not done in the below).

```agda
data _ctx where
  ε : ⟨ [] ⟩ ctx
  _,_ : (Γ : Environment) → ∀ {ℓ} {Aₙ : Form} → Γ ⊢ Aₙ ∶ ⟨ 𝒰 ℓ ⟩ → ⟨ Aₙ ∷ Γ .context ⟩ ctx
```
