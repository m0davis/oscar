
```agda
{-# OPTIONS --allow-unsolved-metas #-}
```

```agda
open import Type.Prelude
```

```agda
module Type.deprecated.Term.Layer-1.Kernel.TypeChecked {# : Nat} (S : Vec (∃ Vec Nat) #) where
```

```agda
private
  -- for some reason, the auto tactic did not work in the module below
  auto′ : ∀ {a b c : Nat}
            → a + b + (c + b) - b ≡ a + b - b + (c + b)
  auto′ {a} {b} {c} = auto
```

```agda
module _ where
  open import Type.deprecated.Term.Layer-1.Kernel S
  module Typechecked
    (_ctx : ∀ {N} → 0 ≾ N → Set)
    (let _ctx = _ctx ; infix 3 _ctx)
    (_⊢_∶_ : ∀ {N} → 0 ≾ N → Expression N → Expression N → Set)
    (let _⊢_∶_ = _⊢_∶_ ; infix 4 _⊢_∶_)
    where
    tcInstantiateAt
      : ∀ {M} {Γ : 0 ≾ M}
      → ∀ {N} {Δ : M ≾ N}
      → ∀ {a A b B}
      → (Γ , A) <<< shift≾ Δ ⊢ b ∶ B
      → Γ <<< Δ ⊢ a ∶ weakenExpression≾ Δ A
      → Expression N
    tcInstantiateAt {Δ = Δ} {a} {b = b} _ _ = instantiateExpressionAt (diff≾ Δ) b a
    tcInstantiateAt'
      : ∀ {M} {Γ : 0 ≾ M}
      → ∀ {N} {Δ : N ≿ M}
      → ∀ {a A b B}
      → (Γ , A) <>< shift≿ Δ ⊢ b ∶ B
      → Γ <>< Δ ⊢ a ∶ weakenExpression≿ Δ A
      → Expression N
    tcInstantiateAt' {Δ = Δ} {a} {b = b} _ _ = instantiateExpressionAt (diff≿ Δ) b a
```

Why can't Agda figure-out that Δ is empty?

```agda
    module Test/tcInstantiateAt where
      postulate
        N : Nat
        Γ : 0 ≾ N
        A a : Expression N
        B b : Expression (suc N)
        Γ,A⊢b∶B : Γ , A ⊢ b ∶ B
        Γ⊢a∶A : Γ ⊢ a ∶ A
        b[a] : Expression N
        b'≡b[a]  : tcInstantiateAt  {Δ = ε } Γ,A⊢b∶B Γ⊢a∶A ≡ b[a]
        b'≡b[a]' : tcInstantiateAt' {Δ = []} Γ,A⊢b∶B Γ⊢a∶A ≡ b[a]
```

```agda
    record Syntactic : Set where
      field
        wfctx₁ : ∀ {N} {Γ : 0 ≾ N} {a A}
               → Γ ⊢ a ∶ A
               → Γ ctx
        well-typed₁ : ∀ {N} {Γ : 0 ≾ N}
                    → ∀ {a A}
                    → Γ ⊢ a ∶ A
                    → ∃ λ ℓ → Γ ⊢ A ∶ 𝒰 ℓ
        weaken
          : ∀ {M} {Γ : 0 ≾ M}
          → ∀ {N} {Δ : N ≿ M}
          → ∀ {X}
          → ∀ {a A}
          → Γ , X ctx
          → Γ <>< Δ ⊢ a ∶ A
          → (Γ , X) <>< shift≿ Δ ⊢ weakenExpressionFrom (diff≿ Δ) a ∶ weakenExpressionFrom (diff≿ Δ) A

      weaken⊢By : ∀ {M N} {Γ : 0 ≾ M}
                → (Δ : N ≿ M)
                → ∀ {a A}
                → Γ ⊢ a ∶ A
                → Γ <>< Δ ⊢ weakenExpression≿ Δ a ∶ weakenExpression≿ Δ A
      weaken⊢By = λ { [] x → x
                    ; (δ ∷ Δ) x → {!!}
                    }

      weaken⊢ByFrom : ∀ {M N X} {Γ : 0 ≾ M} {Δ : N ≿ M} {Ξ : M ≾ X}
                    → ∀ {a A}
                    → Γ <>< Δ ⊢ a ∶ A
                    → Γ <<< Ξ ctx
                    → Γ <<< (Ξ <<> Δ) ⊢ (transport Expression ((case context≤ Ξ of λ {(diff! X-M) → case context≥ Δ of λ {(diff! N-M) → auto′ {N-M} {M} {X-M}}})) (weakenExpressionBy≾From Ξ (diff≿ Δ) a))
                                      ∶ (transport Expression ((case context≤ Ξ of λ {(diff! X-M) → case context≥ Δ of λ {(diff! N-M) → auto′ {N-M} {M} {X-M}}})) (weakenExpressionBy≾From Ξ (diff≿ Δ) A))
      weaken⊢ByFrom = {!!}

      field
        substitute
          : ∀ {M} {Γ : 0 ≾ M}
          → ∀ {N} {Δ : N ≿ M}
          → ∀ {a A b B}
          → (ΓAΔ⊢b∶B : (Γ , A) <>< shift≿ Δ ⊢ b ∶ B)
          → (Γ⊢a∶A : Γ ⊢ a ∶ A)
          → (let ΓΔ⊢a∶A = weaken⊢By Δ Γ⊢a∶A
                 ΓAΔ⊢B∶𝒰 = well-typed₁ ΓAΔ⊢b∶B .snd
                 b[a] = tcInstantiateAt {Γ = Γ} {Δ = {!context≾ Δ!}} {A = A}  {!ΓAΔ⊢b∶B!} {!ΓΔ⊢a∶A!}
                 B[a] = tcInstantiateAt ΓAΔ⊢b∶B ΓΔ⊢a∶A
            )
          → Γ <>< substitute≿ (shift≿ Δ) a ⊢ instantiateExpressionAt (diff≿ Δ) b (weakenExpression≿ Δ a) ∶ instantiateExpressionAt (diff≿ Δ) B (weakenExpression≿ Δ a)
```
