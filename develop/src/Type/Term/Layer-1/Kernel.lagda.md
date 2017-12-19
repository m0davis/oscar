
```agda
{-# OPTIONS --allow-unsolved-metas #-}
```

```agda
module Type.Term.Layer-1.Kernel where
```

```agda
open import Type.Prelude
```

```agda
open import Type.Term.Layer-2.DeBruijn

Universe = Nat

module Meta {# : Nat} (S : Vec (∃ Vec Nat) #) where

  data Expression (N : Nat) : Set
  data Abstractions (N : Nat) : ∀ {M} → Vec Nat M → Set

  data Expression (N : Nat) where
    𝓋 : Fin N → Expression N
    𝒰 : Universe → Expression N
    𝓉 : (t : Fin #) → Abstractions N (snd $ indexVec S t) → Expression N
  data Abstractions (N : Nat) where
    [] : Abstractions N []
    _∷_ : ∀ {v} → Expression (v + N)
        → ∀ {M} {vs : Vec Nat M} → Abstractions N vs
        → Abstractions N (v ∷ vs)
```

```agda
  weakenExpressionFrom : ∀ {N} → Fin (suc N) → Expression N → Expression (suc N)
  weakenAbstractionsFrom : ∀ {N} → Fin (suc N) → ∀ {M} {xs : Vec Nat M} → Abstractions N xs → Abstractions (suc N) xs

  weakenExpressionFrom from (𝒰 ℓ) = 𝒰 ℓ
  weakenExpressionFrom from (𝓋 v) = 𝓋 (weakenFinFrom from v)
  weakenExpressionFrom from (𝓉 t xs) = 𝓉 t (weakenAbstractionsFrom from xs)
  weakenAbstractionsFrom from [] = []
  weakenAbstractionsFrom {N} from (_∷_ {v} x xs) =
    let from' : Fin (suc (v + N))
        from' = transport Fin auto $ weakenFinByFrom v zero from
        x' : Expression (v + suc N)
        x' = transport Expression auto $ weakenExpressionFrom from' x
    in
    x' ∷ weakenAbstractionsFrom from xs
```

```agda
  weakenExpressionByFrom : ∀ by → ∀ {N} → Fin (suc N) → Expression N → Expression (by + N)
  weakenExpressionByFrom 0 from x = x
  weakenExpressionByFrom (suc by) from x =
    let x₋₁ = weakenExpressionFrom from x
        from₋₁ = weakenFinFrom zero from
    in
    transport Expression auto $ weakenExpressionByFrom by from₋₁ x₋₁
```

```agda
  instantiateExpressionAt : ∀ {N} → Fin (suc N) → Expression (suc N) → Expression N → Expression N
  instantiateAbstractionsAt : ∀ {N} → Fin (suc N) → ∀ {M} {vs : Vec Nat M} → Abstractions (suc N) vs → Expression N → Abstractions N vs

  instantiateExpressionAt at (𝒰 ℓ) x = 𝒰 ℓ
  instantiateExpressionAt at (𝓋 v) x with at == v
  … | yes _ = x
  … | no at≢v = 𝓋 (instantiateFinAt at≢v)
  instantiateExpressionAt at (𝓉 t ys) x = 𝓉 t (instantiateAbstractionsAt at ys x)
  instantiateAbstractionsAt at {0} [] x = []
  instantiateAbstractionsAt {N} at {suc M} (_∷_ {v} y/v ys) x
    rewrite (auto ofType v + suc N ≡ suc (v + N)) =
    let at/v : Fin (suc (v + N))
        at/v = transport Fin auto $ weakenFinByFrom        v zero at
        x/v  =                      weakenExpressionByFrom v zero x -- TODO use `at` instead of `zero` here?
    in
    instantiateExpressionAt at/v y/v x/v ∷ instantiateAbstractionsAt at ys x
```

```agda
  -- DContext and UContext view the context from the inside and outside, respectively

  -- `DContext M N`: M ≤ N, includes expressions from N-1 down to M. e.g. DContext 3 7 = expression 6 ∷ (expression 5 ∷ (expression 4 ∷ (expression 3 ∷ []))); the most dependent expressions are exposed first
  infixl 5 _,_
  data _≾_ (M : Nat) : Nat → Set where
    ε : M ≾ M
    _,_ : ∀ {N} → M ≾ N → Expression N → M ≾ suc N

  -- `UContext N M`: M ≤ N, includes expressions from M up to N-1. e.g. UContext 7 3 = expression 3 ∷ (expression 4 ∷ (expression 5 ∷ (expression 6 ∷ []))); the most independent expressions are exposed first
  infixr 5 _∷_
  data _≿_ (N : Nat) : Nat → Set where
    [] : N ≿ N
    _∷_ : ∀ {M} → Expression M → N ≿ suc M → N ≿ M
```

I may prepend `M ≾ n` (having length `n - M`) to the inner portion of `N ≿ M`, resulting in the slimy `(n - M + N) ≿ M`. It will be a problem to prepend yet another `M ≾ n'` to

If instead I represented `M ≾ n` as something that starts at `M` and goes for a length of `n - M`, e.g. `M ⟨+ (n - M)`, then I may prepend `M ⟨+ n-M` to the inner portion of N ≿ M, resulting in `(n-M + N) ≿ M`, which is still slimy but less so.

It does not eliminate the slime entirely simply to add indices for length and endpoint positions. For example, I could use a representation that indexes on the length and both endpoints. Then I may prepend `M ≾[ n ]+ n-M` to `N ≿[ M ]+ N-M`, resulting in the slimeful `(n-M + N) ≿[ M ]+ (n-M + N-M)`.

I can eliminate the slime entirely via encapsulation: use a resultant type that only tells us that its outermost endpoint is at `M`: `⟫ M`. I trade precision in the type to gain some convenience in combinatorics. I can append the result to a outer shell, `L ≾ M`, obtaining `L ⟪`. The gain is limited, however, in that, having lost type-level information about its length or innermost endpoint, I cannot, for example, use a resultant `0 ⟪` as the context in a scope-checked typing judgement, `(Γ : 0 ≾ N) (a : Expression N) (A : Expression N)`, for the contextual size, `N` would first need to be computed from `0 ⟪`.

```agda
  {- I try to use a consistent representation:

    outsides , inside
    outsides ,[ inside ]
    outside ∷ insides
    [ outside ]∷ insides

    Γ or Δ , δ
    Ω or Ξ ,[ δ ]
    ω ∷ Ω or Ξ
    [ ω ]∷ Γ

    outsides - Δ (D) or Ξ (U)
    outside  - ξ
    inside   - δ
    insides  - Ξ (U) or Δ (D)

    mainly, Δ belongs on the lhs of _,_ and Ξ belongs on the rhs of _∷_

    from outsidest to insidest

                    []   ε
         ω   Ω    Ξ    ⋆   Γ    Δ    δ
           ∷                        ,
               ⋆∷             ,⋆

    appending contexts

    Ω ⋆∷ Ξ  ------>  ⋆Ξ
    Γ ,⋆ Δ  ------>  Γ⋆
  -}

  -- putting something inside a thing that exposes its outside first
  _,[_] : ∀ {M N} → N ≿ M → Expression N → suc N ≿ M
  []      ,[ ⋆ ] = ⋆ ∷ []
  (ω ∷ Ξ) ,[ ⋆ ] = ω ∷ Ξ ,[ ⋆ ]

  -- putting something outside a thing that exposes its inside first
  [_]∷_ : ∀ {M N} → Expression M → suc M ≾ N → M ≾ N
  [ ⋆ ]∷ ε       = ε , ⋆
  [ ⋆ ]∷ (Γ , δ) = [ ⋆ ]∷ Γ , δ

  context≿ : ∀ {M N} → M ≾ N → N ≿ M
  context≿ ε       = []
  context≿ (Γ , δ) = context≿ Γ ,[ δ ]

  context≾ : ∀ {M N} → N ≿ M → M ≾ N
  context≾ [] = ε
  context≾ (ω ∷ Ξ) = [ ω ]∷ context≾ Ξ

  context≤ : ∀ {M N} → M ≾ N → M ≤ N
  context≤ ε       = auto
  context≤ (Δ , _) = by (context≤ Δ)

  context≥ : ∀ {M N} → N ≿ M → N ≥ M
  context≥ []      = auto
  context≥ (_ ∷ Ξ) = by (context≥ Ξ)

  diff≾ : ∀ {M N} → M ≾ N → Fin (suc N)
  diff≾ ε       = zero
  diff≾ (Γ , _) = suc (diff≾ Γ)

  diff≿ : ∀ {M N} → N ≿ M → Fin (suc N)
  diff≿ Ξ = diff≾ (context≾ Ξ)

  infixr 7 _<<<_ _<><_ _<>>_

  _<<<_ : ∀ {M N O} → M ≾ N → N ≾ O → M ≾ O
  Γ <<< ε       = Γ
  Γ <<< (Δ , δ) = Γ <<< Δ , δ

  _<><_ : ∀ {M N O} → M ≾ N → O ≿ N → M ≾ O
  Γ <>< []      = Γ
  Γ <>< (⋆ ∷ Ξ) = (Γ , ⋆) <>< Ξ

  _>>>_ : ∀ {M N O} → N ≿ M → O ≿ N → O ≿ M
  [] >>> Ξ      = Ξ
  (ω ∷ Ω) >>> Ξ = ω ∷ Ω >>> Ξ

  _<>>_ : ∀ {M N n} → N ≿ M → M ≾ n → (n - M + N) ≿ M -- FIXME slime
  Ξ <>> ε = transport (_≿ _) auto Ξ
  _<>>_ {M} Ξ (Δ , δ) =
    transport (_≿ M)
      (case (context≤ Δ) of λ { (diff! k) → auto})
      ((Ξ <>> Δ) ,[ (case context≥ Ξ of λ { (diff! N-M) →
                     case context≤ Δ of λ { (diff! n-M) →
                     transport Expression auto $
                     weakenExpressionByFrom N-M (diff≾ Δ) δ } }) ])

  shift≾ : ∀ {M N} → M ≾ N → suc M ≾ suc N
  shift≾ ε       = ε
  shift≾ (Γ , δ) = shift≾ Γ , weakenExpressionFrom zero δ

  shift≿ : ∀ {M N} → N ≿ M → suc N ≿ suc M
  shift≿ []      = []
  shift≿ (ω ∷ Ξ) = weakenExpressionFrom zero ω ∷ shift≿ Ξ

  -- shift≾By :

  index≾ : ∀ {M N} → (Γ : M ≾ N) → Fin (finToNat (diff≾ Γ)) → Expression N
  index≾ ε ()
  index≾ (Γ , δ) zero = weakenExpressionFrom zero δ
  index≾ (Γ , δ) (suc x) = weakenExpressionFrom zero $ index≾ Γ x

  diff≾-eq : ∀ {M N} → (Γ : M ≾ N) → finToNat (diff≾ Γ) + M ≡ N
  diff≾-eq ε = auto
  diff≾-eq (Γ , x) = by (diff≾-eq Γ)
```

```agda
  weakenExpression≾ : ∀ {M N} → M ≾ N → Expression M → Expression N
  weakenExpression≾ ε x       = x
  weakenExpression≾ (Γ , _) x = weakenExpressionFrom zero (weakenExpression≾ Γ x)

  weakenExpression≿ : ∀ {M N} → N ≿ M → Expression M → Expression N
  weakenExpression≿ [] x = x
  weakenExpression≿ (_ ∷ Ξ) x = weakenExpression≿ Ξ (weakenExpressionFrom zero x)
```

```agda
  module Typechecked
    (_⊢_∶_ : ∀ {N} → 0 ≾ N → Expression N → Expression N → Set)
    (let _⊢_∶_ = _⊢_∶_ ; infix 5 _⊢_∶_)
    where
    tcInstantiateAt
      : ∀ {M} {Γ : 0 ≾ M}
      → ∀ {N} {Δ : M ≾ N}
      → ∀ {a A b B}
      → (Γ , A) <<< shift≾ Δ ⊢ b ∶ B
      → Γ <<< Δ ⊢ a ∶ weakenExpression≾ Δ A
      → Expression N
    tcInstantiateAt {Δ = Δ} {a} {b = b} _ _ = instantiateExpressionAt (diff≾ Δ) b a
{-
    tcWeakenFrom
      : ∀ {M} {Γ : 0 ≾ M}
      → ∀ {N} {Δ : M ≾ N}
      →
    tcWeakenFrom = ?
-}
```

```agda
private

  module Test where

    pattern ,_ s = _ ,, s

    myMeta : Vec (∃ Vec Nat) _
    myMeta =
      -- Π
      , (0 ∷ 1 ∷ []) ∷
      , (0 ∷ 1 ∷ []) ∷
      , (0 ∷ 0 ∷ []) ∷
      -- Σ
      , (0 ∷ 1 ∷ []) ∷
      , (0 ∷ 0 ∷ []) ∷
      , (1 ∷ 2 ∷ 0 ∷ []) ∷
      -- +
      []

    module _ where
      open Meta myMeta

      testExpression₁ : Expression 0
      testExpression₁ = 𝓉 0 (𝒰 0 ∷ 𝓋 0 ∷ [])

    module _ where
      open Meta

      -- pattern z = zero

      pattern ΠF x = 𝓉 zero x
      pattern ΠI x = 𝓉 (suc zero) x
      pattern ΠE f x = 𝓉 (suc (suc zero)) (f ∷ x ∷ [])
      pattern ΣF A B = 𝓉 3 (A ∷ B ∷ []) -- there's a problem with Agda assuming this 3 is a Nat (and not possibly a Fin)

      testExpression₁' : Expression myMeta 0
      testExpression₁' = ΠF (𝒰 0 ∷ 𝓋 0 ∷ [])

      testExpression₂ : Expression myMeta 0
      testExpression₂ = ΠI (𝒰 0 ∷ 𝓋 0 ∷ [])

      test₃ : Expression myMeta 2
      test₃ = ΠE (𝓋 0) (𝒰 17)

      test-fail-pattern : Expression myMeta 1
      test-fail-pattern = {!ΣF!}

      test-for-weakening : Expression myMeta 2
      test-for-weakening = ΠI ((𝓋 0) ∷ ((ΠE (𝓋 0) (𝓋 2)) ∷ []))

      test-weakening-0 : Expression myMeta 3
      test-weakening-0 = weakenExpressionFrom myMeta 0 test-for-weakening
```

```agda
```
