
```agda
{-# OPTIONS --allow-unsolved-metas #-}
```

```agda
open import Type.Prelude
```

```agda
module Type.deprecated.Term.Layer-1.Kernel {# : Nat} (S : Vec (∃ Vec Nat) #) where
```

```agda
open import Type.deprecated.Term.Layer-2.DeBruijn
open import Type.Universe

module _ where

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

`_≾_` and `_≿_` view the context from the inside and outside, respectively

```agda
  -- `M ≾ N`: M ≤ N, includes expressions from N-1 down to M. e.g. 3 ≾ 7 = expression 6 ∷ (expression 5 ∷ (expression 4 ∷ (expression 3 ∷ []))); the most dependent expressions are exposed first
  infixl 5 _,_
  data _≾_ (M : Nat) : Nat → Set where
    ε : M ≾ M
    _,_ : ∀ {N} → M ≾ N → Expression N → M ≾ suc N

  -- `N ≿ M`: M ≤ N, includes expressions from M up to N-1. e.g. 7 ≿ 3 = expression 3 ∷ (expression 4 ∷ (expression 5 ∷ (expression 6 ∷ []))); the most independent expressions are exposed first
  infixr 5 _∷_
  data _≿_ (N : Nat) : Nat → Set where
    [] : N ≿ N
    _∷_ : ∀ {M} → Expression M → N ≿ suc M → N ≿ M
```

I may prepend `M ≾ n` (having length `n - M`) to the inner portion of `N ≿ M`, resulting in the slimy `(n - M + N) ≿ M`. It will require a `transport` to append something, say `Z ≿ (n + N - M)` to this.

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

  shift≾ : ∀ {M N} → M ≾ N → suc M ≾ suc N
  shift≾ ε       = ε
  shift≾ (Γ , δ) = shift≾ Γ , weakenExpressionFrom zero δ

  shift≿ : ∀ {M N} → N ≿ M → suc N ≿ suc M
  shift≿ []      = []
  shift≿ (ω ∷ Ξ) = weakenExpressionFrom zero ω ∷ shift≿ Ξ

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
```

```agda
  index≾ : ∀ {M N} → (Γ : M ≾ N) → Fin (finToNat (diff≾ Γ)) → Expression N
  index≾ ε ()
  index≾ (Γ , δ) zero = weakenExpressionFrom zero δ
  index≾ (Γ , δ) (suc x) = weakenExpressionFrom zero $ index≾ Γ x

  diff≾-eq : ∀ {M N} → (Γ : M ≾ N) → finToNat (diff≾ Γ) + M ≡ N
  diff≾-eq ε = auto
  diff≾-eq (Γ , x) = by (diff≾-eq Γ)
```

```agda
  {- Where `x` has free variables v₀ … v₂
     weakenExpressionBy≾From′ {3} {7} (ε , γ₃ , γ₄ , γ₅ , γ₆) 1
     maps an expression such that v₀ ---> v₀
                                  v₁ ---> v₅
                                  v₂ ---> v₆
     = map free vars (v₀ … v₆) in x to
  -}

  weakenExpressionBy≾From′ : ∀ {M N} → M ≾ N → Fin (suc M) → Expression M → Expression N
  weakenExpressionBy≾From′ ε _ x = x
  weakenExpressionBy≾From′ (Γ , ⋆) from x with context≤ Γ
  … | diff! N-M = weakenExpressionFrom (transport Fin auto $ weakenFinByFrom N-M zero from) (weakenExpressionBy≾From′ Γ from x)

  weakenExpressionBy≤From' : ∀ {M N} → M ≤ N → Fin (suc M) → Expression M → Expression N
  weakenExpressionBy≤From' (diff! 0) _ x = x
  weakenExpressionBy≤From' (diff! (suc k)) from x = weakenExpressionFrom (transport Fin auto $ weakenFinByFrom k zero from ) $ weakenExpressionBy≤From' auto from x

  weakenExpressionBy≾From′′ : ∀ {M N} → M ≾ N → Fin (suc M) → Expression M → Expression N
  weakenExpressionBy≾From′′ Δ = weakenExpressionBy≤From' (context≤ Δ)
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
  weakenExpressionBy≤From : ∀ {M N X}
                          → M ≤ X
                          → Fin (suc N)
                          → Expression N
                          → Expression (N + X - M)
  weakenExpressionBy≤From (diff! zero) x φ = transport Expression auto φ
  weakenExpressionBy≤From {M} {N} {X} (diff! (suc k)) x φ = transport Expression auto $ weakenExpressionBy≤From {M = M} (diff! k) (suc x) (weakenExpressionFrom x φ)

  weakenExpressionBy≾From : ∀ {M N X}
                          → M ≾ X
                          → Fin (suc N)
                          → Expression N
                          → Expression (N + X - M)
  weakenExpressionBy≾From M≾X = weakenExpressionBy≤From (context≤ M≾X)
```

`shift≾By` Γ Ξ shifts Ξ through Γ.

γᴹγ¹⁺ᴹ...(N-M ≾-elements)...γᴺ⁻¹
ξᴹξ¹⁺ᴹ...(n-M ≿-elements)...ξⁿ⁻¹
---------------------------------------------------------------------
                                χᴺχ¹⁺ᴺ...(n-M ≿-elements)...χⁿ⁻ᴹ⁺ᴺ⁻¹
so that
ξᴹ----------------------------->χᴺ
  ξ¹⁺ᴹ--------------------------->χ¹⁺ᴺ
                            ξⁿ⁻¹--------------------------->χⁿ⁻ᴹ⁺ᴺ⁻¹

```agda
  shift≾By : ∀ {M N n} → M ≾ N → n ≿ M → (n - M + N) ≿ N
  shift≾By {N = N} Γ [] = transport (_≿ N) auto []
  shift≾By {M} {N} Γ (ξ ∷ Ξ) with context≥ Ξ | context≿ Γ
  -- {!ξ shifted through Γ (N - M)!} ∷ {!shift≾By Γ!}
  shift≾By {M} {.M} Γ (ξ ∷ Ξ) | diff! n-M-1 | [] = ξ ∷ transport (_≿ suc M) auto (shift≾By ε Ξ)
  shift≾By {M} {N} {n} Γ (ξ ∷ Ξ) | diff! n-M-1 | γ ∷ Γ' = weakenExpression≾ Γ ξ ∷ (transport (_≿ suc N) auto $ shift≿ (shift≾By (context≾ Γ') Ξ))

  _<<>_ : ∀ {M N n} → M ≾ N → n ≿ M → M ≾ (n - M + N)
  Ξ <<> Δ = Ξ <>< shift≾By Ξ Δ

  _<>>_ : ∀ {M N n} → N ≿ M → M ≾ n → (n - M + N) ≿ M -- FIXME slime
  Ξ <>> ε = transport (_≿ _) auto Ξ
  _<>>_ {M} Ξ (Δ , δ) =
    transport (_≿ M)
      (case (context≤ Δ) of λ { (diff! k) → auto})
      ((Ξ <>> Δ) ,[ (case context≥ Ξ of λ { (diff! N-M) →
                     case context≤ Δ of λ { (diff! n-M) →
                     transport Expression auto $
                     weakenExpressionByFrom N-M (diff≾ Δ) δ } }) ])
```

```agda
  substitute≿ : ∀ {M N} (Δ : suc N ≿ suc M)
              → Expression M
              → N ≿ M
  substitute≿ [] x = []
  substitute≿ (δ ∷ Δ) x = instantiateExpressionAt zero δ x ∷ substitute≿ Δ (weakenExpressionFrom zero x)
```

```agda
  -- open import Type.deprecated.Term.Layer-1.Kernel.TypeChecked S public
```
