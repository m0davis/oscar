
```agda
{-# OPTIONS --allow-unsolved-metas #-}
```

```agda
open import Type.Prelude
```

```agda
module Type.DeBruijnExpression {# : Set} (S : # → ∃ Vec Nat) where
```

```agda
open import Type.DeBruijnVariable
open import Type.Universe

data Expression (N : Nat) : Set
data Abstractions (N : Nat) : ∀ {M} → Vec Nat M → Set

data Expression (N : Nat) where
  𝓋 : Fin N → Expression N
  𝒰 : Universe → Expression N
  𝓉 : (t : #) → Abstractions N (snd $ S t) → Expression N
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
subId₁ : ∀ {N} {m : Fin N} {k : Fin (suc N)} {A : Expression N} → instantiateExpressionAt (weakenFinFrom k m) (weakenExpressionFrom k A) (𝓋 m) ≡ A
subId₁ = {!!}
```
