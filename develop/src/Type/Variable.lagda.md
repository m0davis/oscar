
```agda
module Type.Variable where
```

```agda
open import Type.Prelude
```

```agda
Variable = Nat
```

In the overloaded combinator `_∉_` I express

```agda
record Distinctness (D : Set) : Set₁ where
  field
    _∉_ : Variable → D → Set
open Distinctness ⦃ … ⦄ public
```

```agda
data DistinctFromVariables {N} (x : Variable) (xs : Vec Variable N) : Set where
  ⟨_⟩ : ((p : Fin N) → indexVec xs p ≢ x) → DistinctFromVariables x xs

instance

  DistinctnessVariables : ∀ {N} → Distinctness (Vec Variable N)
  DistinctnessVariables .Distinctness._∉_ = DistinctFromVariables
```
