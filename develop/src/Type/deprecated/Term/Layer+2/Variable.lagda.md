
```agda
module Type.deprecated.Term.Layer+2.Variable where
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

  _∈_ : Variable → D → Set
  _∈_ v d = ¬ v ∉ d
open Distinctness ⦃ … ⦄ public
```

```agda
data DistinctFromVariables {N} (x : Variable) (xs : Vec Variable N) : Set where
  ⟨_⟩ : ((p : Fin N) → indexVec xs p ≢ x) → DistinctFromVariables x xs

instance

  DistinctnessVariables : ∀ {N} → Distinctness (Vec Variable N)
  DistinctnessVariables .Distinctness._∉_ = DistinctFromVariables
```

```agda
_∈?_ : (x : Variable) → ∀ {N} → (vs : Vec Variable N) → Dec (∃ λ n → indexVec vs n ≡ x)
x ∈? [] = no λ {(() ,, _)}
x ∈? (v ∷ vs) with v == x
… | yes v≡x = yes (zero ,, v≡x)
… | no v≢x with x ∈? vs
… | yes (n ,, iv=x) = yes (suc n ,, iv=x)
… | no x∉vs = no λ { (zero ,, v≡x) → v≢x v≡x ; (suc n ,, x∈vs) → x∉vs (n ,, x∈vs)}
```
