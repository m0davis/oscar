
```agda
{-# OPTIONS --allow-unsolved-metas #-}
```

```agda
open import Type.Prelude
```

```agda
module Type.Term.Layer+1.Expression {# : Nat} (S : Vec (∃ Vec Nat) #) where
```

```agda
open import Type.Prelude
open import Type.Universe
open import Type.Term.Layer+2.Variable
```

```agda
data Expression : Set
data Abstractions : ∀ {M} → Vec Nat M → Set

data Expression where
  𝓋 : Variable → Expression
  𝒰 : Universe → Expression
  𝓉 : (t : Fin #) → Abstractions (snd $ indexVec S t) → Expression
data Abstractions where
  [] : Abstractions []
  _∷_ : ∀ {v} → Expression
      → ∀ {M} {vs : Vec Nat M} → Abstractions vs
      → Abstractions (v ∷ vs)
```

```agda
_[_⋆←⋆_] : Expression → ∀ {N} → Vec Expression N → Vec Variable N → Expression
_[_⋆←⋆_]′ : ∀ {N} {M} {ms : Vec Nat M} → Abstractions ms → Vec Expression N → Vec Nat N → Abstractions ms

𝓋 x [ σs ⋆←⋆ vs ] with x ∈? vs
… | yes (n ,, _) = indexVec σs n
… | no _ = 𝓋 x
𝒰 ℓ [ _ ⋆←⋆ _ ] = 𝒰 ℓ
𝓉 t xs [ σs ⋆←⋆ vs ] = 𝓉 t (xs [ σs  ⋆←⋆ vs ]′)

[] [ _ ⋆←⋆ _ ]′ = []
(x ∷ xs) [ σs ⋆←⋆ vs ]′ = x [ σs ⋆←⋆ vs ] ∷ (xs [ σs ⋆←⋆ vs ]′)
```
