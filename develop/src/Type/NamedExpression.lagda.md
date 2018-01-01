
```agda
open import Type.Prelude
```

```agda
module Type.NamedExpression {# : Nat} (S : Vec (∃ Vec Nat) #) where
```

```agda
open import Type.Prelude
open import Type.Universe
open import Type.NamedVariable
```

```agda
data Expression : Set
data Abstractions : ∀ {M} → Vec Nat M → Set

record BoundExpression (N : Nat) : Set where
  inductive
  constructor [_↦_]
  field
    binders : Vec Variable N
    expression : Expression

data Expression where
  𝓋 : Variable → Expression
  𝒰 : Universe → Expression
  𝓉 : (t : Fin #) → Abstractions (snd $ indexVec S t) → Expression

data Abstractions where
  [] : Abstractions []
  _∷_ : ∀ {v} → BoundExpression v
      → ∀ {M} {vs : Vec Nat M} → Abstractions vs
      → Abstractions (v ∷ vs)
```

```agda
_[_↤E_] : Expression → ∀ {N} → Vec Expression N → Vec Variable N → Expression
_[_↤A_] : ∀ {N} {M} {ms : Vec Nat M} → Abstractions ms → Vec Expression N → Vec Nat N → Abstractions ms
_[_↤B_] : ∀ {B} {N} → BoundExpression B → Vec Expression N → Vec Nat N → BoundExpression B
avoidBinders : ∀ {B N} → Vec Variable B → Vec Expression N → Vec Nat N → ∃ λ N' → Vec Expression N' × Vec Nat N'
avoidBinders bs [] [] = _ ,, [] ,, []
avoidBinders bs (σ ∷ σs) (v ∷ vs) =
  let (_ ,, σs ,, vs) = avoidBinders bs σs vs in
  ifYes v ∈? bs
  then
    (_ ,, σs ,, vs)
  else
    (_ ,, σ ∷ σs ,, v ∷ vs)

𝓋 x [ σs ↤E vs ] with x ∈? vs
… | yes (n ,, _) = indexVec σs n
… | no _ = 𝓋 x
𝒰 ℓ [ _ ↤E _ ] = 𝒰 ℓ
𝓉 t xs [ σs ↤E vs ] = 𝓉 t (xs [ σs  ↤A vs ])

[] [ _ ↤A _ ] = []
(x ∷ xs) [ σs ↤A vs ] = x [ σs ↤B vs ] ∷ xs [ σs ↤A vs ]

[ bs ↦ x ] [ σs ↤B vs ] =
  let (_ ,, σs ,, vs) = avoidBinders bs σs vs in
  [ bs ↦ x [ σs ↤E vs ] ]

_[_↤₁E_] : Expression → Expression → Variable → Expression
x [ σ ↤₁E v ] = x [ σ ∷ [] ↤E v ∷ [] ]

_[_,_↤₂E_,_] : Expression → Expression → Expression → Variable → Variable → Expression
x [ σ₁ , σ₂ ↤₂E v₁ , v₂ ] = x [ σ₁ ∷ σ₂ ∷ [] ↤E v₁ ∷ v₂ ∷ [] ]

_[_,_,_↤₃E_,_,_] : Expression → Expression → Expression → Expression → Variable → Variable → Variable → Expression
x [ σ₁ , σ₂ , σ₃ ↤₃E v₁ , v₂ , v₃ ] = x [ σ₁ ∷ σ₂ ∷ σ₃ ∷ [] ↤E v₁ ∷ v₂ ∷ v₃ ∷ [] ]
```
