
```agda
{-# OPTIONS --allow-unsolved-metas #-}
```

```agda
module Type.Formula where
```

```agda
open import Type.Prelude
open import Type.Universe
open import Type.Variable
```

Some of the terminology here borrows from Dr. Gergő Érdi in [Universe of scope- and type-safe syntaxes](https://raw.githubusercontent.com/gergoerdi/universe-of-syntax/d7d5952cce76be551ff5869914b273be2d398069/README.md).

Formulas are syntactically-valid things.

```agda
record Abstraction (N : Nat) : Set

data Formula : Set where
  𝒰 : Universe → Formula
  𝓋 : Variable → Formula
  ΠF : Formula → Abstraction 1 → Formula
  ΠI : Formula → Abstraction 1 → Formula
  ΠE : Formula → Formula → Formula
  ΣF : Formula → Abstraction 1 → Formula
  ΣI : Formula → Formula → Formula
  ΣE : Abstraction 1 → Abstraction 2 → Formula → Formula
  +F : Formula → Formula → Formula
  +Iˡ : Formula → Formula
  +Iʳ : Formula → Formula
  +E : Abstraction 1 → Abstraction 1 → Abstraction 1 → Formula → Formula
  𝟘F : Formula
  𝟘E : Abstraction 1 → Formula → Formula
  𝟙F : Formula
  𝟙I : Formula
  𝟙E : Abstraction 1 → Formula → Formula → Formula
  ℕF : Formula
  ℕIᶻ : Formula
  ℕIˢ : Formula → Formula
  ℕE : Abstraction 1 → Formula → Abstraction 2 → Formula → Formula
  =F : Formula → Formula → Formula → Formula
  =I : Formula → Formula
  =E : Abstraction 3 → Abstraction 1 → Formula → Formula → Formula → Formula
```

```agda
record Abstraction (N : Nat) where
  constructor _⋆↦_
  inductive
  field
    binders : Vec Variable N
    formula : Formula

infix 10 _↦₁_ _,_↦₂_ _,_,_↦₃_
pattern _↦₁_ x A = (x ∷ []) ⋆↦ A
pattern _,_↦₂_ x y A = (x ∷ y ∷ []) ⋆↦ A
pattern _,_,_↦₃_ x y z A = (x ∷ y ∷ z ∷ []) ⋆↦ A
```

-- simultaneous substitution

```agda
_[_⋆←⋆_] : Formula → ∀ {N} → Vec Formula N → Vec Variable N → Formula
𝒰 ℓ [ _ ⋆←⋆ _ ] = 𝒰 ℓ
𝓋 x [ σs ⋆←⋆ vs ] = {!!}
ΠF A (x ↦₁ B) [ σs ⋆←⋆ vs ] = ΠF (A [ σs ⋆←⋆ vs ]) {!!}
_[_⋆←⋆_] = {!!}

_[_←₁_] : Formula → Formula → Variable → Formula
φ [ σ ←₁ x ] = φ [ σ ∷ [] ⋆←⋆ x ∷ [] ]

_[_,_←₂_,_] : Formula → Formula → Formula → Variable → Variable → Formula
φ [ σx , σy ←₂ x , y ] = φ [ σx ∷ σy ∷ [] ⋆←⋆ x ∷ y ∷ [] ]

_[_,_,_←₃_,_,_] : Formula → Formula → Formula → Formula → Variable → Variable → Variable → Formula
φ [ σx , σy , σz ←₃ x , y , z ] = φ [ σx ∷ σy ∷ σz ∷ [] ⋆←⋆ x ∷ y ∷ z ∷ [] ]
```
