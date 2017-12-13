
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

Definitions for formulas.

```agda
module DefinedFunctions where
  𝟎 𝟏 𝟐 𝟑 𝟒 : Formula
  𝟎 = ℕIᶻ
  𝟏 = ℕIˢ 𝟎
  𝟐 = ℕIˢ 𝟏
  𝟑 = ℕIˢ 𝟐
  𝟒 = ℕIˢ 𝟑

  -- add x represents a function that adds x to a given input
  add : Formula → Formula
  add = ℕE (zero ↦₁ ΠF ℕF (zero ↦₁ ℕF)) -- form a function f : ℕ → ℕ
           -- case x = ℕIZ
           -- λ y → y
           (ΠI ℕF (zero ↦₁ 𝓋 zero))
           -- case x = ℕIS x₋₁
           -- λ x₋₁ f →
              -- λ y → suc (f y)
           (0 , 1 ↦₂ ΠI ℕF (2 ↦₁ ℕIˢ (ΠE (𝓋 1) (𝓋 2))))

  _+ℕ_ : Formula → Formula → Formula
  x +ℕ y = ΠE (add x) y

  double : Formula → Formula
  double = ℕE (0 ↦₁ ℕF) ℕIᶻ (0 , 1 ↦₂ ℕIˢ (ℕIˢ (𝓋 1)))

  multiply : Formula → Formula
  multiply = ℕE (zero ↦₁ ΠF ℕF (zero ↦₁ ℕF))
                (ΠI ℕF (zero ↦₁ ℕIᶻ))
                (let x₋₁ = 0 ; f = 1 ; y = 2 in
                  x₋₁ , f ↦₂ ΠI ℕF (y ↦₁ 𝓋 y +ℕ (ΠE (𝓋 f) (𝓋 x₋₁))))

  _*ℕ_ : Formula → Formula → Formula
  x *ℕ y = ΠE (multiply x) y

  infix 14 _=ℕ_
  _=ℕ_ : Formula → Formula → Formula
  x =ℕ y = =F ℕF x y
```

-- simultaneous substitution

```agda
_∈?_ : (x : Variable) → ∀ {N} → (vs : Vec Variable N) → Dec (∃ λ n → indexVec vs n ≡ x)
x ∈? [] = no λ {(() ,, _)}
x ∈? (v ∷ vs) with v == x
… | yes v≡x = yes (zero ,, v≡x)
… | no v≢x with x ∈? vs
… | yes (n ,, iv=x) = yes (suc n ,, iv=x)
… | no x∉vs = no λ { (zero ,, v≡x) → v≢x v≡x ; (suc n ,, x∈vs) → x∉vs (n ,, x∈vs)}

_[_⋆←⋆_] : Formula → ∀ {N} → Vec Formula N → Vec Variable N → Formula

_[_←_-_] : Formula → ∀ {N} → Vec Formula N → Vec Variable N → ∀ {M} → Vec Variable M → Formula

_[_←_-₁_] : Formula → ∀ {N} → Vec Formula N → Vec Variable N → Variable → Abstraction 1
x [ σs ← vs -₁ e ] = e ↦₁ x [ σs ← vs - e ∷ [] ]

_[_←_-₂_,_] : Formula → ∀ {N} → Vec Formula N → Vec Variable N → Variable → Variable → Abstraction 2
x [ σs ← vs -₂ e₁ , e₂ ] = e₁ , e₂ ↦₂ x [ σs ← vs - e₁ ∷ e₂ ∷ [] ]

_[_←_-₃_,_,_] : Formula → ∀ {N} → Vec Formula N → Vec Variable N → Variable → Variable → Variable → Abstraction 3
x [ σs ← vs -₃ e₁ , e₂ , e₃ ] = e₁ , e₂ , e₃ ↦₃ x [ σs ← vs - e₁ ∷ e₂ ∷ e₃ ∷ [] ]

x [ σs ← vs - [] ] = x [ σs ⋆←⋆ vs ]
x [ σs ← vs - ex ∷ exs ] = x [ 𝓋 ex ∷ σs ← ex ∷ vs - exs ]

𝒰 ℓ [ _ ⋆←⋆ _ ] = 𝒰 ℓ
𝓋 x [ σs ⋆←⋆ vs ] with x ∈? vs
… | yes (n ,, x∈vs) = indexVec σs n
… | no x∉vs = 𝓋 x
ΠF A (x ↦₁ B) [ σs ⋆←⋆ vs ] = ΠF (A [ σs ⋆←⋆ vs ]) (B [ σs ← vs -₁ x ])
ΠI A (x ↦₁ B) [ σs ⋆←⋆ vs ] = ΠI (A [ σs ⋆←⋆ vs ]) (B [ σs ← vs -₁ x ])
ΠE f x [ σs ⋆←⋆ vs ] = ΠE (f [ σs ⋆←⋆ vs ]) (x [ σs ⋆←⋆ vs ])
ΣF A (x ↦₁ B) [ σs ⋆←⋆ vs ] = ΣF (A [ σs ⋆←⋆ vs ]) (B [ σs ← vs -₁ x ])
ΣI a b [ σs ⋆←⋆ vs ] = ΣI (a [ σs ⋆←⋆ vs ]) (b [ σs ⋆←⋆ vs ])
ΣE (z ↦₁ C) (x , y ↦₂ g) p [ σs ⋆←⋆ vs ] = ΣE (C [ σs ← vs -₁ z ]) (g [ σs ← vs -₂ x , y ]) (p [ σs ⋆←⋆ vs ])
+F A B [ σs ⋆←⋆ vs ] = +F (A [ σs ⋆←⋆ vs ]) (B [ σs ⋆←⋆ vs ])
+Iˡ a [ σs ⋆←⋆ vs ] = +Iˡ (a [ σs ⋆←⋆ vs ])
+Iʳ b [ σs ⋆←⋆ vs ] = +Iʳ (b [ σs ⋆←⋆ vs ])
+E (z ↦₁ C) (x ↦₁ m) (y ↦₁ n) e [ σs ⋆←⋆ vs ] = +E (C [ σs ← vs -₁ z ]) (m [ σs ← vs -₁ x ]) (n [ σs ← vs -₁ y ]) (e [ σs ⋆←⋆ vs ])
𝟘F [ σs ⋆←⋆ vs ] = 𝟘F
𝟘E (z ↦₁ C) e [ σs ⋆←⋆ vs ] = 𝟘E (C [ σs ← vs -₁ z ]) (e [ σs ⋆←⋆ vs ])
𝟙F [ σs ⋆←⋆ vs ] = 𝟙F
𝟙I [ σs ⋆←⋆ vs ] = 𝟙I
𝟙E (z ↦₁ C) c e [ σs ⋆←⋆ vs ] = 𝟙E (C [ σs ← vs -₁ z ]) (c [ σs ⋆←⋆ vs ]) (e [ σs ⋆←⋆ vs ])
ℕF [ σs ⋆←⋆ vs ] = ℕF
ℕIᶻ [ σs ⋆←⋆ vs ] = ℕIᶻ
ℕIˢ n [ σs ⋆←⋆ vs ] = ℕIˢ (n [ σs ⋆←⋆ vs ])
ℕE (z ↦₁ C) cᶻ (z' , f ↦₂ cˢ) n [ σs ⋆←⋆ vs ] = ℕE (C [ σs ← vs -₁ z ]) (cᶻ [ σs ⋆←⋆ vs ]) (cˢ [ σs ← vs -₂ z' , f ]) (n [ σs ⋆←⋆ vs ])
=F A a b [ σs ⋆←⋆ vs ] = =F (A [ σs ⋆←⋆ vs ]) (a [ σs ⋆←⋆ vs ]) (b [ σs ⋆←⋆ vs ])
=I a [ σs ⋆←⋆ vs ] = =I (a [ σs ⋆←⋆ vs ])
=E (x , y , p ↦₃ C) (z ↦₁ c) a b p' [ σs ⋆←⋆ vs ] = =E (C [ σs ← vs -₃ x , y , p ]) (c [ σs ← vs -₁ z ]) (a [ σs ⋆←⋆ vs ]) (b [ σs ⋆←⋆ vs ]) (p' [ σs ⋆←⋆ vs ])

_[_←₁_] : Formula → Formula → Variable → Formula
φ [ σ ←₁ x ] = φ [ σ ∷ [] ⋆←⋆ x ∷ [] ]

_[_,_←₂_,_] : Formula → Formula → Formula → Variable → Variable → Formula
φ [ σx , σy ←₂ x , y ] = φ [ σx ∷ σy ∷ [] ⋆←⋆ x ∷ y ∷ [] ]

_[_,_,_←₃_,_,_] : Formula → Formula → Formula → Formula → Variable → Variable → Variable → Formula
φ [ σx , σy , σz ←₃ x , y , z ] = φ [ σx ∷ σy ∷ σz ∷ [] ⋆←⋆ x ∷ y ∷ z ∷ [] ]
```

Checking that a variable is not free in a formula.

```agda
instance

  DistinctnessFormula : Distinctness Formula
  DistinctnessAbstraction : ∀ {N} → Distinctness (Abstraction N)

  DistinctnessFormula .Distinctness._∉_ v (𝒰 x) = ⊤
  DistinctnessFormula .Distinctness._∉_ v (𝓋 x) = v ≢ x
  DistinctnessFormula .Distinctness._∉_ v (ΠF φ₁ φ₂) = v ∉ φ₁ × v ∉ φ₂
  DistinctnessFormula .Distinctness._∉_ v (ΠI φ₁ φ₂) = v ∉ φ₁ × v ∉ φ₂
  DistinctnessFormula .Distinctness._∉_ v (ΠE φ₁ φ₂) = v ∉ φ₁ × v ∉ φ₂
  DistinctnessFormula .Distinctness._∉_ v (ΣF φ₁ φ₂) = v ∉ φ₁ × v ∉ φ₂
  DistinctnessFormula .Distinctness._∉_ v (ΣI φ₁ φ₂) = v ∉ φ₁ × v ∉ φ₂
  DistinctnessFormula .Distinctness._∉_ v (ΣE φ₁ φ₂ φ₃) = v ∉ φ₁ × v ∉ φ₂ × v ∉ φ₃
  DistinctnessFormula .Distinctness._∉_ v (+F φ₁ φ₂) = v ∉ φ₁ × v ∉ φ₂
  DistinctnessFormula .Distinctness._∉_ v (+Iˡ φ₁) = v ∉ φ₁
  DistinctnessFormula .Distinctness._∉_ v (+Iʳ φ₁) = v ∉ φ₁
  DistinctnessFormula .Distinctness._∉_ v (+E φ₁ φ₂ φ₃ φ₄) = v ∉ φ₁ × v ∉ φ₂ × v ∉ φ₃ × v ∉ φ₄
  DistinctnessFormula .Distinctness._∉_ v 𝟘F = ⊤
  DistinctnessFormula .Distinctness._∉_ v (𝟘E φ₁ φ₂) = v ∉ φ₁ × v ∉ φ₂
  DistinctnessFormula .Distinctness._∉_ v 𝟙F = ⊤
  DistinctnessFormula .Distinctness._∉_ v 𝟙I = ⊤
  DistinctnessFormula .Distinctness._∉_ v (𝟙E φ₁ φ₂ φ₃) = v ∉ φ₁ × v ∉ φ₂ × v ∉ φ₃
  DistinctnessFormula .Distinctness._∉_ v ℕF = ⊤
  DistinctnessFormula .Distinctness._∉_ v ℕIᶻ = ⊤
  DistinctnessFormula .Distinctness._∉_ v (ℕIˢ φ₁) = v ∉ φ₁
  DistinctnessFormula .Distinctness._∉_ v (ℕE φ₁ φ₂ φ₃ φ₄) = v ∉ φ₁ × v ∉ φ₂ × v ∉ φ₃ × v ∉ φ₄
  DistinctnessFormula .Distinctness._∉_ v (=F φ₁ φ₂ φ₃) = v ∉ φ₁ × v ∉ φ₂ × v ∉ φ₃
  DistinctnessFormula .Distinctness._∉_ v (=I φ₁) = v ∉ φ₁
  DistinctnessFormula .Distinctness._∉_ v (=E φ₁ φ₂ φ₃ φ₄ φ₅) = v ∉ φ₁ × v ∉ φ₂ × v ∉ φ₃ × v ∉ φ₄ × v ∉ φ₅

  DistinctnessAbstraction .Distinctness._∉_ v (binders ⋆↦ φ) = ifYes v ∈? binders then ⊤ else v ∉ φ
