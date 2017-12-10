
```agda
{-# OPTIONS --allow-unsolved-metas #-}
```

```agda
module Type.Outing where
```

```agda
open import Type.Prelude
open import Type.Universe
```

```agda
Variable = Nat
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

In the overloaded combinator `_∉_` I express

```agda
record Distinctness (D : Set) : Set₁ where
  field
    _∉_ : Variable → D → Set
open Distinctness ⦃ … ⦄
```

```agda
data DistinctFromVariables {N} (x : Variable) (xs : Vec Variable N) : Set where
  ⟨_⟩ : ((p : Fin N) → indexVec xs p ≢ x) → DistinctFromVariables x xs

instance

  DistinctnessVariables : ∀ {N} → Distinctness (Vec Variable N)
  DistinctnessVariables .Distinctness._∉_ = DistinctFromVariables
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

```agda
infixl 15 _,_∶_
data Context : Set where
  ε : Context
  _,_∶_ : Context → Variable → Formula → Context
```

Combinators for contexts.

```agda
infixl 15 _,_
_,_ : Context → Context → Context
Γ , ε = Γ
Γ , (Δ , x ∶ A) = Γ , x ∶ A , Δ

lengthContext : Context → Nat
lengthContext ε = zero
lengthContext (Γ , _ ∶ _) = suc (lengthContext Γ)

indexContext : (Γ : Context) → Fin (lengthContext Γ) → Variable × Formula
indexContext Γ x with lengthContext Γ | graphAt lengthContext Γ
indexContext ε () | .0 | ingraph refl
indexContext (Γ , x ∶ φ) zero | .(suc (lengthContext Γ)) | ingraph refl = x ,, φ
indexContext (Γ , _ ∶ _) (suc i) | .(suc (lengthContext Γ)) | ingraph refl = indexContext Γ i
```

-- I mutually-define well-formed contexts with well-typed (and?) well-scoped formulas in such contexts.

Contexts, well-typed.

```agda
data _ctx : Context → Set
```

Formulas, well-typed relative to one another.

```
infix 5 _⊢_∶_
data _⊢_∶_ (Γ : Context) : Formula → Formula → Set
infix 5 _⊢_≝_∶_
data _⊢_≝_∶_ (Γ : Context) : Formula → Formula → Formula → Set
```

-- Appendix A.2 appeals to a side-condition on `ctx-EXT` that the added variable be distinct from the other variables listed in the context.

```agda
instance

  DistinctnessContext : Distinctness Context
  DistinctnessContext .Distinctness._∉_ v ε = ⊤
  DistinctnessContext .Distinctness._∉_ v (Γ , x ∶ A) = v ≢ x × v ∉ Γ

infix 10 _ctx
data _ctx where
  ctx-EMP : ε ctx
  ctx-EXT : ∀ {Γ : Context} {Aₙ : Formula} {ℓ}
          → Γ ⊢ Aₙ ∶ 𝒰 ℓ
          → ∀ {xₙ}
          → xₙ ∉ Γ
          → Γ , xₙ ∶ Aₙ ctx
```

-- simultaneous substitution

```agda
_[_⋆←⋆_] : Formula → ∀ {N} → Vec Formula N → Vec Variable N → Formula
𝒰 ℓ [ _ ⋆←⋆ _ ] = 𝒰 ℓ
𝓋 x [ σs ⋆←⋆ vs ] = {!!}
ΠF A (x ↦₁ B) [ σs ⋆←⋆ vs ] = ΠF (A [ σs ⋆←⋆ vs ]) {!!}
_[_⋆←⋆_] = {!!}

_[_⋆←⋆_]Ctx : Context → ∀ {N} → Vec Formula N → Vec Variable N → Context
ε [ _ ⋆←⋆ _ ]Ctx = ε
(Γ , x ∶ φ) [ σs ⋆←⋆ vs ]Ctx = {!!} , {!!} ∶ {!!}

_[_←₁_] : Formula → Formula → Variable → Formula
φ [ σ ←₁ x ] = φ [ σ ∷ [] ⋆←⋆ x ∷ [] ]

_[_,_←₂_,_] : Formula → Formula → Formula → Variable → Variable → Formula
φ [ σx , σy ←₂ x , y ] = φ [ σx ∷ σy ∷ [] ⋆←⋆ x ∷ y ∷ [] ]

_[_,_,_←₃_,_,_] : Formula → Formula → Formula → Formula → Variable → Variable → Variable → Formula
φ [ σx , σy , σz ←₃ x , y , z ] = φ [ σx ∷ σy ∷ σz ∷ [] ⋆←⋆ x ∷ y ∷ z ∷ [] ]
```

```agda
data _⊢_∶_ (Γ : Context) where
  var : Γ ctx
      → (i : Fin (lengthContext Γ))
      → ∀ {binder}
      → indexContext Γ i ≡ binder
      → Γ ⊢ 𝓋 (fst binder) ∶ snd binder
  ≝-subst
    : ∀ {a A B ℓ}
    → Γ ⊢ a ∶ A
    → Γ ⊢ A ≝ B ∶ 𝒰 ℓ
    → Γ ⊢ a ∶ B
  𝒰I : Γ ctx
     → ∀ {ℓ}
     → Γ ⊢ 𝒰 ℓ ∶ 𝒰 (suc ℓ)
  𝒰C : ∀ {A ℓ}
     → Γ ⊢ A ∶ 𝒰 ℓ
     → Γ ⊢ A ∶ 𝒰 (suc ℓ)
  ΠF : ∀ {A x B ℓ}
     → Γ ⊢ A ∶ 𝒰 ℓ
     → Γ , x ∶ A ⊢ B ∶ 𝒰 ℓ
     → Γ ⊢ ΠF A (x ↦₁ B) ∶ 𝒰 ℓ
  ΠI : ∀ {x A b B}
     → Γ , x ∶ A ⊢ b ∶ B
     → Γ ⊢ ΠI A (x ↦₁ b) ∶ ΠF A (x ↦₁ B)
  ΠE : ∀ {f x A B a}
     → Γ ⊢ f ∶ ΠF A (x ↦₁ B)
     → Γ ⊢ a ∶ A
     → ∀ {B'}
     → B [ a ←₁ x ] ≡ B'
     → Γ ⊢ ΠE f a ∶ B'
  ΣF : ∀ {A x B ℓ}
     → Γ ⊢ A ∶ 𝒰 ℓ
     → Γ , x ∶ A ⊢ B ∶ 𝒰 ℓ
     → Γ ⊢ ΣF A (x ↦₁ B) ∶ 𝒰 ℓ
  ΣI : ∀ {x A a b B ℓ}
     → Γ , x ∶ A ⊢ B ∶ 𝒰 ℓ
     → Γ ⊢ a ∶ A
     → Γ ⊢ b ∶ B [ a ←₁ x ]
     → Γ ⊢ ΣI a b ∶ ΣF A (x ↦₁ B)
  ΣE : ∀ {A B z C x ℓ y p g Cp}
     → Γ , z ∶ ΣF A (x ↦₁ B) ⊢ C ∶ 𝒰 ℓ
     → Γ , x ∶ A , y ∶ B ⊢ g ∶ C [ ΣI (𝓋 x) (𝓋 y) ←₁ z ]
     → Γ ⊢ p ∶ ΣF A (x ↦₁ B)
     → C [ p ←₁ z ] ≡ Cp
     → Γ ⊢ ΣE (z ↦₁ C) (x , y ↦₂ g) p ∶ Cp
  +F : ∀ {ℓ A B}
     → Γ ⊢ A ∶ 𝒰 ℓ
     → Γ ⊢ B ∶ 𝒰 ℓ
     → Γ ⊢ +F A B ∶ 𝒰 ℓ
  +Iˡ : ∀ {ℓ A B a}
      → Γ ⊢ A ∶ 𝒰 ℓ
      → Γ ⊢ B ∶ 𝒰 ℓ
      → Γ ⊢ a ∶ A
      → Γ ⊢ +Iˡ a ∶ +F A B
  +Iʳ : ∀ {ℓ A B b}
      → Γ ⊢ A ∶ 𝒰 ℓ
      → Γ ⊢ B ∶ 𝒰 ℓ
      → Γ ⊢ b ∶ B
      → Γ ⊢ +Iʳ b ∶ +F A B
  +E : ∀ {z A B x y C ℓ m n e Ce}
     → Γ , z ∶ +F A B ⊢ C ∶ 𝒰 ℓ
     → Γ , x ∶ A ⊢ m ∶ C [ +Iˡ (𝓋 x) ←₁ z ]
     → Γ , y ∶ B ⊢ n ∶ C [ +Iʳ (𝓋 y) ←₁ z ]
     → Γ ⊢ e ∶ +F A B
     → C [ e ←₁ z ] ≡ Ce
     → Γ ⊢ +E (z ↦₁ C) (x ↦₁ m) (y ↦₁ n) e ∶ Ce
  𝟘F : ∀ {ℓ}
     → Γ ctx
     → Γ ⊢ 𝟘F ∶ 𝒰 ℓ
  𝟘E : ∀ {ℓ z C e C[e]}
     → Γ , z ∶ 𝟘F ⊢ C ∶ 𝒰 ℓ
     → Γ ⊢ e ∶ 𝟘F
     → C [ e ←₁ z ] ≡ C[e]
     → Γ ⊢ 𝟘E (z ↦₁ C) e ∶ C[e]
  𝟙F : ∀ {ℓ}
     → Γ ctx
     → Γ ⊢ 𝟙F ∶ 𝒰 ℓ
  𝟙I : Γ ⊢ 𝟙I ∶ 𝟙F
  𝟙E : ∀ {ℓ z C c e C[e]}
     → Γ , z ∶ 𝟙F ⊢ C ∶ 𝒰 ℓ
     → Γ ⊢ c ∶ C [ 𝟙I ←₁ z ]
     → Γ ⊢ e ∶ 𝟙F
     → C [ e ←₁ z ] ≡ C[e]
     → Γ ⊢ 𝟙E (z ↦₁ C) c e ∶ C[e]
  ℕF : ∀ {ℓ}
     → Γ ctx
     → Γ ⊢ ℕF ∶ 𝒰 ℓ
  ℕIᶻ : Γ ⊢ ℕIᶻ ∶ ℕF
  ℕIˢ : ∀ {n}
      → Γ ⊢ n ∶ ℕF
      → Γ ⊢ ℕIˢ n ∶ ℕF
  ℕE : ∀ {z C ℓ cᶻ cˢ f n C[n]}
     → Γ , z ∶ ℕF ⊢ C ∶ 𝒰 ℓ
     → Γ ⊢ cᶻ ∶ C [ ℕIᶻ ←₁ z ]
     → Γ , z ∶ ℕF , f ∶ C ⊢ cˢ ∶ C [ ℕIˢ (𝓋 z) ←₁ z ]
     → Γ ⊢ n ∶ ℕF
     → C [ n ←₁ z ] ≡ C[n]
     → Γ ⊢ ℕE (z ↦₁ C) cᶻ (z , f ↦₂ cˢ) n ∶ C[n]
  =F : ∀ {ℓ A a b}
     → Γ ⊢ =F A a b ∶ 𝒰 ℓ
  =I : ∀ {A a}
     → Γ ⊢ a ∶ A
     → Γ ⊢ =I a ∶ =F A a a
  =E : ∀ {ℓ C z p a b x y A p' c C[a,b,p']}
     → Γ , x ∶ A , y ∶ A , p ∶ =F A (𝓋 x) (𝓋 y) ⊢ C ∶ 𝒰 ℓ
     → Γ , z ∶ A ⊢ c ∶ C [ 𝓋 z , 𝓋 z , =I (𝓋 z) ←₃ x , y , p ]
     → Γ ⊢ a ∶ A
     → Γ ⊢ b ∶ A
     → Γ ⊢ p' ∶ =F A a b
     → C [ a , b , p' ←₃ x , y , p ] ≡ C[a,b,p']
     → Γ ⊢ =E (x , y , p ↦₃ C) (z ↦₁ c) a b p' ∶ C[a,b,p']
```

```agda
data _⊢_≝_∶_ (Γ : Context) where
  ≝-reflexivity
    : ∀ {a A}
    → Γ ⊢ a ∶ A
    → Γ ⊢ a ≝ a ∶ A
  ≝-symmetry
    : ∀ {a b A}
    → Γ ⊢ a ≝ b ∶ A
    → Γ ⊢ b ≝ a ∶ A
  ≝-transitivity
    : ∀ {a b c A}
    → Γ ⊢ a ≝ b ∶ A
    → Γ ⊢ b ≝ c ∶ A
    → Γ ⊢ a ≝ c ∶ A
  ≝-subst
    : ∀ {a b A B ℓ}
    → Γ ⊢ a ≝ b ∶ A
    → Γ ⊢ A ≝ B ∶ 𝒰 ℓ
    → Γ ⊢ a ≝ b ∶ B
  ΠI : ∀ {x A b b' B}
     → Γ , x ∶ A ⊢ b ≝ b' ∶ B
     → Γ ⊢ ΠI A (x ↦₁ b) ≝ ΠI A (x ↦₁ b') ∶ ΠF A (x ↦₁ B)
  ΠE
    : ∀ {x a A b B}
    → Γ , x ∶ A ⊢ b ∶ B
    → Γ ⊢ a ∶ A
    → ∀ {b' B'}
    → b [ a ←₁ x ] ≡ b'
    → B [ a ←₁ x ] ≡ B'
    → Γ ⊢ ΠE (ΠI A (x ↦₁ b)) a ≝ b' ∶ B'
  ΠU
    : ∀ {x A B f}
    → Γ ⊢ f ∶ ΠF A (x ↦₁ B)
    → Γ ⊢ f ≝ ΠI A (x ↦₁ ΠE f (𝓋 x)) ∶ ΠF A (x ↦₁ B)
  ΣI : ∀ {x A a a' b b' B ℓ}
     → Γ , x ∶ A ⊢ B ∶ 𝒰 ℓ
     → Γ ⊢ a ≝ a' ∶ A
     → Γ ⊢ b ≝ b' ∶ B [ a ←₁ x ]
     → Γ ⊢ ΣI a b ≝ ΣI a' b' ∶ ΣF A (x ↦₁ B)
  ΣE : ∀ {A B z C x ℓ y g a b Cab gab}
     → Γ , z ∶ ΣF A (x ↦₁ B) ⊢ C ∶ 𝒰 ℓ
     → Γ , x ∶ A , y ∶ B ⊢ g ∶ C [ ΣI (𝓋 x) (𝓋 y) ←₁ z ]
     → Γ ⊢ a ∶ A
     → Γ ⊢ b ∶ B [ a ←₁ x ]
     → C [ ΣI a b ←₁ z ] ≡ Cab
     → g [ a , b ←₂ x , y ] ≡ gab
     → Γ ⊢ ΣE (z ↦₁ C) (x , y ↦₂ g) (ΣI a b) ≝ gab ∶ Cab
  +Iˡ : ∀ {ℓ A B a a'}
      → Γ ⊢ A ∶ 𝒰 ℓ
      → Γ ⊢ B ∶ 𝒰 ℓ
      → Γ ⊢ a ≝ a' ∶ A
      → Γ ⊢ +Iˡ a ≝ +Iˡ a' ∶ +F A B
  +Iʳ : ∀ {ℓ A B b b'}
      → Γ ⊢ A ∶ 𝒰 ℓ
      → Γ ⊢ B ∶ 𝒰 ℓ
      → Γ ⊢ b ≝ b' ∶ B
      → Γ ⊢ +Iʳ b ≝ +Iʳ b' ∶ +F A B
  +Eˡ : ∀ {z A B x y C ℓ l r a l[a] Ca}
      → Γ , z ∶ +F A B ⊢ C ∶ 𝒰 ℓ
      → Γ , x ∶ A ⊢ l ∶ C [ +Iˡ (𝓋 x) ←₁ z ]
      → Γ , y ∶ B ⊢ r ∶ C [ +Iʳ (𝓋 y) ←₁ z ]
      → Γ ⊢ a ∶ A
      → l [ a ←₁ x ] ≡ l[a]
      → C [ +Iˡ a ←₁ z ] ≡ Ca
      → Γ ⊢ +E (z ↦₁ C) (x ↦₁ l) (y ↦₁ r) (+Iˡ a) ≝ l[a] ∶ Ca
  +Eʳ : ∀ {z A B x y C ℓ l r b r[b] C[+Iʳb]}
      → Γ , z ∶ +F A B ⊢ C ∶ 𝒰 ℓ
      → Γ , x ∶ A ⊢ l ∶ C [ +Iˡ (𝓋 x) ←₁ z ]
      → Γ , y ∶ B ⊢ r ∶ C [ +Iʳ (𝓋 y) ←₁ z ]
      → Γ ⊢ b ∶ B
      → r [ b ←₁ y ] ≡ r[b]
      → C [ +Iʳ b ←₁ z ] ≡ C[+Iʳb]
      → Γ ⊢ +E (z ↦₁ C) (x ↦₁ l) (y ↦₁ r) (+Iʳ b) ≝ r[b] ∶ C[+Iʳb]
  𝟙E : ∀ {ℓ z C c C[𝟙I]}
     → Γ , z ∶ 𝟙F ⊢ C ∶ 𝒰 ℓ
     → Γ ⊢ c ∶ C [ 𝟙I ←₁ z ]
     → C [ 𝟙I ←₁ z ] ≡ C[𝟙I]
     → Γ ⊢ 𝟙E (z ↦₁ C) c 𝟙I ≝ c ∶ C[𝟙I]
  ℕIˢ : ∀ {n n'}
      → Γ ⊢ n ≝ n' ∶ ℕF
      → Γ ⊢ ℕIˢ n ≝ ℕIˢ n' ∶ ℕF
  ℕEᶻ : ∀ {z C ℓ cᶻ cˢ f C[ℕIᶻ]}
      → Γ , z ∶ ℕF ⊢ C ∶ 𝒰 ℓ
      → Γ ⊢ cᶻ ∶ C [ ℕIᶻ ←₁ z ]
      → Γ , z ∶ ℕF , f ∶ C ⊢ cˢ ∶ C [ ℕIˢ (𝓋 z) ←₁ z ]
      → C [ ℕIᶻ ←₁ z ] ≡ C[ℕIᶻ]
      → Γ ⊢ ℕE (z ↦₁ C) cᶻ (z , f ↦₂ cˢ) ℕIᶻ ≝ cᶻ ∶ C[ℕIᶻ]
  ℕEˢ : ∀ {z C ℓ cᶻ cˢ f n cˢ[n] C[ℕIˢn]}
      → Γ , z ∶ ℕF ⊢ C ∶ 𝒰 ℓ
      → Γ ⊢ cᶻ ∶ C [ ℕIᶻ ←₁ z ]
      → Γ , z ∶ ℕF , f ∶ C ⊢ cˢ ∶ C [ ℕIˢ (𝓋 z) ←₁ z ]
      → Γ ⊢ n ∶ ℕF
      → cˢ [ n , ℕE (z ↦₁ C) cᶻ (z , f ↦₂ cˢ) n ←₂ z , f ] ≡ cˢ[n]
      → C [ ℕIˢ n ←₁ z ] ≡ C[ℕIˢn]
      → Γ ⊢ ℕE (z ↦₁ C) cᶻ (z , f ↦₂ cˢ) (ℕIˢ n) ≝ cˢ[n] ∶ C[ℕIˢn]
  =I : ∀ {A a a'}
     → Γ ⊢ a ≝ a' ∶ A
     → Γ ⊢ =I a ≝ =I a' ∶ =F A a a {- should it be `=F A a a'`? -}
  =E : ∀ {ℓ C z p a x y A c c[a] C[a,a,=Ia]}
     → Γ , x ∶ A , y ∶ A , p ∶ =F A (𝓋 x) (𝓋 y) ⊢ C ∶ 𝒰 ℓ
     → Γ , z ∶ A ⊢ c ∶ C [ 𝓋 z , 𝓋 z , =I (𝓋 z) ←₃ x , y , p ]
     → Γ ⊢ a ∶ A
     → c [ a ←₁ z ] ≡ c[a]
     → C [ a , a , =I a ←₃ x , y , p ] ≡ C[a,a,=Ia]
     → Γ ⊢ =E (x , y , p ↦₃ C) (z ↦₁ c) a a (=I a) ≝ c[a] ∶ C[a,a,=Ia]
```

admissible rules

```agda
-- uniqueness principle for Σ (possibly not correctly stated)
ΣU : ∀ {Γ A x B c y z}
   → Γ ⊢ c ∶ ΣF A (x ↦₁ B)
   → Γ ⊢ c ≝ ΣE (z ↦₁ 𝓋 z) (x , y ↦₂ ΣI (𝓋 x) (𝓋 y)) c ∶ ΣF A (x ↦₁ B)
ΣU x₁ = ≝-symmetry {!!}

-- TODO fromterm and fromctx deserve to be renamed and/or refactored

fromterm : ∀ {Γ c C}
         → Γ ⊢ c ∶ C
         → ∃ λ ℓ → Γ ⊢ C ∶ 𝒰 ℓ
fromterm x = {!!}

fromctx : ∀ {Γ x A c C}
        → Γ , x ∶ A ⊢ c ∶ C
        → ∃ λ ℓ → Γ ⊢ A ∶ 𝒰 ℓ
fromctx x₁ = fromterm (var {!!} {!!} {!!})


≝-project₁ : ∀ {Γ a b A}
          → Γ ⊢ a ≝ b ∶ A
          → Γ ⊢ a ∶ A
≝-project₂ : ∀ {Γ a b A}
          → Γ ⊢ a ≝ b ∶ A
          → Γ ⊢ b ∶ A

≝-project₁ (≝-reflexivity Γ⊢a∶A) = Γ⊢a∶A
≝-project₁ (≝-symmetry Γ⊢b≝a∶A) = ≝-project₂ Γ⊢b≝a∶A
≝-project₁ (≝-transitivity Γ⊢a≝b∶A _) = ≝-project₁ Γ⊢a≝b∶A
≝-project₁ (≝-subst Γ⊢a≝b∶B Γ⊢B≝A∶𝒰) = ≝-subst (≝-project₁ Γ⊢a≝b∶B) Γ⊢B≝A∶𝒰
≝-project₁ (ΠI Γ,x∶A⊢b≝b'∶B) = ΠI (≝-project₁ Γ,x∶A⊢b≝b'∶B)
≝-project₁ (ΠE Γ,x∶A⊢b∶B Γ⊢a∶A _ B[a]≡B') = ΠE (ΠI Γ,x∶A⊢b∶B) Γ⊢a∶A B[a]≡B'
≝-project₁ (ΠU Γ⊢f∶ΠFAB) = Γ⊢f∶ΠFAB
≝-project₁ (ΣI Γ⊢x∶A⊢B∶𝒰 Γ⊢a≝a'∶A Γ⊢b≝b'∶B[a]) = ΣI Γ⊢x∶A⊢B∶𝒰 (≝-project₁ Γ⊢a≝a'∶A) (≝-project₁ Γ⊢b≝b'∶B[a])
≝-project₁ (ΣE Γ,z∶ΣFAB⊢C∶𝒰 x₂ x₃ x₄ x₅ x₆) = ΣE Γ,z∶ΣFAB⊢C∶𝒰 x₂ (ΣI (snd (fromctx x₂)) x₃ x₄) x₅
≝-project₁ (+Iˡ x x₁ Γ⊢a≝b∶A) = {!!}
≝-project₁ (+Iʳ x x₁ Γ⊢a≝b∶A) = {!!}
≝-project₁ (+Eˡ x₁ x₂ x₃ x₄ x₅ x₆) = {!!}
≝-project₁ (+Eʳ x₁ x₂ x₃ x₄ x₅ x₆) = {!!}
≝-project₁ (𝟙E x x₁ x₂) = {!!}
≝-project₁ (ℕIˢ Γ⊢a≝b∶A) = {!!}
≝-project₁ (ℕEᶻ x x₁ x₂ x₃) = {!!}
≝-project₁ (ℕEˢ x x₁ x₂ x₃ x₄ x₅) = {!!}
≝-project₁ (=I Γ⊢a≝b∶A) = {!!}
≝-project₁ (=E x₁ x₂ x₃ x₄ x₅) = {!!}

≝-project₂ (≝-reflexivity Γ⊢a∶A) = Γ⊢a∶A
≝-project₂ (≝-symmetry Γ⊢b≝a∶A) = ≝-project₁ Γ⊢b≝a∶A
≝-project₂ (≝-transitivity Γ⊢a≝b∶A Γ⊢a≝b∶A₁) = {!!}
≝-project₂ (≝-subst Γ⊢a≝b∶A Γ⊢a≝b∶A₁) = {!!}
≝-project₂ (ΠI Γ⊢a≝b∶A) = {!!}
≝-project₂ (ΠE x₁ x₂ x₃ x₄) = {!!}
≝-project₂ (ΠU x₁) = {!!}
≝-project₂ (ΣI x₁ Γ⊢a≝b∶A Γ⊢a≝b∶A₁) = ΣI {!!} {!!} {!!}
≝-project₂ (ΣE x₁ x₂ x₃ x₄ x₅ x₆) = {!!}
≝-project₂ (+Iˡ x x₁ Γ⊢a≝b∶A) = {!!}
≝-project₂ (+Iʳ x x₁ Γ⊢a≝b∶A) = {!!}
≝-project₂ (+Eˡ x₁ x₂ x₃ x₄ x₅ x₆) = {!!}
≝-project₂ (+Eʳ x₁ x₂ x₃ x₄ x₅ x₆) = {!!}
≝-project₂ (𝟙E x x₁ x₂) = {!!}
≝-project₂ (ℕIˢ Γ⊢a≝b∶A) = {!!}
≝-project₂ (ℕEᶻ x x₁ x₂ x₃) = {!!}
≝-project₂ (ℕEˢ x x₁ x₂ x₃ x₄ x₅) = {!!}
≝-project₂ (=I Γ⊢a≝b∶A) = {!!}
≝-project₂ (=E x₁ x₂ x₃ x₄ x₅) = {!!}

wkg₁ : ∀ {Δ} {Γ} {x A B b ℓ}
     → Γ ⊢ A ∶ 𝒰 ℓ
     → Γ , Δ ⊢ b ∶ B
     → x ∉ Γ -- the weakening variable must not be confused for anything in its suffix
     → ∀ {Γ'}
     → Γ , x ∶ A , Δ ≡ Γ'
     → Γ' ⊢ b ∶ B

wkg₂ : ∀ {Γ} {Δ : Context} {x A B b c ℓ}
     → Γ ⊢ A ∶ 𝒰 ℓ
     → Γ , Δ ⊢ b ≝ c ∶ B
     → x ∉ Γ
     → ∀ {Γ'}
     → Γ , x ∶ A , Δ ≡ Γ'
     → Γ' ⊢ b ≝ c ∶ B

wkg₁ = {!!}

wkg₂ = {!!}
```

```agda
subst₁ : ∀ {Γ Δ a A b B x}
       → Γ ⊢ a ∶ A
       → Γ , x ∶ A , Δ ⊢ b ∶ B
       → Γ , (Δ [ a ∷ [] ⋆←⋆ x ∷ [] ]Ctx) ⊢ b [ a ←₁ x ] ∶ B [ a ←₁ x ]

subst₂ : ∀ {Γ Δ a A b b' B x}
       → Γ ⊢ a ∶ A
       → Γ , x ∶ A , Δ ⊢ b ≝ b' ∶ B
       → Γ , (Δ [ a ∷ [] ⋆←⋆ x ∷ [] ]Ctx) ⊢ b [ a ←₁ x ] ≝ b' [ a ←₁ x ] ∶ B [ a ←₁ x ]

subst₁ = {!!}

subst₂ = {!!}
```

```agda
infix 5 _⊢_
record _⊢_ (Γ : Context) (type : Formula) : Set where
  constructor ⟨_≈_⟩
  field
    term : Formula
    proof : Γ ⊢ term ∶ type
```
