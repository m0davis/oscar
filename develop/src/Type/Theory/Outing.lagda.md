
```agda
{-# OPTIONS --allow-unsolved-metas #-}
```

```agda
module Type.Theory.Outing where
```

```agda
open import Type.Prelude
open import Type.Formula
open import Type.Universe
open import Type.Variable
open import Type.Context
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

```agda
infix 10 _ctx
data _ctx where
  ctx-EMP : ε ctx
  ctx-EXT : ∀ {Γ : Context} {Aₙ : Formula} {ℓ}
          → Γ ⊢ Aₙ ∶ 𝒰 ℓ
          → ∀ {xₙ}
          → xₙ ∉ Γ
          → Γ , xₙ ∶ Aₙ ctx
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
  𝟙I : Γ ctx
     → Γ ⊢ 𝟙I ∶ 𝟙F
  𝟙E : ∀ {ℓ z C c e C[e]}
     → Γ , z ∶ 𝟙F ⊢ C ∶ 𝒰 ℓ
     → Γ ⊢ c ∶ C [ 𝟙I ←₁ z ]
     → Γ ⊢ e ∶ 𝟙F
     → C [ e ←₁ z ] ≡ C[e]
     → Γ ⊢ 𝟙E (z ↦₁ C) c e ∶ C[e]
  ℕF : ∀ {ℓ}
     → Γ ctx
     → Γ ⊢ ℕF ∶ 𝒰 ℓ
  ℕIᶻ : Γ ctx
      → Γ ⊢ ℕIᶻ ∶ ℕF
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
     → Γ ⊢ A ∶ 𝒰 ℓ
     → Γ ⊢ a ∶ A
     → Γ ⊢ b ∶ A
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
```

By requiring that the lambda-bound variable not be free in the term to be η-expanded, we avoid variable name-clashes.

```agda
  ΠU
    : ∀ {x A B f}
    → Γ ⊢ f ∶ ΠF A (x ↦₁ B)
    → x ∉ f
    → Γ ⊢ f ≝ ΠI A (x ↦₁ ΠE f (𝓋 x)) ∶ ΠF A (x ↦₁ B)
```

```agda
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

```agda
infix 5 _⊨_
record _⊨_ (Γ : Context) (type : Formula) : Set where
  constructor ⟨_∶_⟩
  field
    term : Formula
    proof : Γ ⊢ term ∶ type
open _⊨_ public
```

```agda
infix 5 _⊩_
record _⊩_ (Γ : Context) (type : Formula) : Set where
  constructor ⟨_∋_⟩
  field
    universe : Universe
    proof : Γ ⊢ type ∶ 𝒰 universe
open _⊩_ public
```
