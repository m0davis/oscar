
```agda
{-# OPTIONS --allow-unsolved-metas #-}
```

```agda
module Type.NamedTypeTheory where
```

```agda
open import Type.Prelude
open import Type.Universe
open import Type.NamedVariable
open import Type.A2
open import Type.NamedA2
open import Type.NamedExpression alphabet
open import Type.NamedContext alphabet
```

-- I mutually-define well-formed contexts with well-typed (and?) well-scoped formulas in such contexts.

Contexts, well-typed.

```agda
data _ctx : Context → Set
```

Formulas, well-typed relative to one another.

```
infix 5 _⊢_∶_
data _⊢_∶_ (Γ : Context) : Expression → Expression → Set
infix 5 _⊢_≝_∶_
data _⊢_≝_∶_ (Γ : Context) : Expression → Expression → Expression → Set
```

```agda
infix 10 _ctx
data _ctx where
  ctx-EMP : ε ctx
  ctx-EXT : ∀ {Γ : Context} {Aₙ : Expression} {ℓ}
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
      → ∀ {i γ}
      → binder ≡ (i ,, γ)
      → Γ ⊢ 𝓋 i ∶ γ
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
     → Γ ⊢ Πf A x B ∶ 𝒰 ℓ
  ΠI : ∀ {x A b B}
     → Γ , x ∶ A ⊢ b ∶ B
     → Γ ⊢ Πi A x b ∶ Πf A x B
  ΠE : ∀ {f x A B a}
     → Γ ⊢ f ∶ Πf A x B
     → Γ ⊢ a ∶ A
     → ∀ {B'}
     → B [ a ↤₁E x  ] ≡ B'
     → Γ ⊢ Πe f a ∶ B'
  ΣF : ∀ {A x B ℓ}
     → Γ ⊢ A ∶ 𝒰 ℓ
     → Γ , x ∶ A ⊢ B ∶ 𝒰 ℓ
     → Γ ⊢ Σf A x B ∶ 𝒰 ℓ
  ΣI : ∀ {x A a b B ℓ}
     → Γ , x ∶ A ⊢ B ∶ 𝒰 ℓ
     → Γ ⊢ a ∶ A
     → Γ ⊢ b ∶ B [ a ↤₁E x ]
     → Γ ⊢ Σi a b ∶ Σf A x B
  ΣE : ∀ {A B z C x ℓ y p g Cp}
     → Γ , z ∶ Σf A x B ⊢ C ∶ 𝒰 ℓ
     → Γ , x ∶ A , y ∶ B ⊢ g ∶ C [ Σi (𝓋 x) (𝓋 y) ↤₁E z ]
     → Γ ⊢ p ∶ Σf A x B
     → C [ p ↤₁E z ] ≡ Cp
     → Γ ⊢ Σe z C x y g p ∶ Cp
  +F : ∀ {ℓ A B}
     → Γ ⊢ A ∶ 𝒰 ℓ
     → Γ ⊢ B ∶ 𝒰 ℓ
     → Γ ⊢ +f A B ∶ 𝒰 ℓ
  +Iˡ : ∀ {ℓ A B a}
      → Γ ⊢ A ∶ 𝒰 ℓ
      → Γ ⊢ B ∶ 𝒰 ℓ
      → Γ ⊢ a ∶ A
      → Γ ⊢ +iˡ a ∶ +f A B
  +Iʳ : ∀ {ℓ A B b}
      → Γ ⊢ A ∶ 𝒰 ℓ
      → Γ ⊢ B ∶ 𝒰 ℓ
      → Γ ⊢ b ∶ B
      → Γ ⊢ +iʳ b ∶ +f A B
  +E : ∀ {z A B x y C ℓ m n e Ce}
     → Γ , z ∶ +f A B ⊢ C ∶ 𝒰 ℓ
     → Γ , x ∶ A ⊢ m ∶ C [ +iˡ (𝓋 x) ↤₁E z ]
     → Γ , y ∶ B ⊢ n ∶ C [ +iʳ (𝓋 y) ↤₁E z ]
     → Γ ⊢ e ∶ +f A B
     → C [ e ↤₁E z ] ≡ Ce
     → Γ ⊢ +e z C x m y n e ∶ Ce
  𝟘F : ∀ {ℓ}
     → Γ ctx
     → Γ ⊢ 𝟘f ∶ 𝒰 ℓ
  𝟘E : ∀ {ℓ z C e C[e]}
     → Γ , z ∶ 𝟘f ⊢ C ∶ 𝒰 ℓ
     → Γ ⊢ e ∶ 𝟘f
     → C [ e ↤₁E z ] ≡ C[e]
     → Γ ⊢ 𝟘e z C e ∶ C[e]
  𝟙F : ∀ {ℓ}
     → Γ ctx
     → Γ ⊢ 𝟙f ∶ 𝒰 ℓ
  𝟙I : Γ ctx
     → Γ ⊢ 𝟙i ∶ 𝟙f
  𝟙E : ∀ {ℓ z C c e C[e]}
     → Γ , z ∶ 𝟙f ⊢ C ∶ 𝒰 ℓ
     → Γ ⊢ c ∶ C [ 𝟙i ↤₁E z ]
     → Γ ⊢ e ∶ 𝟙f
     → C [ e ↤₁E z ] ≡ C[e]
     → Γ ⊢ 𝟙e z C c e ∶ C[e]
  ℕF : ∀ {ℓ}
     → Γ ctx
     → Γ ⊢ ℕf ∶ 𝒰 ℓ
  ℕIᶻ : Γ ctx
      → Γ ⊢ ℕiᶻ ∶ ℕf
  ℕIˢ : ∀ {n}
      → Γ ⊢ n ∶ ℕf
      → Γ ⊢ ℕiˢ n ∶ ℕf
  ℕE : ∀ {z C ℓ cᶻ cˢ f n C[n]}
     → Γ , z ∶ ℕf ⊢ C ∶ 𝒰 ℓ
     → Γ ⊢ cᶻ ∶ C [ ℕiᶻ ↤₁E z ]
     → Γ , z ∶ ℕf , f ∶ C ⊢ cˢ ∶ C [ ℕiˢ (𝓋 z) ↤₁E z ]
     → Γ ⊢ n ∶ ℕf
     → C [ n ↤₁E z ] ≡ C[n]
     → Γ ⊢ ℕe z C cᶻ z f cˢ n ∶ C[n]
  =F : ∀ {ℓ A a b}
     → Γ ⊢ A ∶ 𝒰 ℓ
     → Γ ⊢ a ∶ A
     → Γ ⊢ b ∶ A
     → Γ ⊢ =f A a b ∶ 𝒰 ℓ
  =I : ∀ {A a}
     → Γ ⊢ a ∶ A
     → Γ ⊢ =i a ∶ =f A a a
  =E : ∀ {ℓ C z p a b x y A p' c C[a,b,p']}
     → Γ , x ∶ A , y ∶ A , p ∶ =f A (𝓋 x) (𝓋 y) ⊢ C ∶ 𝒰 ℓ
     → Γ , z ∶ A ⊢ c ∶ C [ 𝓋 z , 𝓋 z , =i (𝓋 z) ↤₃E x , y , p ]
     → Γ ⊢ a ∶ A
     → Γ ⊢ b ∶ A
     → Γ ⊢ p' ∶ =f A a b
     → C [ a , b , p' ↤₃E x , y , p ] ≡ C[a,b,p']
     → Γ ⊢ =e x y p C z c a b p' ∶ C[a,b,p']
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
     → Γ ⊢ Πi A x b ≝ Πi A x b' ∶ Πf A x B
  ΠE
    : ∀ {x a A b B}
    → Γ , x ∶ A ⊢ b ∶ B
    → Γ ⊢ a ∶ A
    → ∀ {b' B'}
    → b [ a ↤₁E x ] ≡ b'
    → B [ a ↤₁E x ] ≡ B'
    → Γ ⊢ Πe (Πi A x b) a ≝ b' ∶ B'
```

-- By requiring that the lambda-bound variable not be free in the term to be η-expanded, we avoid variable name-clashes.

-- For reasons I don't fully understand, I have also found it necessary to require that the lambda-bound variable not even exist in the context in order to make the proof of ≝-project₂ go through for the ΠU case.

```agda
  ΠU : ∀ {x A B f}
     → Γ ⊢ f ∶ Πf A x B
     → x ∉ Γ
     → Γ ⊢ f ≝ Πi A x (Πe f (𝓋 x)) ∶ Πf A x B
```

```agda
  ΣI : ∀ {x A a a' b b' B ℓ}
     → Γ , x ∶ A ⊢ B ∶ 𝒰 ℓ
     → Γ ⊢ a ≝ a' ∶ A
     → Γ ⊢ b ≝ b' ∶ B [ a ↤₁E x ]
     → Γ ⊢ Σi a b ≝ Σi a' b' ∶ Σf A x B
  ΣE : ∀ {A B z C x ℓ y g a b Cab gab}
     → Γ , z ∶ Σf A x B ⊢ C ∶ 𝒰 ℓ
     → Γ , x ∶ A , y ∶ B ⊢ g ∶ C [ Σi (𝓋 x) (𝓋 y) ↤₁E z ]
     → Γ ⊢ a ∶ A
     → Γ ⊢ b ∶ B [ a ↤₁E x ]
     → C [ Σi a b ↤₁E z ] ≡ Cab
     → g [ a , b ↤₂E x , y ] ≡ gab
     → Γ ⊢ Σe z C x y g (Σi a b) ≝ gab ∶ Cab
  +Iˡ : ∀ {ℓ A B a a'}
      → Γ ⊢ A ∶ 𝒰 ℓ
      → Γ ⊢ B ∶ 𝒰 ℓ
      → Γ ⊢ a ≝ a' ∶ A
      → Γ ⊢ +iˡ a ≝ +iˡ a' ∶ +f A B
  +Iʳ : ∀ {ℓ A B b b'}
      → Γ ⊢ A ∶ 𝒰 ℓ
      → Γ ⊢ B ∶ 𝒰 ℓ
      → Γ ⊢ b ≝ b' ∶ B
      → Γ ⊢ +iʳ b ≝ +iʳ b' ∶ +f A B
  +Eˡ : ∀ {z A B x y C ℓ l r a l[a] Ca}
      → Γ , z ∶ +f A B ⊢ C ∶ 𝒰 ℓ
      → Γ , x ∶ A ⊢ l ∶ C [ +iˡ (𝓋 x) ↤₁E z ]
      → Γ , y ∶ B ⊢ r ∶ C [ +iʳ (𝓋 y) ↤₁E z ]
      → Γ ⊢ a ∶ A
      → l [ a ↤₁E x ] ≡ l[a]
      → C [ +iˡ a ↤₁E z ] ≡ Ca
      → Γ ⊢ +e z C x l y r (+iˡ a) ≝ l[a] ∶ Ca
  +Eʳ : ∀ {z A B x y C ℓ l r b r[b] C[+Iʳb]}
      → Γ , z ∶ +f A B ⊢ C ∶ 𝒰 ℓ
      → Γ , x ∶ A ⊢ l ∶ C [ +iˡ (𝓋 x) ↤₁E z ]
      → Γ , y ∶ B ⊢ r ∶ C [ +iʳ (𝓋 y) ↤₁E z ]
      → Γ ⊢ b ∶ B
      → r [ b ↤₁E y ] ≡ r[b]
      → C [ +iʳ b ↤₁E z ] ≡ C[+Iʳb]
      → Γ ⊢ +e z C x l y r (+iʳ b) ≝ r[b] ∶ C[+Iʳb]
  𝟙E : ∀ {ℓ z C c C[𝟙I]}
     → Γ , z ∶ 𝟙f ⊢ C ∶ 𝒰 ℓ
     → Γ ⊢ c ∶ C [ 𝟙i ↤₁E z ]
     → C [ 𝟙i ↤₁E z ] ≡ C[𝟙I]
     → Γ ⊢ 𝟙e z C c 𝟙i ≝ c ∶ C[𝟙I]
  ℕIˢ : ∀ {n n'}
      → Γ ⊢ n ≝ n' ∶ ℕf
      → Γ ⊢ ℕiˢ n ≝ ℕiˢ n' ∶ ℕf
  ℕEᶻ : ∀ {z C ℓ cᶻ cˢ f C[ℕIᶻ]}
      → Γ , z ∶ ℕf ⊢ C ∶ 𝒰 ℓ
      → Γ ⊢ cᶻ ∶ C [ ℕiᶻ ↤₁E z ]
      → Γ , z ∶ ℕf , f ∶ C ⊢ cˢ ∶ C [ ℕiˢ (𝓋 z) ↤₁E z ]
      → C [ ℕiᶻ ↤₁E z ] ≡ C[ℕIᶻ]
      → Γ ⊢ ℕe z C cᶻ z f cˢ ℕiᶻ ≝ cᶻ ∶ C[ℕIᶻ]
  ℕEˢ : ∀ {z C ℓ cᶻ cˢ f n cˢ[n] C[ℕIˢn]}
      → Γ , z ∶ ℕf ⊢ C ∶ 𝒰 ℓ
      → Γ ⊢ cᶻ ∶ C [ ℕiᶻ ↤₁E z ]
      → Γ , z ∶ ℕf , f ∶ C ⊢ cˢ ∶ C [ ℕiˢ (𝓋 z) ↤₁E z ]
      → Γ ⊢ n ∶ ℕf
      → cˢ [ n , ℕe z C cᶻ z f cˢ n ↤₂E z , f ] ≡ cˢ[n]
      → C [ ℕiˢ n ↤₁E z ] ≡ C[ℕIˢn]
      → Γ ⊢ ℕe z C cᶻ z f cˢ (ℕiˢ n) ≝ cˢ[n] ∶ C[ℕIˢn]
  =I : ∀ {A a a'}
     → Γ ⊢ a ≝ a' ∶ A
     → Γ ⊢ =i a ≝ =i a' ∶ =f A a a {- should it be `=f A a a'`? -}
  =E : ∀ {ℓ C z p a x y A c c[a] C[a,a,=Ia]}
     → Γ , x ∶ A , y ∶ A , p ∶ =f A (𝓋 x) (𝓋 y) ⊢ C ∶ 𝒰 ℓ
     → Γ , z ∶ A ⊢ c ∶ C [ 𝓋 z , 𝓋 z , =i (𝓋 z) ↤₃E x , y , p ]
     → Γ ⊢ a ∶ A
     → c [ a ↤₁E z ] ≡ c[a]
     → C [ a , a , =i a ↤₃E x , y , p ] ≡ C[a,a,=Ia]
     → Γ ⊢ =e x y p C z c a a (=i a) ≝ c[a] ∶ C[a,a,=Ia]
```

```agda
infix 5 _⊨_
record _⊨_ (Γ : Context) (type : Expression) : Set where
  constructor ⟨_∶_⟩
  field
    term : Expression
    proof : Γ ⊢ term ∶ type
open _⊨_ public
```

```agda
infix 5 _⊩_
record _⊩_ (Γ : Context) (type : Expression) : Set where
  constructor ⟨_∋_⟩
  field
    universe : Universe
    proof : Γ ⊢ type ∶ 𝒰 universe
open _⊩_ public
```
