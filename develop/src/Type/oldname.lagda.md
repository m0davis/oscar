
```agda
{-# OPTIONS --allow-unsolved-metas #-}
```

# Type theory with named variables

```agda
module Type.oldname where
```

I would like to use the type-checker to prevent mistakes when renaming and substituting DeBruijn-indexed variables.

```agda
open import Type.Prelude
open import Type.Complexity
open import Type.Universe
```

I shall take the notion of a symbol to be a primitive concept, except insofar as I think of a symbol as something that can be written down, strung together, moved around. A term is an arrangement of symbols that have been given meta-theoretic semantics. A term is called lexically-checked if it is guaranteed to be in a suitable arrangement to have some meta-theoretically-denoted meaning. A term is called scope-checked if ...

An `STerm` is a scope-checked term.

```agda
open import Type.SCTerm
```

A context is a container of types. A

```agda
data Cx : Set where
```

length-and-complexity-indexed contexts

```agda
data _ctx⋖_ : Nat → Complexity → Set
```

```agda
record _ctx (N : Nat) : Set where
  field
    complexity : Complexity
    context : N ctx⋖ complexity
open _ctx public
```

type-checked terms

```agda
data _⊢_∋_⋖_ {N} (Γ : Cx) : Universe → Term N → Complexity → Set
```

...

I would like to have a type-checked version of `instantiateTerm {N} n ρ τ`. I define a type-checked substutition of Γ ⊢ τ[ρ/γₙ] as that yielding `instantiateTerm {N} n ρ τ` if and only if Γ ⊢ ρ and Δ ⊢ τ, where Γ = γ₀ , γ₁ , ... γ_N-1 and Δ = γ₀ , γ₁ , ... , γₙ₋₁ , γₙ , γₙ₊₁ , ... γ_N-1. Currently, `instantiateTerm` yields such a result under the conditions specified but also under other conditions as well.

sketch of new way:

ℕE :
     (X : ⊣ Γ , ℕF)
     (x₀ : Γ ⊢ X)
     (xₛ : Γ , ℕF , X ⊢ X [ ℕIˢ (𝓋 zero) / zero ])
     (n : Γ ⊢ ℕF)
     (X[n] : X [ n / zero ])

or

ℕE : (N : ℕF ⊣ Γ)
     (X : ⊣ Γ , N)
     (x₀ : Γ ⊢ X)
     (xₛ : Γ , ℕF , X ⊢ X [ ℕIˢ (ℕF ∋ 𝓋 zero) / ℕF ∋ zero ])
     (n : Γ ⊢ ℕF)
     (X[n] : X [ n / N ])
     → Γ ⊢ ℕe X x₀ xₛ n ∶ X[n] ⋖ χ

⊢ ⊣ ⊤ ⊥ ⊦ ⊧ ⊨ ⊩ ⊪ ⊫ ⊬ ⊭ ⊮ ⊯
∈ ∉ ∊ ∋ ∌ ∍ ⋲ ⋳ ⋴ ⋵ ⋶ ⋷ ⋸ ⋹ ⋺ ⋻ ⋼ ⋽ ⋾ ⋿
< ≪ ⋘ ≤ ≦ ≲ ≶ ≺ ≼ ≾ ⊂ ⊆ ⋐ ⊏ ⊑ ⊰ ⊲ ⊴ ⋖ ⋚ ⋜ ⋞
> ≫ ⋙ ≥ ≧ ≳ ≷ ≻ ≽ ≿ ⊃ ⊇ ⋑ ⊐ ⊒ ⊱ ⊳ ⊵ ⋗ ⋛ ⋝ ⋟


infix 5 ⊣_
infixl 10 _,_
infix ?? _∈_
infix ?? _⊢_
infix 15 _[_/_]

ctx₀     : Set -- context of scope-checked terms (historically, ctx₀ = Nat)
ctx=     : Nat → Set -- size-indexed context of sort-checked terms, Γ
ctx      : Set -- context
⊣_       : ∀ {N} → ctx= N → Set -- sort-checked term, γ
-- want _,_ and _⊢_ overloaded
_,_      : ∀ {N} (Γ : ctx= N) → ⊣ Γ → ctx= (suc N) -- Γ , γ = context constructor, prefixing γ to Γ
_,_      : ∀ {N} (Γ : ctx N) → ⊣ Γ → ctx (suc N) -- Γ , γ = context constructor, prefixing γ to Γ
_∶_      : ∀ {N} → Fin N → ∀ {Γ : ctx N} → ⊣ Γ → Set -- x ∶ γ = a named variable, 𝓍, of sort-checked term γ at position x in its context
_⊢_      : ∀ {N} → (Γ : ctx= N) → ⊣ Γ → Set -- Γ ⊢ γ = a type-checked term, τ, of type γ in context Γ
_[_/_]   : ∀ {N} {Γ : ctx= N} {γ₀ : ⊣ Γ} {γ₁ : ⊣ Γ , γ₀}
                 (τ₁ : Γ , γ₀ ⊢ γ₁) →
                 Γ ⊢ γ₀ →
                 ∀ {x} → x ∶ γ₀ →
                 Set -- τ₁ [ τ₀ / 𝓍 ] = a substitution, σ, of τ₀ for 𝓍 in τ₁.
ℕF       : ∀ {Γ} → ⊣ Γ -- ℕF = context-indexed type constructor, natural numbers
ℕIˢ      : ∀ {Γ} → Γ ⊢ ℕF → ⊣ Γ -- ℕIˢ n = context-indexed type constructor,
ℕE       :
data _⊢_∶_⋖_ {N} (Γ : ctx= N) : Term N → Term N →
_⊢_∶_⋖_

ℕE : (X : ⊣ Γ , ℕF)
     (𝓍 : zero ∶ X) -- Γ , x ∶ ℕF ⊢ X
     (x₀ : Γ ⊢ X)
     (xₛ : Γ , ℕF , X ⊢ X [ ℕIˢ 𝓍 / 𝓍 ])
     (n : Γ ⊢ ℕF)
     (X[n] : X [ n / 𝓍 ])
     → Γ ⊢ ℕe X x₀ xₛ n ∶ X[n] ⋖ χ

+E :

ΣE :
  (A : ℓ ⊣ Γ)
  (B : ℓ ⊣ Γ , A)
  (C : ℓ ⊣ Γ , ΣF A B)
  (g : Γ , A , B ⊢ C [ ΣI A B / zero ])

  ΠE :
    -- there is some type provided by Γ, we call it A.
    -- a projection, term : ∀ {N} {Γ : N ctx} → ⊣ Γ → Term N
    -- That is, Γ ⊢ term A
    (A : ⊣ Γ)
    (B : ⊣ (Γ , A))
    (f : Γ ⊢ Π A B) -- I should use ΠF here but I am worried about name conflicts between the scope-checked-term constructor and the type-checked-term constructor. Perhaps these should be renamed or use module name disambiguation. A new naming scheme would have Πf or πF, σF, 1f, 0f, or ∨F ... I think I prefer using the lowercase f, e, i, etc. to distinguish. ... actually, the input here is clearly not a SCTerm b/c A has been defined as ⊣ Γ... So ΠF is fine anyway --
    (a : Γ ⊢ A)
    (B[a] : B [ a / zero ∶ A ]) -- the extra "∶ A" is just there for readability. Agda should know from the context related to B that the zeroeth member is of type A. The given datatype guarantees that the contexts are the same except in for an insertion in the prescribed place.
    → Γ ⊢ Πe f a -- Πe is a field with an instance argument to decide what to make of the input and output types. If we were to spell it out w/o such help, perhaps it would go: ΠE (term⊢ f) (term⊢ a)
     -- but this gets dangerous with the green slime and all... so we need a conversion datatype
       {-
          one way to go is to use ≡. Before the last argument of the constructor, we would have something like
          ∀ {τf τa τB[a] δf δa δB[a]} →
          term⊢ f ≡ τf →
          term⊢ a ≡ τa →
          termσ B[a] ≡ τB[a] →
          complexity⊢ f ≡ δf →
          complexity⊢ a ≡ δa →
          complexityσ B[a] ≡ δB[a] →
          Γ ⊢ ΠE τf τa ∶ τB[a]
       -}
     ∶ ?? B[a]
     ⋖ sumcomplexity

## type-checked terms

```
-- Γ ⊢ a : A ⋖ χ = a proves A given Γ, with complexity χ
data _⊢_∶_⋖_ {N χ} (Γ : N ctx⋖ χ) : Term N → Term N → Complexity → Set


data _⊢_≝_∶_⋖_ {N χ} (Γ : N ctx⋖ χ) : Term N → Term N → Term N → Complexity → Set

-- Γ ⊢ a : A = a is a proof of A given Γ
_⊢_∶_ : ∀ {N χ} (Γ : N ctx⋖ χ) → Term N → Term N → Set
Γ ⊢ a ∶ A = ∃ (Γ ⊢ a ∶ A ⋖_)

-- Γ ⊢ A = there is a proof of A given Γ
--record _⊢_ {N χ} (Γ : N ctx⋖ χ) (τ : Term N) : Set where
record _⊢_ {N} (Γ : N ctx) (τ : Term N) : Set where
  field
    χ : Complexity
    proof : Term N
    the-field : _⊢_∶_⋖_ (context Γ) proof τ χ

-- Γ ⊢ A ≼ δ = there is a proof of A given Γ of size ≤ δ
_⊢_≼_ : ∀ {N χ} (Γ : N ctx⋖ χ) → Term N → Nat → Set
Γ ⊢ A ≼ δ = ∃ λ a → ∃ λ χ → χ-measure χ ≤ δ × Γ ⊢ a ∶ A ⋖ χ
```

I write the conditions of compatible contexts as

    B ∋ A ⊣ Γ⊢A ∧ Δ⊢B

Or maybe this idea

    ρ < τ ⊣ Γ -- meaning ρ and τ share a common context and ρ is less specific than τ

      which should imply that

        (Γ ⋯ Ξ ⊢ ρ →

```agda
data _∋_⊣_∧_ {N} (B : Term (suc N)) (A : Term N)
             : ∀ {Γ : N ctx} {Δ : suc N ctx}
             → Γ ⊢ A → Δ ⊢ B → Set
```

We should be able to extract the position of the difference.

```agda
δ-position : ∀ {N} {B : Term (suc N)} {A : Term N}
           → ∀ {Γ : N ctx} {Δ : suc N ctx}
           → {Γ⊢A : Γ ⊢ A} {Δ⊢B : Δ ⊢ B}
           → B ∋ A ⊣ Γ⊢A ∧ Δ⊢B
           → Fin (suc N)
δ-position = {!!}
```

Then a type-checked singular substitution may be defined as:

```agda
substitute : ∀ {N} {B : Term (suc N)} {A : Term N}
           → ∀ {Γ : N ctx} {Δ : suc N ctx}
           → {Γ⊢A : Γ ⊢ A} {Δ⊢B : Δ ⊢ B}
           → B ∋ A ⊣ Γ⊢A ∧ Δ⊢B
           → Term N
substitute {B = B} {A = A} B∋A = instantiateTerm (δ-position B∋A) A B
```

Notice that the above does not give us a guarantee we want: namely that

  Γ ⊢ substitute B∋A⊣Γ⊢A∧Δ⊢B ∶

```agda
infixl 25 _,_

data _ctx⋖_ where
  [] : zero ctx⋖ c []
  _,_ : ∀ {N ℓ A δΓ δA} →
              (Γ : N ctx⋖ δΓ) → Γ ⊢ A ∶ 𝒰 ℓ ⋖ δA →
            suc N ctx⋖ c (δΓ ∷ δA ∷ [])

_at_ : ∀ {N χ} → N ctx⋖ χ → Fin N → Term N
_,_ {A = A} Γ γ at zero = weakenTermFrom zero A
(Γ , _) at suc n = weakenTermFrom zero (Γ at n)
```

Γ at n = the type of the n-th member of the context Γ. Shall we not also be able to talk about τ ∈ Γ as evidence for a (scope-checked) Term being

Maybe what I need is a notion of a type-checked rather than a scope-checked term.

```agda
data _∈_ : {N : Nat} → Term N → N ctx → Set where
  ⟨_⟩ : ∀ {N χ} (location : Fin N) → {!!}
```

```agda
data _⊢_∋_⋖_ {N} (Γ : Cx) where
  zero :
    Γ ⊢ suc zero ∋ 𝒰 zero ⋖ c []
  suc : ∀ {ℓ A δA} →
    Γ ⊢ ℓ ∋ A ⋖ δA →
    Γ ⊢ (suc ℓ) ∋ A ⋖ c (δA ∷ [])
```

```agda
```

```agda
data _∋_⊣_∧_ {N} (B : Term (suc N)) (A : Term N) where
  -- ε : ∀ {ℓ χ} → (⊢B : {!!} ⊢ B ∶ 𝒰 ℓ ⋖ χ) → B ∋ A ⊣ evidence {![]!} ∧ evidence {![]!} -- ({!{![]!} ,, {!⊢B!}!})

data _⊢_∶_⋖_ {N χ} (Γ : N ctx⋖ χ) where
  Vble :
    ∀ {n A} →
    Γ at n ≡ A →
    Γ ⊢ 𝓋 n ∶ A ⋖ c []

  𝒰I : ∀ {ℓ} →
    Γ ⊢ 𝒰 ℓ ∶ 𝒰 (suc ℓ) ⋖ c []
  𝒰C : ∀ {ℓ A δA} →
    Γ ⊢ A ∶ 𝒰 ℓ ⋖ δA →
    Γ ⊢ A ∶ 𝒰 (suc ℓ) ⋖ c (δA ∷ [])
  ΠF : ∀ {ℓ A B δA δB} →
      (⊢A : Γ ⊢ A ∶ 𝒰 ℓ ⋖ δA) →
      Γ , ⊢A ⊢ B ∶ 𝒰 ℓ ⋖ δB →
    Γ ⊢ ΠF A B ∶ 𝒰 ℓ ⋖ c (δA ∷ δB ∷ [])
  ΠI : ∀ ℓ {A B b δA δb} →
    (⊢A : Γ ⊢ A ∶ 𝒰 ℓ ⋖ δA) →
    Γ , ⊢A ⊢ b ∶ B ⋖ δb →
    Γ ⊢ ΠI b ∶ ΠF A B ⋖ c (δA ∷ δb ∷ [])
  ΠE : ∀ A B {B[a] f a δf δa} →
    Γ ⊢ f ∶ ΠF A B ⋖ δf →
    Γ ⊢ a ∶ A ⋖ δa →
    instantiateTerm zero a B ≡ B[a] →
    Γ ⊢ ΠE f a ∶ B[a] ⋖ c (δf ∷ δa ∷ [])
  ΣF : ∀ {ℓ A B δA δB} →
    (⊢A : Γ ⊢ A ∶ 𝒰 ℓ ⋖ δA) →
    Γ , ⊢A ⊢ B ∶ 𝒰 ℓ ⋖ δB →
    Γ ⊢ ΣF A B ∶ 𝒰 ℓ ⋖ c (δA ∷ δB ∷ [])
```



```agda
  ΣI : ∀ ℓ {A B a b δA δB δa δb} →
    (⊢A : Γ ⊢ A ∶ 𝒰 ℓ ⋖ δA) →
    Γ , ⊢A ⊢ B ∶ 𝒰 ℓ ⋖ δB →
    Γ ⊢ a ∶ A ⋖ δa →
    Γ ⊢ b ∶ instantiateTerm zero a B ⋖ δb →
    Γ ⊢ ΣI a b ∶ ΣF A B ⋖ c (δA ∷ δB ∷ δa ∷ δb ∷ [])
```

I would like to have written this instead as


```agda
  ΣE : ∀ ℓ A B {C[p] C g p δA δB δC δg δp} →
      (⊢A : Γ ⊢ A ∶ 𝒰 ℓ ⋖ δA) →
      (⊢B : Γ , ⊢A ⊢ B ∶ 𝒰 ℓ ⋖ δB) →
      Γ , ΣF ⊢A ⊢B ⊢ C ∶ 𝒰 ℓ ⋖ δC →
      Γ , ⊢A , ⊢B ⊢ g ∶ instantiateTerm (suc (suc zero))
                                          (ΣI (𝓋 (suc zero)) (𝓋 zero))
                                          (weakenTermFrom zero (weakenTermFrom zero C)) ⋖ δg →
      Γ ⊢ p ∶ ΣF A B ⋖ δp →
      C[p] ≡ instantiateTerm zero p C →
    Γ ⊢ ΣE C g p ∶ C[p] ⋖ c (δA ∷ δB ∷ δC ∷ δg ∷ δp ∷ [])
  +F : ∀ {ℓ A B δA δB} →
    Γ ⊢ A ∶ 𝒰 ℓ ⋖ δA →
    Γ ⊢ B ∶ 𝒰 ℓ ⋖ δB →
    Γ ⊢ +F A B ∶ 𝒰 ℓ ⋖ c (δA ∷ δB ∷ [])
```

Note that in the HoTT book, `+IL` demands that both arguments to `+F` be well-formed types, but as an alternative to that, I see no problem with allowing `B` to be garbage: if asked whether it is true that (zero equals zero) or (colorless green ideas sleep furiously), it seems that one should be able to answer positively yes and give the proof of the former, rather than complain that one doesn't understand the latter half of the question.

(changing this back for the moment)

```agda
  +IL : ∀ ℓ {A B a δA δB δa} →
    Γ ⊢ A ∶ 𝒰 ℓ ⋖ δA →
    Γ ⊢ B ∶ 𝒰 ℓ ⋖ δB →
    Γ ⊢ a ∶ A ⋖ δa →
    Γ ⊢ +IL a ∶ +F A B ⋖ c (δA ∷ δB ∷ δa ∷ [])
  +IR : ∀ ℓ {A B b δA δB δb} →
    Γ ⊢ A ∶ 𝒰 ℓ ⋖ δA →
    Γ ⊢ B ∶ 𝒰 ℓ ⋖ δB →
    Γ ⊢ b ∶ B ⋖ δb →
    Γ ⊢ +IR b ∶ +F A B ⋖ c (δA ∷ δB ∷ δb ∷ [])
  +E : ∀ ℓ A B {N[a+b] N na nb a+b δA δB δN δna δnb δa+b} →
      (⊢A : Γ ⊢ A ∶ 𝒰 ℓ ⋖ δA) →
      (⊢B : Γ ⊢ B ∶ 𝒰 ℓ ⋖ δB) →
      Γ , +F ⊢A ⊢B ⊢ N ∶ 𝒰 ℓ ⋖ δN →
      Γ , ⊢A ⊢ na ∶ instantiateTerm (suc zero)
                                     (+IL (𝓋 zero))
                                     (weakenTermFrom zero N) ⋖ δna →
      Γ , ⊢B ⊢ nb ∶ instantiateTerm (suc zero)
                                     (+IR (𝓋 zero))
                                     (weakenTermFrom zero N) ⋖ δnb →
      Γ ⊢ a+b ∶ +F A B ⋖ δa+b →
      instantiateTerm zero a+b N ≡ N[a+b] →
    Γ ⊢ +E N na nb a+b ∶ N[a+b] ⋖ c (δA ∷ δB ∷ δN ∷ δna ∷ δnb ∷ δa+b ∷ [])
  𝟘F : ∀ {ℓ} →
    Γ ⊢ 𝟘F ∶ 𝒰 ℓ ⋖ c []
```

Similar to the above, unlike the HoTT book, I allow one to prove absolutely anything (that is scope-checked) given bottom. The philosophical justification, however is a little trickier, at least in my mind. For now, another reason I give is a practical one: I just don't care.

(changing back for now)

```agda
  𝟘E : ∀ ℓ {N[a] N a δN δa} →
    Γ , 𝟘F {ℓ = ℓ} ⊢ N ∶ 𝒰 ℓ ⋖ δN →
    Γ ⊢ a ∶ 𝟘F ⋖ δa →
    instantiateTerm zero a N ≡ N[a] →
    Γ ⊢ 𝟘E N a ∶ N[a] ⋖ c (δN ∷ δa ∷ [])
  𝟙F : ∀ {ℓ} →
    Γ ⊢ 𝟙F ∶ 𝒰 ℓ ⋖ c []
  𝟙I :
    Γ ⊢ 𝟙I ∶ 𝟙F ⋖ c []
```

Here, by eliminating the requirement that N be well-formed, I fear to be treading on thin-ice: might I be allowing the successor of true be a natural number? Note that in this and in the case of bottom, we are dealing with elimination rules. The introduction rule for + did not seem nearly so... upsetting.

(changing back for now)

```agda
  𝟙E : ∀ ℓ {N[a] N n1 a δN δn1 δa} →
    Γ , 𝟙F {ℓ = ℓ} ⊢ N ∶ 𝒰 ℓ ⋖ δN →
    Γ ⊢ n1 ∶ instantiateTerm zero 𝟙I N ⋖ δn1 →
    Γ ⊢ a ∶ 𝟙F ⋖ δa →
    instantiateTerm zero a N ≡ N[a] →
    Γ ⊢ 𝟙E N n1 a ∶ N[a] ⋖ c (δN ∷ δn1 ∷ δa ∷ [])
  ℕF : ∀ {ℓ} →
    Γ ⊢ ℕF ∶ 𝒰 ℓ ⋖ c []
  ℕIZ :
    Γ ⊢ ℕIZ ∶ ℕF ⋖ c []
  ℕIS : ∀ {n δn} →
    Γ ⊢ n ∶ ℕF ⋖ δn →
    Γ ⊢ ℕIS n ∶ ℕF ⋖ c (δn ∷ [])
```

```agda
  ℕE : ∀ ℓ {X[n] X x₀  xₛ n δX δx₀ δxₛ δn} →
    (⊢X : Γ , ℕF {ℓ = ℓ} ⊢ X ∶ 𝒰 ℓ ⋖ δX) →
    Γ ⊢ x₀ ∶ instantiateTerm zero ℕIZ X ⋖ δx₀ →
    Γ , ℕF {ℓ = ℓ} , ⊢X ⊢ xₛ ∶ weakenTermFrom zero
                                   (instantiateTerm (suc zero)
                                     (ℕIS (𝓋 zero))
                                     (weakenTermFrom zero X)) ⋖ δxₛ →
    Γ ⊢ n ∶ ℕF ⋖ δn →
    instantiateTerm zero n X ≡ X[n] →
    Γ ⊢ ℕE X x₀ xₛ n ∶ X[n] ⋖ c (δX ∷ δx₀ ∷ δxₛ ∷ δn ∷ [])
  =F : ∀ {ℓ A a b δA δa δb} →
    Γ ⊢ A ∶ 𝒰 ℓ ⋖ δA →
    Γ ⊢ a ∶ A ⋖ δa →
    Γ ⊢ b ∶ A ⋖ δb →
    Γ ⊢ =F A a b ∶ 𝒰 ℓ ⋖ c (δA ∷ δa ∷ δb ∷ [])
  =I : ∀ ℓ {A a δA δa} →
    Γ ⊢ A ∶ 𝒰 ℓ ⋖ δA →
    Γ ⊢ a ∶ A ⋖ δa →
    Γ ⊢ =I a ∶ =F A a a ⋖ c (δA ∷ δa ∷ [])
```

Here I am experimenting with

```agda
  =E : ∀ ℓ {X[a,b,p] X c' A a b p δC δc' δA δA' δa δb δp} →
      (⊢A : Γ ⊢ A ∶ 𝒰 ℓ ⋖ δA) →
      (⊢A' : Γ , ⊢A ⊢ weakenTermFrom zero A ∶ 𝒰 ℓ ⋖ δA') →
      (⊢p : Γ , ⊢A , ⊢A' ⊢ =F (weakenTermFrom zero (weakenTermFrom zero A))
                                ((𝓋 (suc zero)))
                                ((𝓋 zero))
                           ∶ 𝒰 ℓ
                           ⋖ δp) →
      (⊢C : Γ , ⊢A , ⊢A' , ⊢p ⊢ X ∶ 𝒰 ℓ ⋖ δC) →
      Γ , ⊢A ⊢ c' ∶ instantiateTerm (suc zero) (𝓋 zero)
                       (instantiateTerm (suc zero) (𝓋 zero)
                                      (instantiateTerm (suc zero) (=I (𝓋 zero))
                                        (weakenTermFrom zero X))) →
      Γ ⊢ a ∶ A →
      Γ ⊢ b ∶ A →
      Γ ⊢ p ∶ =F A a b →
      instantiateTerm zero a
        (instantiateTerm zero (weakenTermFrom zero b)
          (instantiateTerm zero
            (weakenTermFrom zero
              (weakenTermFrom zero p)) X)) ≡ X[a,b,p] →
      Γ ⊢ =E X c' a b p ∶ X[a,b,p] ⋖ c (δC ∷ δc' ∷ δa ∷ δb ∷ δp ∷ [])
```

The HoTT book has no name for this.

```agda
  ≡-type-substitution :
    ∀ {ℓ a δa A B δA≡B} →
    Γ ⊢ a ∶ A ⋖ δa →
    Γ ⊢ A ≝ B ∶ 𝒰 ℓ ⋖ δA≡B →
    Γ ⊢ a ∶ B ⋖ c (δa ∷ δA≡B ∷ [])
```

I was surprised to find this missing from the HoTT book. I do not see how to make use of computational equalities without it.

```agda
  ≡-term-substitution :
    ∀ {a δa b A δa≡b} →
    Γ ⊢ a ∶ A ⋖ δa →
    Γ ⊢ a ≝ b ∶ A ⋖ δa≡b →
    Γ ⊢ b ∶ A ⋖ c (δa ∷ δa≡b ∷ [])
```

```agda
data _⊢_≝_∶_⋖_ {N χ} (Γ : N ctx⋖ χ) where
  ≡-reflexivity :
    ∀ {a A δa} →
    Γ ⊢ a ∶ A ⋖ δa →
    Γ ⊢ a ≝ a ∶ A ⋖ c (δa ∷ [])
  ≡-symmetry :
    ∀ {A a b δa=b} →
    Γ ⊢ a ≝ b ∶ A ⋖ δa=b →
    Γ ⊢ b ≝ a ∶ A ⋖ c (δa=b ∷ [])
  ≡-transitivity :
    ∀ {A a b c' δa=b δb=c} →
    Γ ⊢ a ≝ b ∶ A ⋖ δa=b →
    Γ ⊢ b ≝ c' ∶ A ⋖ δb=c →
    Γ ⊢ a ≝ c' ∶ A ⋖ c (δa=b ∷ δb=c ∷ [])
  ≡-type-substitution :
    ∀ {ℓ a b A B δa=b δA=B} →
    Γ ⊢ a ≝ b ∶ A ⋖ δa=b →
    Γ ⊢ A ≝ B ∶ 𝒰 ℓ ⋖ δA=B →
    Γ ⊢ a ≝ b ∶ B ⋖ c (δa=b ∷ δA=B ∷ [])
  Π-uniq :
    ∀ f δf A B →
    Γ ⊢ f ∶ ΠF A B ⋖ δf →
    Γ ⊢ f ≝ ΠI (ΠE (weakenTermFrom zero f) (𝓋 zero)) ∶ ΠF A B ⋖ c (δf ∷ [])
```

The HoTT book takes `Π-intro-eq` to require `Γ , x:A ⊢ B : 𝒰ᵢ`. However, I conjecture that such a judgement would already have been made in order to conclude another of its requirements, `Γ , x:A ⊢ b ≡ b' : B`, so I leave it out.

On the other hand, the requirement `Γ ⊢ A : 𝒰ᵢ` is needed as part of the construction of another premise, so it stays.

```agda
  ΠI :
    ∀ ℓ {A δA B b b' δb=b'} →
    (⊢A : Γ ⊢ A ∶ 𝒰 ℓ ⋖ δA) →
    Γ , ⊢A ⊢ b ≝ b' ∶ B ⋖ δb=b' →
    Γ ⊢ ΠI b ≝ ΠI b' ∶ ΠF A B ⋖ c (δA ∷ δb=b' ∷ [])
  ΣI :
    ∀ {ℓ A δA B δB a a' δa=a' b b' δb=b'} →
    (⊢A : Γ ⊢ A ∶ 𝒰 ℓ ⋖ δA) →
    Γ , ⊢A ⊢ B ∶ 𝒰 ℓ ⋖ δB →
    Γ ⊢ a ≝ a' ∶ A ⋖ δa=a' →
    Γ ⊢ b ≝ b' ∶ instantiateTerm zero a B ⋖ δb=b' →
    Γ ⊢ ΣI a b ≝ ΣI a' b' ∶ ΣF A B ⋖ c (δA ∷ δB ∷ δa=a' ∷ δb=b' ∷ [])
  +IL :
    ∀ {A a a' δa=a' B} →
    Γ ⊢ a ≝ a' ∶ A ⋖ δa=a' →
    Γ ⊢ +IL a ≝ +IL a' ∶ +F A B ⋖ δa=a'
  +IR :
    ∀ {A B b b' δb=b'} →
    Γ ⊢ b ≝ b' ∶ B ⋖ δb=b' →
    Γ ⊢ +IR b ≝ +IR b' ∶ +F A B ⋖ δb=b'
  ℕIS :
    ∀ {n n' δn=n'} →
    Γ ⊢ n ≝ n' ∶ ℕF ⋖ δn=n' →
    Γ ⊢ ℕIS n ≝ ℕIS n' ∶ ℕF ⋖ δn=n'
```

This definitional equality is not obvious from Appendix 2.

```agda
  =I : ∀ {A a a' δa=a'} →
    Γ ⊢ a ≝ a' ∶ A ⋖ δa=a' →
    Γ ⊢ =I a ≝ =I a' ∶ =F A a a' ⋖ c (δa=a' ∷ [])
```

Computation rules:

```agda
  ΠE : ∀ {ℓ A δA B b δb a δa}
    (⊢A : Γ ⊢ A ∶ 𝒰 ℓ ⋖ δA) →
    Γ , ⊢A ⊢ b ∶ B ⋖ δb →
    Γ ⊢ a ∶ A ⋖ δa →
    Γ ⊢ ΠE (ΠI b) a ≝ instantiateTerm zero a b ∶ instantiateTerm zero a B ⋖ c (δA ∷ δb ∷ δa ∷ [])
  ΣE : ∀ {ℓ δΠAB A δA B δB C δC g δg a δa b δb} →
    (⊢ΠAB : Γ ⊢ ΠF A B ∶ 𝒰 ℓ ⋖ δΠAB) →
    Γ , ⊢ΠAB ⊢ C ∶ 𝒰 ℓ ⋖ δC →
    (⊢A : Γ ⊢ A ∶ 𝒰 ℓ ⋖ δA) →
    (⊢B : Γ , ⊢A ⊢ B ∶ 𝒰 ℓ ⋖ δB) →
    Γ , ⊢A , ⊢B ⊢ g ∶ instantiateTerm (suc (suc zero)) (ΣI (𝓋 (suc zero)) (𝓋 (suc zero))) (weakenTermFrom zero (weakenTermFrom zero C)) ⋖ δg →
    Γ ⊢ a ∶ A ⋖ δa →
    Γ ⊢ b ∶ instantiateTerm zero a B ⋖ δb →
    Γ ⊢ ΣE C g (ΣI a b) ≝ instantiateTerm zero a (instantiateTerm zero (weakenTermFrom zero b) g) ∶ instantiateTerm zero (ΣI a b) C ⋖ c (δΠAB ∷ δA ∷ δB ∷ δC ∷ δg ∷ δa ∷ δb ∷ [])
  +LE : ∀ {ℓ δ+FAB C δC A δA B δB c' δc' d δd a δa} →
    (⊢+FAB : Γ ⊢ +F A B ∶ 𝒰 ℓ ⋖ δ+FAB) →
    Γ , ⊢+FAB ⊢ C ∶ 𝒰 ℓ ⋖ δC →
    (⊢A : Γ ⊢ A ∶ 𝒰 ℓ ⋖ δA) →
    Γ , ⊢A ⊢ c' ∶ instantiateTerm (suc zero) (+IL (𝓋 zero)) (weakenTermFrom zero C) ⋖ δc' →
    (⊢B : Γ ⊢ B ∶ 𝒰 ℓ ⋖ δB) →
    Γ , ⊢B ⊢ d ∶ instantiateTerm (suc zero) (+IL (𝓋 zero)) (weakenTermFrom zero C) ⋖ δd →
    Γ ⊢ a ∶ A ⋖ δa →
    Γ ⊢ +E C c' d (+IL a) ≝ instantiateTerm zero a c' ∶ instantiateTerm zero (+IL a) C ⋖ c (δ+FAB ∷ δC ∷ δA ∷ δB ∷ δc' ∷ δd ∷ δa ∷ [])
```

Instead of something like the above, could simpler computation rules like these work?

```agda
  +RE : ∀ {b δb B C C[+IRb] c' d d[b]} →
    Γ ⊢ b ∶ B ⋖ δb →
    instantiateTerm zero (+IR b) C ≡ C[+IRb] →
    instantiateTerm zero b d ≡ d[b] →
    Γ ⊢ +E C c' d (+IR b) ≝ d[b] ∶ C[+IRb] ⋖ c (δb ∷ [])
  𝟙E : ∀ {C c' C[𝟙I]} →
    instantiateTerm zero 𝟙I C ≡ C[𝟙I] →
    Γ ⊢ 𝟙E C c' 𝟙I ≝ c' ∶ C[𝟙I] ⋖ c []
  ℕEZ : ∀ {n C c₀ cₛ C[ℕIZ] δn} →
    Γ ⊢ n ∶ ℕF ⋖ δn →
    instantiateTerm zero ℕIZ C ≡ C[ℕIZ] →
    Γ ⊢ ℕE C c₀ cₛ ℕIZ ≝ c₀ ∶ C[ℕIZ] ⋖ c (δn ∷ [])
  ℕES : ∀ {n C c₀ cₛ cₛ[n,ℕEn] C[ℕISn] δn} →
    Γ ⊢ n ∶ ℕF ⋖ δn →
    instantiateTerm zero n ((instantiateTerm zero (weakenTermFrom zero (Term.ℕE C c₀ cₛ n)) cₛ)) ≡ cₛ[n,ℕEn] →
    instantiateTerm zero (ℕIS n) C ≡ C[ℕISn] →
    Γ ⊢ ℕE C c₀ cₛ (ℕIS n) ≝ cₛ[n,ℕEn] ∶ C[ℕISn] ⋖ c (δn ∷ [])
  =E : ∀ {a c' c[a] C C[a,a,=Ia]} →
    instantiateTerm zero a c' ≡ c[a] →
    instantiateTerm zero a
      (instantiateTerm zero
        (weakenTermFrom zero a)
        ((instantiateTerm zero
          (weakenTermFrom zero
            (weakenTermFrom zero
              (=I a))) C))) ≡ C[a,a,=Ia] →
    Γ ⊢ =E C c' a a (=I a) ≝ c[a] ∶ C[a,a,=Ia] ⋖ c []
```

## validation

```agda
{- commented-out until I develop the API

consistent : ∀ ℓ → [] ⊢ 𝟘F ∶ 𝒰 ℓ × ¬ ([] ⊢ 𝟘F)
consistent = {!!}

{- an alternative definition?
consistent : ∃ λ bottom → ∃ λ ℓ → [] ⊢ bottom ∶ 𝒰 ℓ × ¬ ([] ⊢ bottom)
consistent = {!!}
-}

-- perhaps: show that "bottom is bad", i.e. that if we can infer it, then we can infer everything

-- type-checking is decidable
TC-decidable : ∀ {N χ} (Γ : N ctx⋖ χ) (a : Term N) (A : Term N) → Dec (Γ ⊢ a ∶ A)
TC-decidable = {!!}

-- type inference is semi-decidable
σ-decidable : ∀ {N δ} (Γ : N ctx⋖ δ) (A : Term N) (ℓ : Universe)
            → Γ ⊢ A ∶ 𝒰 ℓ
            → ∀ σ
            → Dec (Γ ⊢ A ≼ σ)
σ-decidable = {!!}
-}
```
