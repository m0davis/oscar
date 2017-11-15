
# Wherein I really am building the architecture for a type theory proof system

```agda
module YAF6 where
```

## Some preliminaries that could be put elsewhere.

```agda
module Preliminary where

  open import Prelude public

  ∃_ : ∀ {a b} {A : Set a} (B : A → Set b) → Set (a ⊔ b)
  ∃_ = Σ _

  data IsYes {a} {P : Set a} : Dec P → Set a where
    yes : (p : P) → IsYes (yes p)

  getProof : ∀ {a} {P : Set a} → {d : Dec P} → IsYes d → P
  getProof (yes p) = p
```

I was hoping that, by using DeBruijn indexes to locate variables, I would be relieved of defining α-equivalence. However, there comes a problem when, for example, using a type C, given by the judgement `Γ , x : ℕ ⊢ C : 𝒰ᵢ`, in another judgement with a different context, `Γ , x : ℕ , y : C ⊢ cₛ : C[succ x / x]`. In the latter judgement, the type to which the term is adjudicated resides in an expanded context.

Using variables isn't as easy as it looks. When doing a simultaneous substitution of, say, succ x for x, x occurs in the result, so we cannot strengthen the context to remove x. We can only strengthen the context `Γ , x , Δ` to `Γ , Δ` if x does not occur in Δ and does not occur in the adjudication clause.

Can simultaneous substitution be reduced to singular substitution? Consider `σ[ succ y , succ x / x , y ]`, where `σ ≡ x < y`. The result should be succ y < succ x. If we tried doing this one at a time, we might substitute x first, obtaining `succ y < y`, then substituting y, obtaining `succ (succ x) < succ x`.

How about another approach, where we create new variables while doing substitution? The idea is:

x : N , y : N ⊢ (x < y)[succ y , succ x / x , y] : U
x : N , y : N , x' : N , y' : N ⊢ (x < y)[x' / x][y' / y][succ y / x'][succ x / y'] : U
x : N , y : N , x' : N , y' : N ⊢ (x' < y)[y' / y][succ y / x'][succ x / y'] : U
x : N , y : N , x' : N , y' : N ⊢ (x' < y')[succ y / x'][succ x / y'] : U
x : N , y : N , x' : N , y' : N ⊢ (succ y < y')[succ x / y'] : U
x : N , y : N , x' : N , y' : N ⊢ succ y < succ x : U

...and then remove x' and y'. Unfortunately, this idea still does not handle a case where, by substituting, we want to remove one of the substituted variables:

x : N , y : N ⊢ (x < y)[succ y / x] : U
y : N ⊢ succ y < y : U

So, it occurs to me that we need an occurs check. Or maybe have the occurrence of variables in a type or term be part of its index. Or maybe the easiest way to go is to come up with a notion of equivalence between terms or types in different contexts. Then, when we specify a rule, such as ℕ-Elim, we ask that, given a type `C` in context `Γ , x : N`, there is an equivalent type `C'` in context `Γ , x : N , y : C`, the substitution C[succ x / x]

Yet another approach is to define a singular substitution rule, use Subst₁ and Wkg₁ from Appendix A.2. Particular uses of simultaneous substitution will be defined as a combination of the above rules. For example,

Γ , x : N ⊢ C : U

We want to derive the type Γ , x : N ⊢ Cₛ : U, where Cₛ ≡ C[succ x / x] : U. We use Subst₂ to do this? We then use the derived type in the rule.

How about simultaneous substitution? We can do it step-wise: For σ[y , x / x , y], say we want:

x : N , y : N ⊢ (x < y)[y , x / x , y] : U

We write this (we think, equivalently) as

x : N , y : N , x' : N , y' : N ⊢ (x < y)[x' / x][y' / y][y , x / x , y] : U

...ugh, there will be problems when the types of the simultaneously-substituted variables depend on each other.

Now I'm thinking that substitution needs to be ignorant of the types, and just know what free variables are there.

I'm going to try again in another YAF7. The below is my scribbles of my last attempt.

```agda
```

This all reminds me of the `Thinkandthin` class I created in inspiration from Conor McBride's work. I will bring that back presently.

```agda
module Thickandthin where


```

```agda
module TypeTheory where
  open Preliminary

{-
  {- Each constructor for each of the datatypes below represents a rule of the type theory -}

  -- contexts
  data Ctx : Nat → Set

  -- type formation
  data Type : ∀ {N : Nat} (Γ : Ctx N) (universe : Nat) → Set

  -- judgements about terms inhabiting types
  data Term : ∀ {N : Nat} {Γ : Ctx N} {universe : Nat} → Type Γ universe → Set

  -- judgements about definitional equality
  data Equal : ∀ {N : Nat} {Γ : Ctx N} {universe : Nat} {type : Type Γ universe} →
                 Term type → Term type → Set

  {- We will need a way of substituting and weakening -}
  substituteTerm : {N : Nat} {Γ : Ctx N} {universe : Nat} {type : Type Γ universe}
                   → Term type → (v : Variables Γ) → Substitutions v
                   → Term type

  {- also a way of strengthening -}
  strengthenTerm : {N : Nat} {Γ : Ctx N} {universe : Nat} {type : Type Γ universe}
                   → Term type → (v : Variables Γ) -- the unnecessary that we now lose (and get stronger)
                   → ?

  -- but then we need to be able to say (sometimes) that if we do a certain substitution, we can strengthen a term. We need to track the variables that are free in a term or type (as opposed to what variables from the context do not appear. Otherwise, we need to somehow enforce that a term or type always uses all of the variables from its context, but this seems odd: we might want to draw a conclusion from, say, a = b, but not use the fact of the proof in the statement of the type (but we would of course want to use it in the proof.) Alternatively, we might use a contextual variable in the type but not in the term.

  So we want something like

  data



  Π-elim : (N : Nat) (Γ : Ctx N) (universe : Nat)
           (A : Type Γ universe) (B : Type (Γ ∷ A) universe)
           (f : Term (Π A B))
           (a : Term A)
           → Σ (Term (substitute₁ B a)) λ t →

  substitution

  record Statement : Set
    field
      {N} : Nat
      {Γ} : Ctx N
      {universe} : Nat
      type : Type Γ universe

  FormationRule : List TypingJudgement → TypingJudgement

  data _⊢_ : List Statement → Statement
  data Proof

  foo : Set₁
  foo = Σ Set λ x → x → Set
-}
{-
  data Choose : (N : Nat) → Fin (suc N) → Set where

  data VecChoose (A : Set) : (N : Nat) → Fin (suc N) → Set where

  data Context : Nat → Set
  data Type : {N : Nat} (Γ : Context N) → Set
  data Term : {N : Nat} (Γ : Context N) → Type Γ → Set
  -- data _⊢_∶_ {N : Nat} (Γ : Context N) : Term Γ → Type Γ → Set

  data Context where
    [] : Context zero
    _<∷_ : ∀ {N} → (Γ : Context N) → Type Γ → Context (suc N)



  data Type where
    variable : {N : Nat} (Γ : Context N) → Fin N → Type Γ
    universe : {N : Nat} (Γ : Context N) → Nat → Type Γ
    Π-former : {N : Nat} (Γ : Context N) → {t : Type Γ} → Type (Γ <∷ t) → Type Γ
    Σ-former : {N : Nat} (Γ : Context N) → {t : Type Γ} → Type (Γ <∷ t) → Type Γ
    +-former : {N : Nat} (Γ : Context N) → Type Γ → Type Γ → Type Γ
    =-former : {N : Nat} (Γ : Context N) → {t : Type Γ} → Term Γ t → Term Γ t → Type Γ
    0-former : {N : Nat} (Γ : Context N) → Type Γ
    ℕ-former : {N : Nat} (Γ : Context N) → Type Γ
    substitution : {N : Nat} (Γ : Context N) → {A : Type Γ} (B : Type (Γ <∷ A)) → Term Γ A → Type (Γ <∷ A)
    -- substitution' : {N : Nat} (Γ : Context (suc N)) → ∀ {m : Fin (suc N)} → Vec () m → Choose N m → Type Γ
    -- weakening : (A : Type Γ) (B : Type (Γ <∷ A)) → Type (Γ <∷ A)

  data Term where
    variable : {N : Nat} (Γ : Context N) → (n : Fin N) → (t : Type Γ) → Term Γ t
    application : {N : Nat} (Γ : Context N) → ∀ {A B} → (f : Term Γ (Π-former Γ B)) → (a : Term Γ A) → Term Γ {!(substitution Γ B a)!}
    Π-intro : {N : Nat} (Γ : Context N) → ∀ {A B} → Term (Γ <∷ A) B → Term Γ (Π-former Γ B)
    zero : {N : Nat} (Γ : Context N) → Term Γ (ℕ-former Γ)
    succ : {N : Nat} (Γ : Context N) → Term Γ (ℕ-former _) → Term Γ (ℕ-former _)
    ind0 : {N : Nat} (Γ : Context N) → (C : Type (Γ <∷ (0-former _)))
           (a : Term Γ (0-former _))
           → Term Γ {!substitution Γ C a!}
    indℕ : {N : Nat} (Γ : Context N) → (C : Type (Γ <∷ ℕ-former Γ))
           (c₀ : Term Γ {!substitution _ C (zero _)!})
           (cₛ : Term ((Γ <∷ (ℕ-former _)) <∷ C) {!substitution C ?!})
           -- (substitution C (succ (variable ?)))
           (n : Term Γ (ℕ-former _))
           → Term Γ {!substitution _ C n!}
    substitution : {N : Nat} (Γ : Context N) → {A : Type Γ} (B : Type (Γ <∷ A)) → Term Γ A → Term Γ A

  data Equation

  data Computation : ∀ {N : Nat} {Γ : Context N} (t : Type Γ) → Term Γ t → Term Γ t → Set where
    Π-comp : ∀ {N : Nat} {Γ : Context N} (A : Type Γ) (B : Type (Γ <∷ A)) (b : Term (Γ <∷ A) B) (a : Term Γ A) →
               Computation {!substitution _ B a!} {!application _ (Π-intro _ b) a!} {!Term.substitution B!}

  data Derivation : ∀ {N : Nat} {Γ : Context N} {t : Type Γ} → Term Γ t → Set where

    -- universe0 : {N : Nat} {Γ : Context N} → Derivation (universe 0)
-}


    {-
    variable : Fin N → Term Γ
    application : Term Γ → Term Γ → Term Γ
    Π-constructor : (t : Type Γ) → Term (Γ <∷ t) → Term Γ
    Σ-construtor : Term Γ → Term Γ → Term Γ
    -}
    -- Σ-induction :

{-
  data _⊢_∶_ {N : Nat} (Γ : Context N) where
    Γ ⊢ universe u ∶ universe (suc u)
    Γ ⊢ universe u ∶ universe (suc u)
    application : (t : Type Γ) → Term (Γ <∷ t) → Γ ⊢ (application
-}
{-
  [] ctx
  nat , [] ctx
  nat , nat , [] ctx
  eq nat (var 0) (var 1) , nat , nat , [] ctx

  zero ∶ nat
  suc zero ∶ nat

  universe zero ∶ universe (suc zero)

  [] ⊩ zero level

  l , Γ / J level l , J ctx Γ , [] ⊩ J sort (universe l)
  s / J sort s ⊩ J type s
  l , Γ / J level l , J ctx Γ , [] ⊩ J deptype Γ (universe l) (universe (lsuc l))
  t , Γ / J deptype Γ t s , J deptype (Γ ,
  universe l , [] ⊩
  Γ ⊢ ⊩
-}

  {-
    sigma : Type Γ → Type (suc Γ) → Type Γ
    coproduct : Type Γ → Type Γ → Type Γ
    -- empty : Type Γ
    -- unit : Type Γ
    natural : Type Γ
    identity : (t : Type Γ) → Type Γ
  -}

    {-
  data Term (Γ : Nat) : Set where
    var : Fin Γ → Term Γ
    application : Term Γ → Term Γ → Term Γ
    pi-constructor : Term (suc Γ) → Term Γ
    -}

  -- data _⊢_∶_ : {N : Nat} → (Γ : Context N) → Term Γ → Type Γ → Set where



```
