
# Wherein I go all-in for free variables!

```agda
module YAF8 where
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

  add-zero : ∀ n → n ≡ n +N 0
  add-zero zero = refl
  add-zero (suc n) = cong suc (add-zero n)
```

The plan is to identify what variables are free in the index of relevant datatypes.

```agda

open Preliminary

data Context : Nat → Set

_⊆_ : ∀ {N} → (_ _ : Fin N → Bool) → Set
f₁ ⊆ f₂ = ∀ i → f₁ i ≡ true → f₂ i ≡ true

_=̇_ : ∀ {N} → (_ _ : Fin N → Bool) → Set
f₁ =̇ f₂ = ∀ i → f₁ i ≡ f₂ i

mkFreeAt : ∀ {N} (f : Fin N) → Fin N → Bool
mkFreeAt zero zero = true
mkFreeAt zero (suc x) = false
mkFreeAt (suc f) zero = false
mkFreeAt (suc f) (suc x) = mkFreeAt f x

mkFreeNever : ∀ {N} → Fin N → Bool
mkFreeNever x = false

droplastFree : ∀ {N} → (Fin (suc N) → Bool) → Fin N → Bool
droplastFree f n = f (suc n)

_∪_ : ∀ {N} → (_ _ : Fin N → Bool) → Fin N → Bool
(f₁ ∪ f₂) x = f₁ x || f₂ x

-- (A : Type Γ f u) is equivalent to saying Γ ⊢ A : Uᵤ, where f are the free variables in A.
-- That is, we are saying that, given certain assumptions, we can construct a type that inhabits a particular universe, and that the type itself is constructed from some subset of those assumptions (viz, the free variables).
data Type {N : Nat} (Γ : Context N) : (Fin N → Bool) → Nat → Set

-- (t : Term Γ f u A f') is equivalent to saying Γ ⊢ t : A, where f are the free variables in A and f' are the free variables in t, and A : Uᵤ.
data Term {N : Nat} (Γ : Context N) : (f : Fin N → Bool) (u : Nat) → Type Γ f u → (Fin N → Bool) → Set

data Context where
  [] : Context zero
  _∷_ : ∀ {N} (Γ : Context N) (f : Fin N → Bool) (u : Nat) → Type Γ f u → Context (suc N)

-- contextPick : ∀ {N} (Γ' : Context N') → Fin N → ∃ λ Γ → ∃ λ f → ∃ λ u → Type Γ

data Type {N : Nat} (Γ : Context N) where
  {- I wonder if this is needed.
  -- variable is equivalent to saying Γ ⊢ v : Uᵤ, where v is some type listed in Γ. (is it mentioned?) It's not yet clear to me what the point of this would be.
  Okay, it's a little clearer. We will need this to construct things like
    Γ , x : N , y : N ⊢ x = y : U₀
  In this case, the x and y in the judgement refer to elements of the context.
  Umm, no.
  How about this?
    A : U , x : A , y : A ⊢ x = y : U₀
  In the =-form for the above Type, the Type for A : U ... well how do we call that? We don't have a rule for creating new types out of thin air, do we? I guess Appendix A.2 is not designed for that. So, that's not a good example.
  Consider a

  variable : (v : Fin N) (f : Fin N → Bool) → f =̇ mkFreeAt v → (u : Nat) → Type Γ f u
  -}
  -- universes inhabit higher universes
  𝒰-intro : (u : Nat) (f : Fin N → Bool) → f =̇ mkFreeNever → Type Γ f (suc u)
  -- universe inhabitation is cumulative
  𝒰-cumul : (u : Nat) (f : Fin N → Bool) → (A : Type Γ f u) → Type Γ f (suc u)
  -- NB I have a suspicion that 𝒰-cumul does not belong here. There is nothing to say that A is in the higher universe. Only that we may judge there to be an inhabitant of a higher universe. Maybe this is okay. We are saying that there is a type in a higher universe, and giving evidence of a type in a lower universe.

  -- dependent-function types
  Π-form : (u : Nat)
           (f : Fin N → Bool) (A : Type Γ f u)
           (f' : Fin (suc N) → Bool) (B : Type ((Γ ∷ f) u A) f' u)
           → Type Γ (droplastFree f' ∪ f) u
  -- the natural number type
  ℕ-form : (f : Fin N → Bool) → f =̇ mkFreeNever → Type Γ f zero -- we could specify a variable universe for this to live in, but we already have 𝒰-cumul for that
  -- Identity types
  =-form : (uA : Nat)
           (fA : Fin N → Bool)
           (A : Type Γ fA uA)
           (fa : Fin N → Bool)
           (a : Term Γ _ _ A fa)
           (fb : Fin N → Bool)
           (b : Term Γ _ _ A fb)
           → Type Γ (fA ∪ (fa ∪ fb)) uA

lift𝒰 : ∀ {N : Nat} (Γ : Context N) → (f : Fin N → Bool) → (u : Nat) → Type Γ f u → (u' : Nat) → u' ≥ u → Type Γ f u'
lift𝒰 Γ f u x .u (diff! zero) = x
lift𝒰 Γ f u x _ (diff! (suc k)) = 𝒰-cumul _ _ (lift𝒰 _ _ _ x _ (diff k refl))

-- substitute : {N : Nat} (Γ : Context N)

data Term {N : Nat} (Γ : Context N) where
  -- this is the same as the rule Vble from Appendix A.2.
  variable : {!!} → Term Γ {!!} {!!} {!!} {!!}
  Π-Intro : (uA : Nat) (fA : Fin N → Bool) (A : Type Γ fA uA)
            (uB : Nat) (fB : Fin (suc N) → Bool) (B : Type (_∷_ Γ _ _ A) fB uB)
            → Term Γ (droplastFree fB) {!(max uA uB)!} (Π-form {!!} {!!} A {!!} {!B!}) {!!}
  ℕ-Intro₁ : (f : Fin N → Bool) (eq : f =̇ mkFreeNever)
             (f' : Fin N → Bool) (eq' : f' =̇ mkFreeNever) →
             Term Γ f zero (ℕ-form f eq) f'
  ℕ-Intro₂ : (f : Fin N → Bool) (eq : f =̇ mkFreeNever)
             (f' : Fin N → Bool) (eq' : f' =̇ mkFreeNever)
             (u : Nat)
             (n : Type Γ f u)
             → n ≡ (lift𝒰 _ _ _ (ℕ-form f eq) u (diff u (add-zero (suc u))))
             → Term Γ f u n f'
             → Term Γ f u n f'
  ℕ-Elim : (uC : Nat) (fC : Fin (suc N) → Bool)
           (C : Type (_∷_ Γ _ uC (lift𝒰 Γ _ _ (ℕ-form mkFreeNever λ i → refl) _ (diff uC (add-zero _)))) fC uC)
           (C[0/x] : Type Γ (droplastFree fC) uC)
           -- now we want to say that C[0/x] is the same as C, except wherever we see reference to a Term that is a variable referring to the first element of the context, we should replace that with an ℕ-Intro₁ and *that* whole thing will be equivalent to C[0/x].
           → Term Γ {!!} {!!} {!!} {!!}

```

Okay, I think what I've learned is that carrying around the "meta"-information (about free variables) in the datatype, when such a thing is calculable from the structure itself is not helpful... why? When is such information ever helpful, I wonder? Consider the difference between Nat and Fin. Could we not define Fin as a Nat that is less than a certain number? Let's try.

```agda
Fine : Nat → Set
Fine n = Σ Nat λ m → m < n

test-fine2 : Fine 2
test-fine2 = suc zero , diff 0 refl

test-fine0 : Fine 0 → ⊥
test-fine0 (fst₁ , diff k ())
```

So it looks like the difference is that with Fin, we don't have to carry around proofs.

I am going to try once again with a more normal-sounding approach. (who me?)
