
```agda
module Type.Term.Layer-1.SCTerm where

open import Type.Prelude
open import Type.Universe
open import Type.Term.Layer-2.DeBruijn
```

## scope-checked terms

```agda
data Term (N : Nat) : Set where
  𝒰 : Universe → Term N
  𝓋 : Fin N → Term N
  ΠF : Term N → Term (suc N) → Term N
  ΠI : Term (suc N) → Term N
  ΠE : Term N → Term N → Term N
  ΣF : Term N → Term (suc N) → Term N
  ΣI : Term N → Term N → Term N
  ΣE : Term (suc N) → Term (suc (suc N)) → Term N → Term N
  +F : Term N → Term N → Term N
  +IL : Term N → Term N
  +IR : Term N → Term N
  +E : Term (suc N) → Term (suc N) → Term (suc N) → Term N → Term N
  𝟘F : Term N
  𝟘E : Term (suc N) → Term N → Term N
  𝟙F : Term N
  𝟙I : Term N
  𝟙E : Term (suc N) → Term N → Term N → Term N
  ℕF : Term N
  ℕIZ : Term N
  ℕIS : Term N → Term N
  ℕE : Term (suc N) → Term N → Term (suc (suc N)) → Term N → Term N
  =F : Term N → Term N → Term N → Term N
  =I : Term N → Term N
  =E : Term (suc (suc (suc N))) → Term (suc N) → Term N → Term N → Term N → Term N
```

Some definitions for scope-checked terms.

```agda
module DefinedFunctions where
  𝟎 𝟏 𝟐 𝟑 𝟒 : ∀ {N} → Term N
  𝟎 = ℕIZ
  𝟏 = ℕIS 𝟎
  𝟐 = ℕIS 𝟏
  𝟑 = ℕIS 𝟐
  𝟒 = ℕIS 𝟑

  -- add x represents a function that adds x to a given input
  add : ∀ {N} → Term N → Term N
  add x = ℕE (ΠF ℕF ℕF) -- form a function f : ℕ → ℕ
             -- case x = ℕIZ
             -- λ y → y
             (ΠI (𝓋 zero))
             -- case x = ℕIS x₋₁
             -- λ x₋₁ f →
                -- λ y → suc (f y)
                (ΠI (ℕIS (ΠE (𝓋 (suc zero)) (𝓋 zero))))
             x

  _+ℕ_ : ∀ {N} → Term N → Term N → Term N
  x +ℕ y = ΠE (add x) y

  double : ∀ {N} → Term N → Term N
  double x = ΠE (ΠI (add (𝓋 zero))) x

  multiply : ∀ {N} → Term N → Term N
  multiply x = ℕE (ΠF ℕF ℕF)
                  (ΠI ℕIZ)
                  (ΠI let x₋₁ = 𝓋 (suc (suc zero)) ; f = 𝓋 (suc zero) ; y = 𝓋 zero in
                      y +ℕ (ΠE f x₋₁))
                  x

  _*ℕ_ : ∀ {N} → Term N → Term N → Term N
  x *ℕ y = ΠE (multiply x) y

  _=ℕ_ : ∀ {N} → Term N → Term N → Term N
  x =ℕ y = =F ℕF x y
```

```agda
weakenTermFrom : ∀ {N} → Fin (suc N) → Term N → Term (suc N)
weakenTermFrom from (𝒰 ℓ) =
                     𝒰 ℓ
weakenTermFrom from (𝓋 v) =
                     𝓋 (weakenFinFrom from v)
weakenTermFrom from (ΠF t₁ t₂) =
                     ΠF (weakenTermFrom from t₁)
                        (weakenTermFrom (suc from) t₂)
weakenTermFrom from (ΠI t₁) =
                     ΠI (weakenTermFrom (suc from) t₁)
weakenTermFrom from (ΠE t₁ t₂) =
                     ΠE (weakenTermFrom from t₁)
                        (weakenTermFrom from t₂)
weakenTermFrom from (ΣF t₁ t₂) =
                     ΣF (weakenTermFrom from t₁)
                        (weakenTermFrom (suc from) t₂)
weakenTermFrom from (ΣI t₁ t₂) =
                     ΣI (weakenTermFrom from t₁)
                        (weakenTermFrom from t₂)
weakenTermFrom from (ΣE t₁ t₂ t₃) =
                     ΣE (weakenTermFrom (suc from) t₁)
                        (weakenTermFrom (suc (suc from)) t₂)
                        (weakenTermFrom from t₃)
weakenTermFrom from (+F t₁ t₂) =
                     +F (weakenTermFrom from t₁)
                        (weakenTermFrom from t₂)
weakenTermFrom from (+IL t₁) =
                     +IL (weakenTermFrom from t₁)
weakenTermFrom from (+IR t₁) =
                     +IR (weakenTermFrom from t₁)
weakenTermFrom from (+E t₁ t₂ t₃ t₄) =
                     +E (weakenTermFrom (suc from) t₁)
                        (weakenTermFrom (suc from) t₂)
                        (weakenTermFrom (suc from) t₃)
                        (weakenTermFrom from t₄)
weakenTermFrom from 𝟘F =
                    𝟘F
weakenTermFrom from (𝟘E t₁ t₂) =
                     𝟘E (weakenTermFrom (suc from) t₁)
                        (weakenTermFrom from t₂)
weakenTermFrom from 𝟙F =
                    𝟙F
weakenTermFrom from 𝟙I =
                    𝟙I
weakenTermFrom from (𝟙E t₁ t₂ t₃) =
                     𝟙E (weakenTermFrom (suc from) t₁)
                        (weakenTermFrom from t₂)
                        (weakenTermFrom from t₃)
weakenTermFrom from ℕF =
                    ℕF
weakenTermFrom from ℕIZ =
                    ℕIZ
weakenTermFrom from (ℕIS t₁) =
                     ℕIS (weakenTermFrom from t₁)
weakenTermFrom from (ℕE t₁ t₂ t₃ t₄) =
                     ℕE (weakenTermFrom (suc from) t₁)
                        (weakenTermFrom from t₂)
                        (weakenTermFrom (suc (suc from)) t₃)
                        (weakenTermFrom from t₄)
weakenTermFrom from (=F t₁ t₂ t₃) =
                     =F (weakenTermFrom from t₁)
                        (weakenTermFrom from t₂)
                        (weakenTermFrom from t₃)
weakenTermFrom from (=I t₁) =
                     =I (weakenTermFrom from t₁)
weakenTermFrom from (=E t₁ t₂ t₃ t₄ t₅) =
                     =E (weakenTermFrom (suc (suc (suc from))) t₁)
                        (weakenTermFrom (suc from) t₂)
                        (weakenTermFrom from t₃)
                        (weakenTermFrom from t₄)
                        (weakenTermFrom from t₅)
```

`instantiateTerm` functions as a simple form of substitution. Given a term ρ in a context(*) of N elements, γ₀ , γ₁ , ... γ_N-1, and a term τ in the same context except for an additional element inserted before the element γₙ, for some 0 ≤ n ≤ N-1, `instantiateTerm {N} n ρ τ` yields τ[ρ/γₙ], a term in the same context as ρ where every referent to γₙ in τ has been replaced by ρ.

[*] It is a bit loose to say that these scope-checked terms are "in a context" because there is nothing about `Term.𝓋 : Fin N → Term N` that demands that its argument denote an element of a context.

```agda
instantiateTerm : ∀ {N} → Fin (suc N) → Term N → Term (suc N) → Term N
instantiateTerm at ρ (𝒰 ℓ) =
                      𝒰 ℓ
instantiateTerm at ρ (𝓋 v) with at == v
… | yes _ = ρ
… | no at≠v = 𝓋 (instantiateFinAt at≠v)
instantiateTerm at ρ (ΠF t₁ t₂) =
                      ΠF (instantiateTerm at ρ t₁)
                         (instantiateTerm (suc at) (weakenTermFrom zero ρ) t₂)
instantiateTerm at ρ (ΠI t₁) =
                      ΠI (instantiateTerm (suc at) (weakenTermFrom zero ρ) t₁)
instantiateTerm at ρ (ΠE t₁ t₂) =
                      ΠE (instantiateTerm at ρ t₁)
                         (instantiateTerm at ρ t₂)
instantiateTerm at ρ (ΣF t₁ t₂) =
                      ΣF (instantiateTerm at ρ t₁)
                         (instantiateTerm (suc at) (weakenTermFrom zero ρ) t₂)
instantiateTerm at ρ (ΣI t₁ t₂) =
                      ΣI (instantiateTerm at ρ t₁)
                         (instantiateTerm at ρ t₂)
instantiateTerm at ρ (ΣE t₁ t₂ t₃) =
                      ΣE (instantiateTerm (suc at) (weakenTermFrom zero ρ) t₁)
                         (instantiateTerm (suc (suc at)) (weakenTermFrom zero (weakenTermFrom zero ρ)) t₂)
                         (instantiateTerm at ρ t₃)
instantiateTerm at ρ (+F t₁ t₂) =
                      +F (instantiateTerm at ρ t₁)
                         (instantiateTerm at ρ t₂)
instantiateTerm at ρ (+IL t₁) =
                      +IL (instantiateTerm at ρ t₁)
instantiateTerm at ρ (+IR t₁) =
                      +IR (instantiateTerm at ρ t₁)
instantiateTerm at ρ (+E t₁ t₂ t₃ t₄) =
                      +E (instantiateTerm (suc at) (weakenTermFrom zero ρ) t₁)
                         (instantiateTerm (suc at) (weakenTermFrom zero ρ) t₂)
                         (instantiateTerm (suc at) (weakenTermFrom zero ρ) t₃)
                         (instantiateTerm at ρ t₄)
instantiateTerm at ρ 𝟘F =
                     𝟘F
instantiateTerm at ρ (𝟘E t₁ t₂) =
                      𝟘E (instantiateTerm (suc at) (weakenTermFrom zero ρ) t₁)
                         (instantiateTerm at ρ t₂)
instantiateTerm at ρ 𝟙F =
                     𝟙F
instantiateTerm at ρ 𝟙I =
                     𝟙I
instantiateTerm at ρ (𝟙E t₁ t₂ t₃) =
                      𝟙E (instantiateTerm (suc at) (weakenTermFrom zero ρ) t₁)
                         (instantiateTerm at ρ t₂)
                         (instantiateTerm at ρ t₃)
instantiateTerm at ρ ℕF =
                     ℕF
instantiateTerm at ρ ℕIZ =
                     ℕIZ
instantiateTerm at ρ (ℕIS t₁) =
                      ℕIS (instantiateTerm at ρ t₁)
instantiateTerm at ρ (ℕE t₁ t₂ t₃ t₄) =
                      ℕE (instantiateTerm (suc at) (weakenTermFrom zero ρ) t₁)
                         (instantiateTerm at ρ t₂)
                         (instantiateTerm (suc (suc at)) (weakenTermFrom zero (weakenTermFrom zero ρ)) t₃)
                         (instantiateTerm at ρ t₄)
instantiateTerm at ρ (=F t₁ t₂ t₃) =
                      =F (instantiateTerm at ρ t₁)
                         (instantiateTerm at ρ t₂)
                         (instantiateTerm at ρ t₃)
instantiateTerm at ρ (=I t₁) =
                      =I (instantiateTerm at ρ t₁)
instantiateTerm at ρ (=E t₁ t₂ t₃ t₄ t₅) =
                      =E (instantiateTerm (suc (suc (suc at))) (weakenTermFrom zero (weakenTermFrom zero (weakenTermFrom zero ρ))) t₁)
                         (instantiateTerm (suc at) (weakenTermFrom zero ρ) t₂)
                         (instantiateTerm at ρ t₃)
                         (instantiateTerm at ρ t₄)
                         (instantiateTerm at ρ t₅)
```

## Fundamental Theorem

It seems of fundamental importance, similar to the Fundamental Theorem of Calculus, to have a correspondence between weakening and substitution. In particular, there is a certain way in which `weakenTermFrom` and `instantiateTerm` are inverses of one another.

Just how to say this? Instantiating a term with anything at all at a position p that has been weakened at that same position should result in the same term prior to instantiation or weakening.

Can I say something stronger? There is the swapping of variables. Swapping variables and then swapping back again also results in the same term. How do we swap variables with the above machinery? Suppose the term contains slots for variables p and q (thus N ≤ suc (max p q)). To be definite, let's say p = 3 and q = 7.

0 1 2 p=3 4 5 6 q=7 8

weaken from 3, imagining we are creating a slot for the new q

0 1 2 *=3 p=4 5 6 7 q=8 9

instantiate at 8 with 𝓋 3, now resulting in renaming all references to q with references to q'

0 1 2 q=3 p=4 5 6 7 8

weaken from 7, imagining we are creating a slot for the new p

0 1 2 q=3 p=4 5 6 *=7 8 9

instantiate at 4 with 𝓋 7

0 1 2 q=3 4 5 6 p=7 8

That process swapped p with q. Repeat this process and we end up where we started.

But the identities don't end there, because we can swap p with q, q with r, p with q, and then r with p, resulting in something like

p q r -0/1-> q p r -0/2-> r p q -1/2-> r q p -0/2-> p q r

On the other hand, there are also ways to instantiate in a term so that no amount of weakening or instantiating will ever return it to its original state. For example, if the term is 𝓋 0, and we instantiate 0 with 𝒰 0, there is no going back. Instantiating with any non-variable at position p in a term that refers to p results in a no-go-back situation because, in that case, the number of non-variable subterms grows, and neither weakening nor instantiation can ever reduce that number.

Another way to get to a no-go-back situation is to instantiating a variable q at position p in a term that refers to both q and p. This "muddies the water" now providing no way to tell which places originally referred to p and which referred to q. The action reduces the number of used variables without reducing the number of non-variable subterms and results in a no-go-back because weakening never changes the number of used variables or non-variable subterms and instantiation never increases the number of used variables without increasing the number of non-variable subterms.

## Complex Substitutions

```agda
applyTerm : ∀ {N} → Term (suc N) → Term N → Term N
applyTerm f x = instantiateTerm zero x f

weakenTermByFrom : ∀ {N} → (M : Nat) → Fin (suc N) → Term N → Term (M + N)
weakenTermByFrom zero from τ = τ
weakenTermByFrom (suc by) from τ = transport Term auto $ weakenTermByFrom by (weakenFinFrom zero from) (weakenTermFrom from τ)

substituteTerm : ∀ {M N} → Term (suc (M + N)) → Term N → Term (M + N)
substituteTerm {M} {N} f x = applyTerm f $ weakenTermByFrom M zero x
```