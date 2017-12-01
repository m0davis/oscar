
#

```agda
module Type.Common where
```

```agda
open import Prelude
open import Tactic.Nat
```

## some conveniences that are here, inconveniently

```agda
∃_ : ∀ {a b} {A : Set a} (B : A → Set b) → Set (a ⊔ b)
∃_ = Σ _
```

```agda
_≢_ : ∀ {ℓ} {A : Set ℓ} → A → A → Set ℓ
a ≢ b = ¬ (a ≡ b)
```

## some necessities that are unnecessarily here

I use DeBruijn indexing to describe parts of a context. A context has a size represented by a natural number. A DeBruijn index on a context of some size N is a number between 0 and N-1, and is meant to represent a signifier of one of the contextual elements. We will sometimes want to talk about a context expanded by the insertion of some element. When we do so, we will also want to carry along an index that points to the same element in the expanded context as it was prior to expansion. In a context of size N there are N + 1 places at which to insert a new element. I say that an index i in a context Γ of size N is weakened from a place f yielding an index i'. That is, `weakenFinFrom {N} p i = i'`.

```agda
weakenFinFrom : ∀ {N} → Fin (suc N) → Fin N → Fin (suc N)
weakenFinFrom zero x = suc x
weakenFinFrom (suc from) zero = zero
weakenFinFrom (suc from) (suc x) = suc (weakenFinFrom from x)
```

Similarly, we may also want to talk about contractions of a context. Or we may want to talk about pidgeons. You are a pigeon. There are some pigeon holes labeled 0,1,...,N. You are given a particular pigeon hole, i. One of the holes that you are not given, labeled h, is removed, and the pigeon holes are relabeled 0,1,...,N-1. What is the new label on your pigeon hole?

```agda
instantiateFinAt : ∀ {N} {h i : Fin (suc N)} → h ≢ i → Fin N
instantiateFinAt {zero} {zero} {zero} h≢i = ⊥-elim (h≢i refl)
instantiateFinAt {zero} {zero} {suc ()} _
instantiateFinAt {zero} {suc ()} {_} _
instantiateFinAt {suc _} {_} {zero} _ = zero -- my label stays at 0
instantiateFinAt {suc _} {zero} {suc i} _ = i -- my label shifts down
instantiateFinAt {suc _} {suc h} {suc i} sh≢si =
  let h≢i : h ≢ i -- the hole lower than mine is not the same as the hole lower than the one removed
      h≢i = λ {refl → sh≢si refl}
  in
  suc (instantiateFinAt h≢i) -- my label is one more then the one lower than me after the change
```

# Specification of Type Theory (from the HoTT book, mostly)

This is inspired mainly from Appendix A.2, though I have taken a liberty or two.

The postulated multiverse.

```agda
Universe = Nat
```

We may also view `Complexity` as the shape of a proof.

```agda
data Complexity : Set where
  c : ∀ {N} → Vec Complexity N → Complexity
```

These are measures of the size of the shape of a proof. they are not to be confused with how long it takes to prove something. although they could be if a given proof system searches monotonically over sizes.

```agda
χ-measure : Complexity → Nat
δ-measure : ∀ {N} → Vec Complexity N → Nat

χ-measure (c {N} δ) = δ-measure δ

δ-measure {.0} [] = zero
δ-measure {.(suc _)} (χ ∷ δ) = suc (χ-measure χ + δ-measure δ)
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
