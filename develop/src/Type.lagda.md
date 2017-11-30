
# Type theory, metaprogrammed (eventually)

```agda
module Type where
```

I develop a partial (or maybe a full) implementation of a particular type theory and then turn back to re-develop it as an instance of a general (metaprogrammed) type theory.

```agda
open import Prelude
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

# Specification of Type Theory (from the HoTT book)

This based on that from Appendices A.1 and A.2, not including W-types.

The postulated multiverse.

```agda
Universe = Nat
```

We may also view `Complexity` as the shape of a proof.

```agda
data Complexity : Set where
  c : ∀ {N} → Vec Complexity N → Complexity
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

## type-checked terms

```
data _ctx⋖_ : Nat → Complexity → Set

-- Γ ⊢ a : A ⋖ χ = a proves A given Γ, with complexity χ
data _⊢_∶_⋖_ {N χ} (Γ : N ctx⋖ χ) : Term N → Term N → Complexity → Set


data _⊢_≝_∶_⋖_ {N χ} (Γ : N ctx⋖ χ) : Term N → Term N → Term N → Complexity → Set

-- Γ ⊢ a : A = a is a proof of A given Γ
_⊢_∶_ : ∀ {N χ} (Γ : N ctx⋖ χ) → Term N → Term N → Set
Γ ⊢ a ∶ A = ∃ (Γ ⊢ a ∶ A ⋖_)

-- Γ ⊢ A = there is a proof of A given Γ
_⊢_ : ∀ {N χ} (Γ : N ctx⋖ χ) → Term N → Set
Γ ⊢ A = ∃ (Γ ⊢_∶ A)

-- these are measures of the size of the shape of a proof. they are not to be confused with how long it takes to prove something. although they could be if a given proof system searches monotonically over sizes.
χ-measure : Complexity → Nat
δ-measure : ∀ {N} → Vec Complexity N → Nat

χ-measure (c {N} δ) = δ-measure δ

δ-measure {.0} [] = zero
δ-measure {.(suc _)} (χ ∷ δ) = suc (χ-measure χ + δ-measure δ)

-- Γ ⊢ A ≼ δ = there is a proof of A given Γ of size ≤ δ
_⊢_≼_ : ∀ {N χ} (Γ : N ctx⋖ χ) → Term N → Nat → Set
Γ ⊢ A ≼ δ = ∃ λ a → ∃ λ χ → χ-measure χ ≤ δ × Γ ⊢ a ∶ A ⋖ χ

infixl 25 _,,_

data _ctx⋖_ where
  [] : zero ctx⋖ c []
  _,,_ : ∀ {N ℓ A δΓ δA} →
              (Γ : N ctx⋖ δΓ) → Γ ⊢ A ∶ 𝒰 ℓ ⋖ δA →
            suc N ctx⋖ c (δΓ ∷ δA ∷ [])

_at_ : ∀ {N χ} → N ctx⋖ χ → Fin N → Term N
_,,_ {A = A} Γ γ at zero = weakenTermFrom zero A
(Γ ,, _) at suc n = weakenTermFrom zero (Γ at n)

data _⊢_∶_⋖_ {N χ} (Γ : N ctx⋖ χ) where
  𝒰I : ∀ ℓ →
    Γ ⊢ 𝒰 ℓ ∶ 𝒰 (suc ℓ) ⋖ c []
  𝒰C : ∀ {ℓ A δA} →
    Γ ⊢ A ∶ 𝒰 ℓ ⋖ δA →
    Γ ⊢ A ∶ 𝒰 (suc ℓ) ⋖ c (δA ∷ [])
  ΠF : ∀ {ℓ A B δA δB} →
      (⊢A : Γ ⊢ A ∶ 𝒰 ℓ ⋖ δA) →
      Γ ,, ⊢A ⊢ B ∶ 𝒰 ℓ ⋖ δB →
    Γ ⊢ ΠF A B ∶ 𝒰 ℓ ⋖ c (δA ∷ δB ∷ [])
  ΠI : ∀ {ℓ A b B δA δb} →
    (⊢A : Γ ⊢ A ∶ 𝒰 ℓ ⋖ δA) →
    Γ ,, ⊢A ⊢ b ∶ B ⋖ δb →
    Γ ⊢ ΠI b ∶ ΠF A B ⋖ c (δb ∷ [])
  ΠE : ∀ {f δf A a δa B Ba} →
    Γ ⊢ f ∶ ΠF A B ⋖ δf → Γ ⊢ a ∶ A ⋖ δa →
    instantiateTerm zero a B ≡ Ba →
    Γ ⊢ ΠE f a ∶ Ba ⋖ c (δf ∷ δa ∷ [])
  ΣF : ∀ {ℓ A δA B δB} →
    (⊢A : Γ ⊢ A ∶ 𝒰 ℓ ⋖ δA) → Γ ,, ⊢A ⊢ B ∶ 𝒰 ℓ ⋖ δB →
    Γ ⊢ ΣF A B ∶ 𝒰 ℓ ⋖ c (δA ∷ δB ∷ [])
  ΣI : ∀ {ℓ A δA a δa B δB b δb} →
    (⊢A : Γ ⊢ A ∶ 𝒰 ℓ ⋖ δA) →
    Γ ,, ⊢A ⊢ B ∶ 𝒰 ℓ ⋖ δB → Γ ⊢ a ∶ A ⋖ δa → Γ ⊢ b ∶ instantiateTerm zero a B ⋖ δb →
    Γ ⊢ ΣI a b ∶ ΣF A B ⋖ c (δa ∷ δb ∷ [])
  ΣE : ∀ {ℓ δz A δA B δB C δC g δg p δp Cp} →
      (z : Γ ⊢ ΣF A B ∶ 𝒰 ℓ ⋖ δz) →
      Γ ,, z ⊢ C ∶ 𝒰 ℓ ⋖ δC →
      (⊢A : Γ ⊢ A ∶ 𝒰 ℓ ⋖ δA) →
      (⊢B : Γ ,, ⊢A ⊢ B ∶ 𝒰 ℓ ⋖ δB) →
      Γ ,, ⊢A ,, ⊢B ⊢ g ∶ instantiateTerm (suc (suc zero))
                                          (ΣI (𝓋 (suc zero)) (𝓋 zero))
                                          (weakenTermFrom zero (weakenTermFrom zero C)) ⋖ δg →
      Γ ⊢ p ∶ ΣF A B ⋖ δp →
      Cp ≡ instantiateTerm zero p C →
    Γ ⊢ ΣE C g p ∶ Cp ⋖ c (δC ∷ δg ∷ δp ∷ [])
  +F : ∀ {ℓ A δA B δB} →
    Γ ⊢ A ∶ 𝒰 ℓ ⋖ δA → Γ ⊢ B ∶ 𝒰 ℓ ⋖ δB →
    Γ ⊢ +F A B ∶ 𝒰 ℓ ⋖ c (δA ∷ δB ∷ [])
  +IL : ∀ {ℓ A δA a δa B δB} →
    Γ ⊢ A ∶ 𝒰 ℓ ⋖ δA → Γ ⊢ B ∶ 𝒰 ℓ ⋖ δB → Γ ⊢ a ∶ A ⋖ δa →
    Γ ⊢ +IL a ∶ +F A B ⋖ δa
  +IR : ∀ {ℓ A δA b δb B δB} →
    Γ ⊢ A ∶ 𝒰 ℓ ⋖ δA → Γ ⊢ B ∶ 𝒰 ℓ ⋖ δB → Γ ⊢ b ∶ B ⋖ δb →
    Γ ⊢ +IR b ∶ +F A B ⋖ δb
  +E : ∀ {ℓ δz A δA B δB C δC c' δc d δd e δe Ce} →
      (⊢z : Γ ⊢ +F A B ∶ 𝒰 ℓ ⋖ δz) →
      (⊢A : Γ ⊢ A ∶ 𝒰 ℓ ⋖ δA) →
      (⊢B : Γ ⊢ B ∶ 𝒰 ℓ ⋖ δB) →
      Γ ,, ⊢z ⊢ C ∶ 𝒰 ℓ ⋖ δC →
      Γ ,, ⊢A ⊢ c' ∶ instantiateTerm (suc zero)
                                    (+IL (𝓋 zero))
                                    (weakenTermFrom zero C) ⋖ δc →
      Γ ,, ⊢B ⊢ d ∶ instantiateTerm (suc zero)
                                    (+IR (𝓋 zero))
                                    (weakenTermFrom zero C) ⋖ δd →
      Γ ⊢ e ∶ +F A B ⋖ δe →
      instantiateTerm zero e C ≡ Ce →
    Γ ⊢ +E C c' d e ∶ Ce ⋖ c (δC ∷ δc ∷ δd ∷ δe ∷ [])
  𝟘F : ∀ {ℓ} →
    Γ ⊢ 𝟘F ∶ 𝒰 ℓ ⋖ c []
  𝟘E : ∀ {ℓ δz C δC a δa Ca} →
    (z : Γ ⊢ 𝟘F ∶ 𝒰 ℓ ⋖ δz) →
    Γ ,, z ⊢ C ∶ 𝒰 ℓ ⋖ δC → Γ ⊢ a ∶ 𝟘F ⋖ δa →
    instantiateTerm zero a C ≡ Ca →
    Γ ⊢ 𝟘E C a ∶ Ca ⋖ c (δC ∷ δa ∷ [])
  𝟙F : ∀ {ℓ} →
    Γ ⊢ 𝟙F ∶ 𝒰 ℓ ⋖ c []
  𝟙I :
    Γ ⊢ 𝟙I ∶ 𝟙F ⋖ c []
  𝟙E : ∀ {ℓ C δC c' δc' a δa Ca} →
    Γ ,, (𝟙F {ℓ = ℓ}) ⊢ C ∶ 𝒰 ℓ ⋖ δC → Γ ⊢ c' ∶ instantiateTerm zero 𝟙I C ⋖ δc' → Γ ⊢ a ∶ 𝟙F ⋖ δa →
    instantiateTerm zero a C ≡ Ca →
    Γ ⊢ 𝟙E C c' a ∶ Ca ⋖ c (δC ∷ δc' ∷ δa ∷ [])

  ℕF : ∀ {ℓ} →
    Γ ⊢ ℕF ∶ 𝒰 ℓ ⋖ c []
  ℕIZ :
    Γ ⊢ ℕIZ ∶ ℕF ⋖ c []
  ℕIS : ∀ {n δn} →
    Γ ⊢ n ∶ ℕF ⋖ δn →
    Γ ⊢ ℕIS n ∶ ℕF ⋖ c (δn ∷ [])
  ℕE : ∀ {ℓ C δC c₀ δc₀ cₛ δcₛ n δn Cn} →
    Γ ,, ℕF {ℓ = ℓ} ⊢ C ∶ 𝒰 ℓ ⋖ δC →
    Γ ⊢ c₀ ∶ instantiateTerm zero ℕIZ C ⋖ δc₀ →
    Γ ,, ℕF {ℓ = ℓ} ,, ℕF {ℓ = ℓ} ⊢ cₛ ∶ weakenTermFrom zero
                                         (instantiateTerm (suc zero)
                                                          (ℕIS (𝓋 zero))
                                                          (weakenTermFrom zero C)) ⋖ δcₛ →
    Γ ⊢ n ∶ ℕF ⋖ δn →
    instantiateTerm zero n C ≡ Cn →
    Γ ⊢ ℕE C c₀ cₛ n ∶ Cn ⋖ c (δC ∷ δc₀ ∷ δcₛ ∷ δn ∷ [])
  =F : ∀ {ℓ A δA a δa b δb} →
    Γ ⊢ A ∶ 𝒰 ℓ ⋖ δA → Γ ⊢ a ∶ A ⋖ δa  → Γ ⊢ b ∶ A ⋖ δb →
    Γ ⊢ =F A a b ∶ 𝒰 ℓ ⋖ c (δA ∷ δa ∷ δb ∷ [])
  =I : ∀ {ℓ A δA a δa} →
    Γ ⊢ A ∶ 𝒰 ℓ ⋖ δA → Γ ⊢ a ∶ A ⋖ δa →
    Γ ⊢ =I a ∶ =F A a a ⋖ c (δa ∷ [])
  =E : ∀ {ℓ C δC c' δc' A δA δA' a δa b δb p δp} →
      (⊢A : Γ ⊢ A ∶ 𝒰 ℓ ⋖ δA) →
      (⊢A' : Γ ,, ⊢A ⊢ weakenTermFrom zero A ∶ 𝒰 ℓ ⋖ δA') →
      (⊢p : Γ ,, ⊢A ,, ⊢A' ⊢ =F (weakenTermFrom zero (weakenTermFrom zero A)) ((𝓋 (suc zero))) ((𝓋 zero)) ∶ 𝒰 ℓ ⋖ δp) →
      (⊢C : Γ ,, ⊢A ,, ⊢A' ,, ⊢p ⊢ C ∶ 𝒰 ℓ ⋖ δC) →
      Γ ,, ⊢A ⊢ c' ∶ instantiateTerm (suc zero) (𝓋 zero)
                       (instantiateTerm (suc zero) (𝓋 zero)
                                      (instantiateTerm (suc zero) (=I (𝓋 zero))
                                        (weakenTermFrom zero C))) →
      Γ ⊢ a ∶ A →
      Γ ⊢ b ∶ A →
      Γ ⊢ p ∶ =F A a b →
      Γ ⊢ =E C c' a b p ∶ instantiateTerm zero a
                            (instantiateTerm zero (weakenTermFrom zero b)
                              (instantiateTerm zero
                                (weakenTermFrom zero
                                  (weakenTermFrom zero p)) C)) ⋖ c (δC ∷ δc' ∷ δa ∷ δb ∷ δp ∷ [])
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
  Vble :
    ∀ {n A} →
    Γ at n ≡ A →
    Γ ⊢ 𝓋 n ∶ A ⋖ c []

data _⊢_≝_∶_⋖_ {N χ} (Γ : N ctx⋖ χ) where
  ≡-reflexivity :
    ∀ {a δa A} →
    Γ ⊢ a ∶ A ⋖ δa →
    Γ ⊢ a ≝ a ∶ A ⋖ c (δa ∷ [])
  ≡-symmetry :
    ∀ {a b A δa=b} →
    Γ ⊢ a ≝ b ∶ A ⋖ δa=b →
    Γ ⊢ b ≝ a ∶ A ⋖ c (δa=b ∷ [])
  ≡-transitivity :
    ∀ {a b c' A δa=b δb=c} →
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
    ∀ {ℓ A δA B b b' δb=b'} →
    (⊢A : Γ ⊢ A ∶ 𝒰 ℓ ⋖ δA) →
    Γ ,, ⊢A ⊢ b ≝ b' ∶ B ⋖ δb=b' →
    Γ ⊢ ΠI b ≝ ΠI b' ∶ ΠF A B ⋖ c (δA ∷ δb=b' ∷ [])
  ΣI :
    ∀ {ℓ A δA B δB a a' δa=a' b b' δb=b'} →
    (⊢A : Γ ⊢ A ∶ 𝒰 ℓ ⋖ δA) →
    Γ ,, ⊢A ⊢ B ∶ 𝒰 ℓ ⋖ δB →
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
    Γ ,, ⊢A ⊢ b ∶ B ⋖ δb →
    Γ ⊢ a ∶ A ⋖ δa →
    Γ ⊢ ΠE (ΠI b) a ≝ instantiateTerm zero a b ∶ instantiateTerm zero a B ⋖ c (δA ∷ δb ∷ δa ∷ [])
  ΣE : ∀ {ℓ δΠAB A δA B δB C δC g δg a δa b δb} →
    (⊢ΠAB : Γ ⊢ ΠF A B ∶ 𝒰 ℓ ⋖ δΠAB) →
    Γ ,, ⊢ΠAB ⊢ C ∶ 𝒰 ℓ ⋖ δC →
    (⊢A : Γ ⊢ A ∶ 𝒰 ℓ ⋖ δA) →
    (⊢B : Γ ,, ⊢A ⊢ B ∶ 𝒰 ℓ ⋖ δB) →
    Γ ,, ⊢A ,, ⊢B ⊢ g ∶ instantiateTerm (suc (suc zero)) (ΣI (𝓋 (suc zero)) (𝓋 (suc zero))) (weakenTermFrom zero (weakenTermFrom zero C)) ⋖ δg →
    Γ ⊢ a ∶ A ⋖ δa →
    Γ ⊢ b ∶ instantiateTerm zero a B ⋖ δb →
    Γ ⊢ ΣE C g (ΣI a b) ≝ instantiateTerm zero a (instantiateTerm zero (weakenTermFrom zero b) g) ∶ instantiateTerm zero (ΣI a b) C ⋖ c (δΠAB ∷ δA ∷ δB ∷ δC ∷ δg ∷ δa ∷ δb ∷ [])
  +LE : ∀ {ℓ δ+FAB C δC A δA B δB c' δc' d δd a δa} →
    (⊢+FAB : Γ ⊢ +F A B ∶ 𝒰 ℓ ⋖ δ+FAB) →
    Γ ,, ⊢+FAB ⊢ C ∶ 𝒰 ℓ ⋖ δC →
    (⊢A : Γ ⊢ A ∶ 𝒰 ℓ ⋖ δA) →
    Γ ,, ⊢A ⊢ c' ∶ instantiateTerm (suc zero) (+IL (𝓋 zero)) (weakenTermFrom zero C) ⋖ δc' →
    (⊢B : Γ ⊢ B ∶ 𝒰 ℓ ⋖ δB) →
    Γ ,, ⊢B ⊢ d ∶ instantiateTerm (suc zero) (+IL (𝓋 zero)) (weakenTermFrom zero C) ⋖ δd →
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

## test drive

```
module Sandbox where

  check-𝟙→𝟙 : [] ⊢ ΠI (𝓋 zero) ∶ ΠF 𝟙F 𝟙F ⋖ c (c [] ∷ [])
  check-𝟙→𝟙 = ΠI {ℓ = zero} 𝟙F (Vble refl)

  infer-𝟙→𝟙 : [] ⊢ ΠF 𝟙F 𝟙F
  infer-𝟙→𝟙 = ΠI (𝓋 zero) , c (c [] ∷ []) , ΠI (𝟙F {ℓ = zero}) (Vble {1} {c (c [] ∷ c [] ∷ [])} refl)

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

  check-𝟎=𝟎 : [] ⊢ =I 𝟎 ∶ (𝟎 =ℕ 𝟎)
  check-𝟎=𝟎 = c (c [] ∷ []) , =I {ℓ = zero} ℕF ℕIZ

  infer-𝟎+𝟎=𝟎 : [] ⊢ (𝟎 =ℕ 𝟎)
  infer-𝟎+𝟎=𝟎 = =I 𝟎 , c (c [] ∷ []) , =I {ℓ = zero} ℕF ℕIZ

  check-𝟎+𝟏=𝟏 : [] ⊢ =I 𝟏 ∶ ((𝟎 +ℕ 𝟏) =ℕ 𝟏)
  check-𝟎+𝟏=𝟏 = {!!} , {!!}

  infer-∀n→doublen=𝟐*n : [] ⊢ ΠF ℕF
                                 let n = 𝓋 zero in (double n =ℕ (𝟐 *ℕ n))
  infer-∀n→doublen=𝟐*n = ΠI (=I (𝓋 zero)) , {!!} , {!!}
```

## validation

```agda
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
