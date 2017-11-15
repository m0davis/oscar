
Specification of Type Theory (from the HoTT book)

```agda
module TypeTheory-2 where
```

```agda
module FormalTypeTheory where
  open import Preliminary

  weakenFinFrom : ∀ {N} → Fin (suc N) → Fin N → Fin (suc N)
  weakenFinFrom zero x = suc x
  weakenFinFrom (suc from) zero = zero
  weakenFinFrom (suc from) (suc x) = suc (weakenFinFrom from x)

  {- You are a pigeon. There are some pigeon holes labeled 0,1,...,N. You are given a particular pigeon hole, i. One of the holes that you are not given, labeled h, is removed, and the pigeon holes are relabeled 0,1,...,N-1. What is the new label on your pigeon hole?  -}
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

  Universe = Nat

  data Complexity : Set where
    c : ∀ {N} → Vec Complexity N → Complexity

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

  data _ctx⋖_ : Nat → Complexity → Set

  -- Γ ⊢ a : A ⋖ χ = a proves A given Γ, with complexity χ
  data _⊢_∶_⋖_ {N χ} (Γ : N ctx⋖ χ) : Term N → Term N → Complexity → Set

  -- Γ ⊢ a : A = a is a proof of A given Γ
  _⊢_∶_ : ∀ {N χ} (Γ : N ctx⋖ χ) → Term N → Term N → Set
  Γ ⊢ a ∶ A = ∃ (Γ ⊢ a ∶ A ⋖_)

  -- Γ ⊨ A = there is a proof of A
  _⊨_ : ∀ {N χ} (Γ : N ctx⋖ χ) → Term N → Set
  Γ ⊨ A = ∃ (Γ ⊢_∶ A)

  χ-measure : Complexity → Nat
  δ-measure : ∀ {N} → Vec Complexity N → Nat

  χ-measure (c {N} δ) = δ-measure δ

  δ-measure {.0} [] = zero
  δ-measure {.(suc _)} (χ ∷ δ) = suc (χ-measure χ + δ-measure δ)

  _⊨_≼_ : ∀ {N χ} (Γ : N ctx⋖ χ) → Term N → Nat → Set
  Γ ⊨ A ≼ δ = ∃ λ a → ∃ λ χ → χ-measure χ ≤ δ × Γ ⊢ a ∶ A ⋖ χ

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

    Vble :
      ∀ {n A} →
      Γ at n ≡ A →
      Γ ⊢ 𝓋 n ∶ A ⋖ c []

  module Test where

    0=0 : [] ⊢ =I ℕIZ ∶ =F ℕF ℕIZ ℕIZ
    0=0 = c (c [] ∷ []) , =I {ℓ = zero} ℕF ℕIZ


    2+2=4 : [] ⊢ =I (ℕIS (ℕIS (ℕIS (ℕIS ℕIZ)))) ∶ =F ℕF (ΠE (ΠI (ℕE (ΠF ℕF ℕF) (ΠI (𝓋 zero)) (ΠI (ℕIS (ΠE (𝓋 (suc zero)) (𝓋 zero)))) (𝓋 zero))) (ℕIS (ℕIS ℕIZ))) (ℕIS (ℕIS (ℕIS (ℕIS ℕIZ))))
    2+2=4 = {!!} , {!!}

    test' : [] ⊢ ΠI (𝓋 zero) ∶ ΠF 𝟙F 𝟙F ⋖ c (c [] ∷ [])
    test' = ΠI (𝟙F {ℓ = zero}) (Vble refl)

    test'' : ∃ λ N → ∃ λ c' → ∃ λ p → [] ⊢ p ∶ ΠF 𝟙F 𝟙F ⋖ c {N} c'
    test'' = 1 , c [] ∷ [] , ΠI (𝓋 zero) , ΠI (𝟙F {ℓ = zero}) (Vble {1} {c (c [] ∷ c [] ∷ [])} refl)



  consistent : ∀ ℓ → [] ⊢ 𝟘F ∶ 𝒰 ℓ × ¬ ([] ⊨ 𝟘F)
  consistent = {!!}
{-
  consistent : ∃ λ bottom → ∃ λ ℓ → [] ⊨ bottom ∶ 𝒰 ℓ × ¬ ([] ⊨ bottom)
  consistent = {!!}
-}

  TC-decidable : ∀ {N χ} (Γ : N ctx⋖ χ) (a : Term N) (A : Term N) → Dec (Γ ⊢ a ∶ A)
  TC-decidable = {!!}

  σ-decidable : ∀ {N δ} (Γ : N ctx⋖ δ) (A : Term N) (ℓ : Universe)
              → Γ ⊢ A ∶ 𝒰 ℓ
              → ∀ σ
              → Dec (Γ ⊨ A ≼ σ)
  σ-decidable Γ (𝒰 zero) ℓ x zero = yes (𝟙F , _ , diff zero refl , 𝟙F)
  σ-decidable Γ (𝒰 (suc x₁)) ℓ x zero = yes ({!!} , {!!} , {!!} , {!!})
  σ-decidable Γ (𝓋 x₁) ℓ x zero = {!!}
  σ-decidable Γ (ΠF A A₁) ℓ x zero = {!!}
  σ-decidable Γ (ΠI A) ℓ x zero = {!!}
  σ-decidable Γ (ΠE A A₁) ℓ x zero = {!!}
  σ-decidable Γ (ΣF A A₁) ℓ x zero = {!!}
  σ-decidable Γ (ΣI A A₁) ℓ x zero = {!!}
  σ-decidable Γ (ΣE A A₁ A₂) ℓ x zero = {!!}
  σ-decidable Γ (+F A A₁) ℓ x zero = {!!}
  σ-decidable Γ (+IL A) ℓ x zero = {!!}
  σ-decidable Γ (+IR A) ℓ x zero = {!!}
  σ-decidable Γ (+E A A₁ A₂ A₃) .(suc _) (.(c (_ ∷ [])) , 𝒰C snd₁) zero = {!!}
  σ-decidable Γ (+E A A₁ A₂ A₃) ℓ (.(c (_ ∷ _ ∷ _ ∷ _ ∷ [])) , +E snd₁ snd₂ snd₃ snd₄ snd₅ snd₆ snd₇ x) zero = {!!}
  σ-decidable Γ 𝟘F ℓ x zero = {!!}
  σ-decidable Γ (𝟘E A A₁) ℓ x zero = {!!}
  σ-decidable Γ 𝟙F ℓ x zero = {!!}
  σ-decidable Γ 𝟙I ℓ x zero = {!!}
  σ-decidable Γ (𝟙E A A₁ A₂) ℓ x zero = {!!}
  σ-decidable Γ ℕF ℓ x zero = {!!}
  σ-decidable Γ ℕIZ ℓ x zero = {!!}
  σ-decidable Γ (ℕIS A) ℓ x zero = {!!}
  σ-decidable Γ (ℕE A A₁ A₂ A₃) ℓ x zero = {!!}
  σ-decidable Γ (=F A A₁ A₂) ℓ x zero = {!!}
  σ-decidable Γ (=I A) ℓ x zero = {!!}
  σ-decidable Γ (=E A A₁ A₂ A₃ A₄) ℓ x zero = {!!}
  σ-decidable Γ A ℓ x (suc σ) = {!!}
```
