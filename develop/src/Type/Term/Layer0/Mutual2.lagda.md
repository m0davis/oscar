
```agda
-- {-# OPTIONS --allow-unsolved-metas #-}
```

# Including mutually-defined weakening and substitution functions for type-checked terms

```agda
module Type.Term.Layer0.Mutual2 where
```

```agda
open import Type.Prelude
open import Type.Term.Layer-1.SCTerm
open import Type.Universe
```

## type-checked terms

```
data _ctx : Nat → Set

-- Γ ⊢ a : A = a proves A given Γ
data _⊢_∶_ {N} (Γ : N ctx) : Term N → Term N → Set


data _⊢_≝_∶_ {N} (Γ : N ctx) : Term N → Term N → Term N → Set

-- Γ ⊢ A = there is a proof of A given Γ
_⊢_ : ∀ {N} (Γ : N ctx) → Term N → Set
Γ ⊢ A = ∃ (Γ ⊢_∶ A)

infixl 25 _,_

data _ctx where
  [] : zero ctx
  _,_ : ∀ {N ℓ A} →
              (Γ : N ctx) → Γ ⊢ A ∶ 𝒰 ℓ →
            suc N ctx

_at_ : ∀ {N} → N ctx → Fin N → Term N
_,_ {A = A} Γ γ at zero = weakenTermFrom zero A
(Γ , _) at suc n = weakenTermFrom zero (Γ at n)

data _⊢_∶_ {N} (Γ : N ctx) where
  Vble :
    ∀ {n A} →
    Γ at n ≡ A →
    Γ ⊢ 𝓋 n ∶ A

  𝒰I : ∀ {ℓ} →
    Γ ⊢ 𝒰 ℓ ∶ 𝒰 (suc ℓ)
  𝒰C : ∀ {ℓ A} →
    Γ ⊢ A ∶ 𝒰 ℓ →
    Γ ⊢ A ∶ 𝒰 (suc ℓ)
  ΠF : ∀ {ℓ A B} →
      (⊢A : Γ ⊢ A ∶ 𝒰 ℓ) →
      Γ , ⊢A ⊢ B ∶ 𝒰 ℓ →
    Γ ⊢ ΠF A B ∶ 𝒰 ℓ
  ΠI : ∀ ℓ {A B b} →
    (⊢A : Γ ⊢ A ∶ 𝒰 ℓ) →
    Γ , ⊢A ⊢ b ∶ B →
    Γ ⊢ ΠI b ∶ ΠF A B
  ΠE : ∀ A B {B[a] f a} →
    Γ ⊢ f ∶ ΠF A B →
    Γ ⊢ a ∶ A →
    instantiateTerm zero a B ≡ B[a] →
    Γ ⊢ ΠE f a ∶ B[a]
  ΣF : ∀ {ℓ A B} →
    (⊢A : Γ ⊢ A ∶ 𝒰 ℓ) →
    Γ , ⊢A ⊢ B ∶ 𝒰 ℓ →
    Γ ⊢ ΣF A B ∶ 𝒰 ℓ
  ΣI : ∀ ℓ {A B a b} →
    (⊢A : Γ ⊢ A ∶ 𝒰 ℓ) →
    Γ , ⊢A ⊢ B ∶ 𝒰 ℓ →
    Γ ⊢ a ∶ A →
    Γ ⊢ b ∶ instantiateTerm zero a B →
    Γ ⊢ ΣI a b ∶ ΣF A B
  ΣE : ∀ ℓ A B {C[p] C g p} →
      (⊢A : Γ ⊢ A ∶ 𝒰 ℓ) →
      (⊢B : Γ , ⊢A ⊢ B ∶ 𝒰 ℓ) →
      Γ , ΣF ⊢A ⊢B ⊢ C ∶ 𝒰 ℓ →
      Γ , ⊢A , ⊢B ⊢ g ∶ instantiateTerm (suc (suc zero))
                                          (ΣI (𝓋 (suc zero)) (𝓋 zero))
                                          (weakenTermFrom zero (weakenTermFrom zero C)) →
      Γ ⊢ p ∶ ΣF A B →
      C[p] ≡ instantiateTerm zero p C →
    Γ ⊢ ΣE C g p ∶ C[p]
  +F : ∀ {ℓ A B} →
    Γ ⊢ A ∶ 𝒰 ℓ →
    Γ ⊢ B ∶ 𝒰 ℓ →
    Γ ⊢ +F A B ∶ 𝒰 ℓ
```

Note that in the HoTT book, `+IL` demands that both arguments to `+F` be well-formed types, but as an alternative to that, I see no problem with allowing `B` to be garbage: if asked whether it is true that (zero equals zero) or (colorless green ideas sleep furiously), it seems that one should be able to answer positively yes and give the proof of the former, rather than complain that one doesn't understand the latter half of the question.

(changing this back for the moment)

```agda
  +IL : ∀ ℓ {A B a} →
    Γ ⊢ A ∶ 𝒰 ℓ →
    Γ ⊢ B ∶ 𝒰 ℓ →
    Γ ⊢ a ∶ A →
    Γ ⊢ +IL a ∶ +F A B
  +IR : ∀ ℓ {A B b} →
    Γ ⊢ A ∶ 𝒰 ℓ →
    Γ ⊢ B ∶ 𝒰 ℓ →
    Γ ⊢ b ∶ B →
    Γ ⊢ +IR b ∶ +F A B
  +E : ∀ ℓ A B {N[a+b] N na nb a+b} →
      (⊢A : Γ ⊢ A ∶ 𝒰 ℓ) →
      (⊢B : Γ ⊢ B ∶ 𝒰 ℓ) →
      Γ , +F ⊢A ⊢B ⊢ N ∶ 𝒰 ℓ →
      Γ , ⊢A ⊢ na ∶ instantiateTerm (suc zero)
                                     (+IL (𝓋 zero))
                                     (weakenTermFrom zero N) →
      Γ , ⊢B ⊢ nb ∶ instantiateTerm (suc zero)
                                     (+IR (𝓋 zero))
                                     (weakenTermFrom zero N) →
      Γ ⊢ a+b ∶ +F A B →
      instantiateTerm zero a+b N ≡ N[a+b] →
    Γ ⊢ +E N na nb a+b ∶ N[a+b]
  𝟘F : ∀ {ℓ} →
    Γ ⊢ 𝟘F ∶ 𝒰 ℓ
```

Similar to the above, unlike the HoTT book, I allow one to prove absolutely anything (that is scope-checked) given bottom. The philosophical justification, however is a little trickier, at least in my mind. For now, another reason I give is a practical one: I just don't care.

(changing back for now)

```agda
  𝟘E : ∀ ℓ {N[a] N a} →
    Γ , 𝟘F {ℓ = ℓ} ⊢ N ∶ 𝒰 ℓ →
    Γ ⊢ a ∶ 𝟘F →
    instantiateTerm zero a N ≡ N[a] →
    Γ ⊢ 𝟘E N a ∶ N[a]
  𝟙F : ∀ {ℓ} →
    Γ ⊢ 𝟙F ∶ 𝒰 ℓ
  𝟙I :
    Γ ⊢ 𝟙I ∶ 𝟙F
```

Here, by eliminating the requirement that N be well-formed, I fear to be treading on thin-ice: might I be allowing the successor of true be a natural number? Note that in this and in the case of bottom, we are dealing with elimination rules. The introduction rule for + did not seem nearly so... upsetting.

(changing back for now)

```agda
  𝟙E : ∀ ℓ {N[a] N n1 a} →
    Γ , 𝟙F {ℓ = ℓ} ⊢ N ∶ 𝒰 ℓ →
    Γ ⊢ n1 ∶ instantiateTerm zero 𝟙I N →
    Γ ⊢ a ∶ 𝟙F →
    instantiateTerm zero a N ≡ N[a] →
    Γ ⊢ 𝟙E N n1 a ∶ N[a]
  ℕF : ∀ {ℓ} →
    Γ ⊢ ℕF ∶ 𝒰 ℓ
  ℕIZ :
    Γ ⊢ ℕIZ ∶ ℕF
  ℕIS : ∀ {n} →
    Γ ⊢ n ∶ ℕF →
    Γ ⊢ ℕIS n ∶ ℕF
```

```agda
  ℕE : ∀ ℓ {X[n] X x₀  xₛ n} →
    (⊢X : Γ , ℕF {ℓ = ℓ} ⊢ X ∶ 𝒰 ℓ) →
    Γ ⊢ x₀ ∶ instantiateTerm zero ℕIZ X →
    Γ , ℕF {ℓ = ℓ} , ⊢X ⊢ xₛ ∶ weakenTermFrom zero
                                   (instantiateTerm (suc zero)
                                     (ℕIS (𝓋 zero))
                                     (weakenTermFrom zero X)) →
    Γ ⊢ n ∶ ℕF →
    instantiateTerm zero n X ≡ X[n] →
    Γ ⊢ ℕE X x₀ xₛ n ∶ X[n]
  =F : ∀ {ℓ A a b} →
    Γ ⊢ A ∶ 𝒰 ℓ →
    Γ ⊢ a ∶ A →
    Γ ⊢ b ∶ A →
    Γ ⊢ =F A a b ∶ 𝒰 ℓ
  =I : ∀ ℓ {A a} →
    Γ ⊢ A ∶ 𝒰 ℓ →
    Γ ⊢ a ∶ A →
    Γ ⊢ =I a ∶ =F A a a
```

Here I am experimenting with

```agda
  =E : ∀ ℓ {X[a,b,p] X c' A a b p} →
      (⊢A : Γ ⊢ A ∶ 𝒰 ℓ) →
      (⊢A' : Γ , ⊢A ⊢ weakenTermFrom zero A ∶ 𝒰 ℓ) →
      (⊢p : Γ , ⊢A , ⊢A' ⊢ =F (weakenTermFrom zero (weakenTermFrom zero A))
                                ((𝓋 (suc zero)))
                                ((𝓋 zero))
                           ∶ 𝒰 ℓ) →
      (⊢C : Γ , ⊢A , ⊢A' , ⊢p ⊢ X ∶ 𝒰 ℓ) →
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
      Γ ⊢ =E X c' a b p ∶ X[a,b,p]
```

The HoTT book has no name for this.

```agda
  ≡-type-substitution :
    ∀ {ℓ a A B} →
    Γ ⊢ a ∶ A →
    Γ ⊢ A ≝ B ∶ 𝒰 ℓ →
    Γ ⊢ a ∶ B
```

I was surprised to find this missing from the HoTT book. I do not see how to make use of computational equalities without it.

```agda
  ≡-term-substitution :
    ∀ {a b A} →
    Γ ⊢ a ∶ A →
    Γ ⊢ a ≝ b ∶ A →
    Γ ⊢ b ∶ A
```

```agda
data _⊢_≝_∶_ {N} (Γ : N ctx) where
  ≡-reflexivity :
    ∀ {a A} →
    Γ ⊢ a ∶ A →
    Γ ⊢ a ≝ a ∶ A
  ≡-symmetry :
    ∀ {A a b} →
    Γ ⊢ a ≝ b ∶ A →
    Γ ⊢ b ≝ a ∶ A
  ≡-transitivity :
    ∀ {A a b c'} →
    Γ ⊢ a ≝ b ∶ A →
    Γ ⊢ b ≝ c' ∶ A →
    Γ ⊢ a ≝ c' ∶ A
  ≡-type-substitution :
    ∀ {ℓ a b A B} →
    Γ ⊢ a ≝ b ∶ A →
    Γ ⊢ A ≝ B ∶ 𝒰 ℓ →
    Γ ⊢ a ≝ b ∶ B
  Π-uniq :
    ∀ f A B →
    Γ ⊢ f ∶ ΠF A B →
    Γ ⊢ f ≝ ΠI (ΠE (weakenTermFrom zero f) (𝓋 zero)) ∶ ΠF A B
```

The HoTT book takes `Π-intro-eq` to require `Γ , x:A ⊢ B : 𝒰ᵢ`. However, I conjecture that such a judgement would already have been made in order to conclude another of its requirements, `Γ , x:A ⊢ b ≡ b' : B`, so I leave it out.

On the other hand, the requirement `Γ ⊢ A : 𝒰ᵢ` is needed as part of the construction of another premise, so it stays.

```agda
  ΠI :
    ∀ ℓ {A B b b'} →
    (⊢A : Γ ⊢ A ∶ 𝒰 ℓ) →
    Γ , ⊢A ⊢ b ≝ b' ∶ B →
    Γ ⊢ ΠI b ≝ ΠI b' ∶ ΠF A B
  ΣI :
    ∀ {ℓ A B a a' b b'} →
    (⊢A : Γ ⊢ A ∶ 𝒰 ℓ) →
    Γ , ⊢A ⊢ B ∶ 𝒰 ℓ →
    Γ ⊢ a ≝ a' ∶ A →
    Γ ⊢ b ≝ b' ∶ instantiateTerm zero a B →
    Γ ⊢ ΣI a b ≝ ΣI a' b' ∶ ΣF A B
  +IL :
    ∀ {A a a' B} →
    Γ ⊢ a ≝ a' ∶ A →
    Γ ⊢ +IL a ≝ +IL a' ∶ +F A B
  +IR :
    ∀ {A B b b'} →
    Γ ⊢ b ≝ b' ∶ B →
    Γ ⊢ +IR b ≝ +IR b' ∶ +F A B
  ℕIS :
    ∀ {n n'} →
    Γ ⊢ n ≝ n' ∶ ℕF →
    Γ ⊢ ℕIS n ≝ ℕIS n' ∶ ℕF
```

This definitional equality is not obvious from Appendix 2.

```agda
  =I : ∀ {A a a'} →
    Γ ⊢ a ≝ a' ∶ A →
    Γ ⊢ =I a ≝ =I a' ∶ =F A a a'
```

Computation rules:

```agda
  ΠE : ∀ {ℓ A B b a}
    (⊢A : Γ ⊢ A ∶ 𝒰 ℓ) →
    Γ , ⊢A ⊢ b ∶ B →
    Γ ⊢ a ∶ A →
    Γ ⊢ ΠE (ΠI b) a ≝ instantiateTerm zero a b ∶ instantiateTerm zero a B
  ΣE : ∀ {ℓ A B C g a b} →
    (⊢ΠAB : Γ ⊢ ΠF A B ∶ 𝒰 ℓ) →
    Γ , ⊢ΠAB ⊢ C ∶ 𝒰 ℓ →
    (⊢A : Γ ⊢ A ∶ 𝒰 ℓ) →
    (⊢B : Γ , ⊢A ⊢ B ∶ 𝒰 ℓ) →
    Γ , ⊢A , ⊢B ⊢ g ∶ instantiateTerm (suc (suc zero)) (ΣI (𝓋 (suc zero)) (𝓋 (suc zero))) (weakenTermFrom zero (weakenTermFrom zero C)) →
    Γ ⊢ a ∶ A →
    Γ ⊢ b ∶ instantiateTerm zero a B →
    Γ ⊢ ΣE C g (ΣI a b) ≝ instantiateTerm zero a (instantiateTerm zero (weakenTermFrom zero b) g) ∶ instantiateTerm zero (ΣI a b) C
  +LE : ∀ {ℓ C A B c' d a} →
    (⊢+FAB : Γ ⊢ +F A B ∶ 𝒰 ℓ) →
    Γ , ⊢+FAB ⊢ C ∶ 𝒰 ℓ →
    (⊢A : Γ ⊢ A ∶ 𝒰 ℓ) →
    Γ , ⊢A ⊢ c' ∶ instantiateTerm (suc zero) (+IL (𝓋 zero)) (weakenTermFrom zero C) →
    (⊢B : Γ ⊢ B ∶ 𝒰 ℓ) →
    Γ , ⊢B ⊢ d ∶ instantiateTerm (suc zero) (+IL (𝓋 zero)) (weakenTermFrom zero C) →
    Γ ⊢ a ∶ A →
    Γ ⊢ +E C c' d (+IL a) ≝ instantiateTerm zero a c' ∶ instantiateTerm zero (+IL a) C
```

Instead of something like the above, could simpler computation rules like these work?

```agda
  +RE : ∀ {b B C C[+IRb] c' d d[b]} →
    Γ ⊢ b ∶ B →
    instantiateTerm zero (+IR b) C ≡ C[+IRb] →
    instantiateTerm zero b d ≡ d[b] →
    Γ ⊢ +E C c' d (+IR b) ≝ d[b] ∶ C[+IRb]
  𝟙E : ∀ {C c' C[𝟙I]} →
    instantiateTerm zero 𝟙I C ≡ C[𝟙I] →
    Γ ⊢ 𝟙E C c' 𝟙I ≝ c' ∶ C[𝟙I]
  ℕEZ : ∀ {n C c₀ cₛ C[ℕIZ]} →
    Γ ⊢ n ∶ ℕF →
    instantiateTerm zero ℕIZ C ≡ C[ℕIZ] →
    Γ ⊢ ℕE C c₀ cₛ ℕIZ ≝ c₀ ∶ C[ℕIZ]
  ℕES : ∀ {n C c₀ cₛ cₛ[n,ℕEn] C[ℕISn]} →
    Γ ⊢ n ∶ ℕF →
    instantiateTerm zero n ((instantiateTerm zero (weakenTermFrom zero (Term.ℕE C c₀ cₛ n)) cₛ)) ≡ cₛ[n,ℕEn] →
    instantiateTerm zero (ℕIS n) C ≡ C[ℕISn] →
    Γ ⊢ ℕE C c₀ cₛ (ℕIS n) ≝ cₛ[n,ℕEn] ∶ C[ℕISn]
  =E : ∀ {a c' c[a] C C[a,a,=Ia]} →
    instantiateTerm zero a c' ≡ c[a] →
    instantiateTerm zero a
      (instantiateTerm zero
        (weakenTermFrom zero a)
        ((instantiateTerm zero
          (weakenTermFrom zero
            (weakenTermFrom zero
              (=I a))) C))) ≡ C[a,a,=Ia] →
    Γ ⊢ =E C c' a a (=I a) ≝ c[a] ∶ C[a,a,=Ia]
```
