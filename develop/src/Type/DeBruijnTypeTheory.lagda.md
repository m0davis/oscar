
```agda
-- {-# OPTIONS --allow-unsolved-metas #-}
```

# Including mutually-defined weakening and substitution functions for type-checked terms

```agda
module Type.DeBruijnTypeTheory where
```

```agda
open import Type.Prelude
open import Type.A2
open import Type.DeBruijnA2
open import Type.DeBruijnVariable
open import Type.DeBruijnExpression interpretAlphabet renaming (instantiateExpressionAt to instantiateExpressionAt')
open import Type.DeBruijnContext interpretAlphabet

-- FIXME the order of arguments should be standardised across modules
instantiateExpressionAt : ∀ {N} → Fin (suc N) → Expression N → Expression (suc N) → Expression N
instantiateExpressionAt at r x = instantiateExpressionAt' at x r

open import Type.Universe
```

```agda
Context = 0 ≾_
```

## type-checked terms

```
data _ctx : ∀ {N} → Context N → Set

-- Γ ⊢ a : A = a proves A given Γ
data _⊢_∶_ {N} (Γ : Context N) : Expression N → Expression N → Set


data _⊢_≝_∶_ {N} (Γ : Context N) : Expression N → Expression N → Expression N → Set

-- Γ ⊢ A = there is a proof of A given Γ
_⊢_ : ∀ {N} (Γ : Context N) → Expression N → Set
Γ ⊢ A = ∃ (Γ ⊢_∶ A)

data _ctx where
  [] : ε ctx
  _,_ : ∀ {N ℓ A} →
              {Γ : Context N} → Γ ctx → (Γ⊢A∶𝒰 : Γ ⊢ A ∶ 𝒰 ℓ) →
            (Γ , A) ctx

_at_ : ∀ {N} (Γ : Context N) → Fin N → Expression N
(Γ , A) at zero = weakenExpressionFrom zero A
(Γ , _) at suc n = weakenExpressionFrom zero (Γ at n)

infix 4 _⊢_∶_
data _⊢_∶_ {N} (Γ : Context N) where
  Vble :
    Γ ctx →
    ∀ {n A} →
    Γ at n ≡ A →
    Γ ⊢ 𝓋 n ∶ A

  𝒰I : ∀ {ℓ} →
    Γ ⊢ 𝒰 ℓ ∶ 𝒰 (suc ℓ)
  𝒰C : ∀ {ℓ A} →
    Γ ⊢ A ∶ 𝒰 ℓ →
    Γ ⊢ A ∶ 𝒰 (suc ℓ)
  ΠF : ∀ {ℓ A B} →
      Γ ⊢ A ∶ 𝒰 ℓ →
      Γ , A ⊢ B ∶ 𝒰 ℓ →
    Γ ⊢ Πf A B ∶ 𝒰 ℓ
  ΠI : ∀ ℓ {A B b} →
    Γ ⊢ A ∶ 𝒰 ℓ →
    Γ , A ⊢ b ∶ B →
    Γ ⊢ Πi A b ∶ Πf A B
  ΠE : ∀ A B {B[a] f a} →
    Γ ⊢ f ∶ Πf A B →
    Γ ⊢ a ∶ A →
    instantiateExpressionAt zero a B ≡ B[a] →
    Γ ⊢ Πe f a ∶ B[a]
  ΣF : ∀ {ℓ A B} →
    Γ ⊢ A ∶ 𝒰 ℓ →
    Γ , A ⊢ B ∶ 𝒰 ℓ →
    Γ ⊢ Σf A B ∶ 𝒰 ℓ
  ΣI : ∀ ℓ {A B a b} →
    Γ ⊢ A ∶ 𝒰 ℓ →
    Γ , A ⊢ B ∶ 𝒰 ℓ →
    Γ ⊢ a ∶ A →
    Γ ⊢ b ∶ instantiateExpressionAt zero a B →
    Γ ⊢ Σi a b ∶ Σf A B
  ΣE : ∀ ℓ A B {C[p] C g p}
     → Γ ⊢ A ∶ 𝒰 ℓ
     → Γ , A ⊢ B ∶ 𝒰 ℓ
     → Γ , Σf A B ⊢ C ∶ 𝒰 ℓ
     → Γ , A , B ⊢ g ∶ instantiateExpressionAt 2
                                               (Σi (𝓋 1) (𝓋 0))
                                               (weakenExpressionFrom 0 (weakenExpressionFrom 0 C))
     → Γ ⊢ p ∶ Σf A B
     → C[p] ≡ instantiateExpressionAt zero p C
     → Γ ⊢ Σe C g p ∶ C[p]
  +F : ∀ {ℓ A B} →
    Γ ⊢ A ∶ 𝒰 ℓ →
    Γ ⊢ B ∶ 𝒰 ℓ →
    Γ ⊢ +f A B ∶ 𝒰 ℓ
```

Note that in the HoTT book, `+Iˡ` demands that both arguments to `+F` be well-formed types, but as an alternative to that, I see no problem with allowing `B` to be garbage: if asked whether it is true that (zero equals zero) or (colorless green ideas sleep furiously), it seems that one should be able to answer positively yes and give the proof of the former, rather than complain that one doesn't understand the latter half of the question.

(changing this back for the moment)

```agda
  +Iˡ : ∀ ℓ {A B a} →
    Γ ⊢ A ∶ 𝒰 ℓ →
    Γ ⊢ B ∶ 𝒰 ℓ →
    Γ ⊢ a ∶ A →
    Γ ⊢ +iˡ a ∶ +f A B
  +Iʳ : ∀ ℓ {A B b} →
    Γ ⊢ A ∶ 𝒰 ℓ →
    Γ ⊢ B ∶ 𝒰 ℓ →
    Γ ⊢ b ∶ B →
    Γ ⊢ +iʳ b ∶ +f A B
  +E : ∀ ℓ A B {N[a+b] N na nb a+b} →
      Γ ⊢ A ∶ 𝒰 ℓ →
      Γ ⊢ B ∶ 𝒰 ℓ →
      Γ , +f A B ⊢ N ∶ 𝒰 ℓ →
      Γ , A ⊢ na ∶ instantiateExpressionAt (suc zero)
                                   (+iˡ (𝓋 zero))
                                   (weakenExpressionFrom zero N) →
      Γ , B ⊢ nb ∶ instantiateExpressionAt (suc zero)
                                   (+iʳ (𝓋 zero))
                                   (weakenExpressionFrom zero N) →
      Γ ⊢ a+b ∶ +f A B →
      instantiateExpressionAt zero a+b N ≡ N[a+b] →
    Γ ⊢ +e N na nb a+b ∶ N[a+b]
  𝟘F : ∀ {ℓ} →
    Γ ⊢ 𝟘f ∶ 𝒰 ℓ
```

Similar to the above, unlike the HoTT book, I allow one to prove absolutely anything (that is scope-checked) given bottom. The philosophical justification, however is a little trickier, at least in my mind. For now, another reason I give is a practical one: I just don't care.

(changing back for now)

```agda
  𝟘E : ∀ ℓ {N[a] N a} →
    Γ , 𝟘f ⊢ N ∶ 𝒰 ℓ →
    Γ ⊢ a ∶ 𝟘f →
    instantiateExpressionAt zero a N ≡ N[a] →
    Γ ⊢ 𝟘e N a ∶ N[a]
  𝟙F : ∀ {ℓ} →
    Γ ⊢ 𝟙f ∶ 𝒰 ℓ
  𝟙I :
    Γ ⊢ 𝟙i ∶ 𝟙f
```

Here, by eliminating the requirement that N be well-formed, I fear to be treading on thin-ice: might I be allowing the successor of true be a natural number? Note that in this and in the case of bottom, we are dealing with elimination rules. The introduction rule for + did not seem nearly so... upsetting.

(changing back for now)

```agda
  𝟙E : ∀ ℓ {N[a] N n1 a} →
    Γ , 𝟙f ⊢ N ∶ 𝒰 ℓ →
    Γ ⊢ n1 ∶ instantiateExpressionAt zero 𝟙i N →
    Γ ⊢ a ∶ 𝟙f →
    instantiateExpressionAt zero a N ≡ N[a] →
    Γ ⊢ 𝟙e N n1 a ∶ N[a]
  ℕF : ∀ {ℓ} →
    Γ ⊢ ℕf ∶ 𝒰 ℓ
  ℕIᶻ :
    Γ ⊢ ℕiᶻ ∶ ℕf
  ℕIˢ : ∀ {n} →
    Γ ⊢ n ∶ ℕf →
    Γ ⊢ ℕiˢ n ∶ ℕf
```

```agda
  ℕE : ∀ ℓ {X[n] X x₀  xₛ n} →
    (⊢X : Γ , ℕf ⊢ X ∶ 𝒰 ℓ) →
    Γ ⊢ x₀ ∶ instantiateExpressionAt zero ℕiᶻ X →
    Γ , ℕf , X ⊢ xₛ ∶ weakenExpressionFrom zero
                                   (instantiateExpressionAt (suc zero)
                                     (ℕiˢ (𝓋 zero))
                                     (weakenExpressionFrom zero X)) →
    Γ ⊢ n ∶ ℕf →
    instantiateExpressionAt zero n X ≡ X[n] →
    Γ ⊢ ℕe X x₀ xₛ n ∶ X[n]
  =F : ∀ {ℓ A a b} →
    Γ ⊢ A ∶ 𝒰 ℓ →
    Γ ⊢ a ∶ A →
    Γ ⊢ b ∶ A →
    Γ ⊢ =f A a b ∶ 𝒰 ℓ
  =I : ∀ ℓ {A a} →
    Γ ⊢ A ∶ 𝒰 ℓ →
    Γ ⊢ a ∶ A →
    Γ ⊢ =i a ∶ =f A a a
```

Here I am experimenting with

```agda
  =E : ∀ ℓ {X[a,b,p] X c' A a b p} →
      (⊢A : Γ ⊢ A ∶ 𝒰 ℓ) →
      (⊢A' : Γ , A ⊢ weakenExpressionFrom zero A ∶ 𝒰 ℓ) →
      (⊢p : Γ , A , weakenExpressionFrom zero A ⊢ =f (weakenExpressionFrom zero (weakenExpressionFrom zero A))
                                ((𝓋 (suc zero)))
                                ((𝓋 zero))
                           ∶ 𝒰 ℓ) →
      (⊢C : Γ , A , weakenExpressionFrom zero A , (weakenExpressionFrom zero (weakenExpressionFrom zero p)) ⊢ X ∶ 𝒰 ℓ) →
      Γ , A ⊢ c' ∶ instantiateExpressionAt (suc zero) (𝓋 zero)
                       (instantiateExpressionAt (suc zero) (𝓋 zero)
                                      (instantiateExpressionAt (suc zero) (=i (𝓋 zero))
                                        (weakenExpressionFrom zero X))) →
      Γ ⊢ a ∶ A →
      Γ ⊢ b ∶ A →
      Γ ⊢ p ∶ =f A a b →
      instantiateExpressionAt zero a
        (instantiateExpressionAt zero (weakenExpressionFrom zero b)
          (instantiateExpressionAt zero
            (weakenExpressionFrom zero
              (weakenExpressionFrom zero p)) X)) ≡ X[a,b,p] →
      Γ ⊢ =e X c' a b p ∶ X[a,b,p]
```

The HoTT book has no name for this.

```agda
  ≝-subst :
    ∀ {ℓ a A B} →
    Γ ⊢ a ∶ A →
    Γ ⊢ A ≝ B ∶ 𝒰 ℓ →
    Γ ⊢ a ∶ B
```

```agda
infix 4 _⊢_≝_∶_
data _⊢_≝_∶_ {N} (Γ : Context N) where
  ≝-reflexivity :
    ∀ {a A} →
    Γ ⊢ a ∶ A →
    Γ ⊢ a ≝ a ∶ A
  ≝-symmetry :
    ∀ {A a b} →
    Γ ⊢ a ≝ b ∶ A →
    Γ ⊢ b ≝ a ∶ A
  ≝-transitivity :
    ∀ {A a b c'} →
    Γ ⊢ a ≝ b ∶ A →
    Γ ⊢ b ≝ c' ∶ A →
    Γ ⊢ a ≝ c' ∶ A
  ≝-subst :
    ∀ {ℓ a b A B} →
    Γ ⊢ a ≝ b ∶ A →
    Γ ⊢ A ≝ B ∶ 𝒰 ℓ →
    Γ ⊢ a ≝ b ∶ B
  ΠU :
    ∀ f A B →
    Γ ⊢ f ∶ Πf A B →
    Γ ⊢ f ≝ Πi A (Πe (weakenExpressionFrom zero f) (𝓋 zero)) ∶ Πf A B
```

The HoTT book takes `Π-intro-eq` to require `Γ , x:A ⊢ B : 𝒰ᵢ`. However, I conjecture that such a judgement would already have been made in order to conclude another of its requirements, `Γ , x:A ⊢ b ≡ b' : B`, so I leave it out.

On the other hand, the requirement `Γ ⊢ A : 𝒰ᵢ` is needed as part of the construction of another premise, so it stays.

```agda
  ΠI :
    ∀ ℓ {A B b b'} →
    Γ ⊢ A ∶ 𝒰 ℓ →
    Γ , A ⊢ b ≝ b' ∶ B →
    Γ ⊢ Πi A b ≝ Πi A b' ∶ Πf A B
  ΣI :
    ∀ {ℓ A B a a' b b'} →
    (⊢A : Γ ⊢ A ∶ 𝒰 ℓ) →
    Γ , A ⊢ B ∶ 𝒰 ℓ →
    Γ ⊢ a ≝ a' ∶ A →
    Γ ⊢ b ≝ b' ∶ instantiateExpressionAt zero a B →
    Γ ⊢ Σi a b ≝ Σi a' b' ∶ Σf A B
  +Iˡ :
    ∀ {A a a' B} →
    Γ ⊢ a ≝ a' ∶ A →
    Γ ⊢ +iˡ a ≝ +iˡ a' ∶ +f A B
  +Iʳ :
    ∀ {A B b b'} →
    Γ ⊢ b ≝ b' ∶ B →
    Γ ⊢ +iʳ b ≝ +iʳ b' ∶ +f A B
  ℕIˢ :
    ∀ {n n'} →
    Γ ⊢ n ≝ n' ∶ ℕf →
    Γ ⊢ ℕiˢ n ≝ ℕiˢ n' ∶ ℕf
```

This definitional equality is not obvious from Appendix 2.

```agda
  =I : ∀ {A a a'} →
    Γ ⊢ a ≝ a' ∶ A →
    Γ ⊢ =i a ≝ =i a' ∶ =f A a a'
```

Computation rules:

```agda
  ΠE : ∀ {ℓ A B b a}
    (⊢A : Γ ⊢ A ∶ 𝒰 ℓ) →
    Γ , A ⊢ b ∶ B →
    Γ ⊢ a ∶ A →
    Γ ⊢ Πe (Πi A b) a ≝ instantiateExpressionAt zero a b ∶ instantiateExpressionAt zero a B
  ΣE : ∀ {ℓ A B C g a b} →
    (⊢ΠAB : Γ ⊢ Πf A B ∶ 𝒰 ℓ) →
    Γ , Πf A B ⊢ C ∶ 𝒰 ℓ →
    (⊢A : Γ ⊢ A ∶ 𝒰 ℓ) →
    (⊢B : Γ , A ⊢ B ∶ 𝒰 ℓ) →
    Γ , A , B ⊢ g ∶ instantiateExpressionAt (suc (suc zero)) (Σi (𝓋 (suc zero)) (𝓋 (suc zero))) (weakenExpressionFrom zero (weakenExpressionFrom zero C)) →
    Γ ⊢ a ∶ A →
    Γ ⊢ b ∶ instantiateExpressionAt zero a B →
    Γ ⊢ Σe C g (Σi a b) ≝ instantiateExpressionAt zero a (instantiateExpressionAt zero (weakenExpressionFrom zero b) g) ∶ instantiateExpressionAt zero (Σi a b) C
  +Eˡ : ∀ {ℓ C A B c' d a} →
    (⊢+FAB : Γ ⊢ +f A B ∶ 𝒰 ℓ) →
    Γ , +f A B ⊢ C ∶ 𝒰 ℓ →
    (⊢A : Γ ⊢ A ∶ 𝒰 ℓ) →
    Γ , A ⊢ c' ∶ instantiateExpressionAt (suc zero) (+iˡ (𝓋 zero)) (weakenExpressionFrom zero C) →
    (⊢B : Γ ⊢ B ∶ 𝒰 ℓ) →
    Γ , B ⊢ d ∶ instantiateExpressionAt (suc zero) (+iˡ (𝓋 zero)) (weakenExpressionFrom zero C) →
    Γ ⊢ a ∶ A →
    Γ ⊢ +e C c' d (+iˡ a) ≝ instantiateExpressionAt zero a c' ∶ instantiateExpressionAt zero (+iˡ a) C
```

Instead of something like the above, could simpler computation rules like these work?

```agda
  +Eʳ : ∀ {b B C C[+iʳb] c' d d[b]} →
    Γ ⊢ b ∶ B →
    instantiateExpressionAt zero (+iʳ b) C ≡ C[+iʳb] →
    instantiateExpressionAt zero b d ≡ d[b] →
    Γ ⊢ +e C c' d (+iʳ b) ≝ d[b] ∶ C[+iʳb]
  𝟙E : ∀ {C c' C[𝟙I]} →
    instantiateExpressionAt zero 𝟙i C ≡ C[𝟙I] →
    Γ ⊢ 𝟙e C c' 𝟙i ≝ c' ∶ C[𝟙I]
  ℕEᶻ : ∀ {n C c₀ cₛ C[ℕIZ]} →
    Γ ⊢ n ∶ ℕf →
    instantiateExpressionAt zero ℕiᶻ C ≡ C[ℕIZ] →
    Γ ⊢ ℕe C c₀ cₛ ℕiᶻ ≝ c₀ ∶ C[ℕIZ]
  ℕEˢ : ∀ {n C c₀ cₛ cₛ[n,ℕEn] C[ℕIˢn]} →
    Γ ⊢ n ∶ ℕf →
    instantiateExpressionAt zero n ((instantiateExpressionAt zero (weakenExpressionFrom zero (ℕe C c₀ cₛ n)) cₛ)) ≡ cₛ[n,ℕEn] →
    instantiateExpressionAt zero (ℕiˢ n) C ≡ C[ℕIˢn] →
    Γ ⊢ ℕe C c₀ cₛ (ℕiˢ n) ≝ cₛ[n,ℕEn] ∶ C[ℕIˢn]
  =E : ∀ {a c' c[a] C C[a,a,=Ia]} →
    instantiateExpressionAt zero a c' ≡ c[a] →
    instantiateExpressionAt zero a
      (instantiateExpressionAt zero
        (weakenExpressionFrom zero a)
        ((instantiateExpressionAt zero
          (weakenExpressionFrom zero
            (weakenExpressionFrom zero
              (=i a))) C))) ≡ C[a,a,=Ia] →
    Γ ⊢ =e C c' a a (=i a) ≝ c[a] ∶ C[a,a,=Ia]
```

```agda
Expression' = Expression
{-# DISPLAY Expression _ = Expression' #-}
```
