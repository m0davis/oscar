
# Minimum requirements for an implementation of a type theory

```agda
module Minimal where
```

In Appendix 2, an implementation of a type theory for a number of types are given. I wonder if some of them could have been left out and instead defined in the type theory itself.

I'll take it that universes and variables are indispensible to even talk about the formation of types, so I leave that fixed. I also cannot see my way around dispensing with the Π-type: how else will I introduce new types? (actually, I maybe can... see below) I would like then to see if, with just this machinery, I could construct a unit type.

In simplified form, the formation, introduction, and elimination rules for the unit type are


----------- 𝟙-form
Γ ⊢ 𝟙F : 𝒰ᵢ


----------- 𝟙-intro
Γ ⊢ 𝟙I : 𝟙F


 Γ , x : 𝟙 ⊢ C : 𝒰ᵢ      Γ ⊢ a : 𝟙F
------------------------------------- 𝟙-elim
         Γ ⊢ 𝟙E : C[a/x]

```agda
open import Agda.Primitive renaming (_⊔_ to lmax)
```

a few tries at creating the unit type

```agda
𝟙-type : ∀ ℓ-form ℓ-elim ℓ-theory
         → (φ : ∀ (𝟙 : Set ℓ-form)
                → (⋆ : 𝟙)
                → ((C : 𝟙 → Set ℓ-elim) (a : 𝟙) → C a)
                → Set ℓ-theory)
         → Set _
𝟙-type _ _ _ φ = ∀ 𝟙 ⋆ ind₁ → φ 𝟙 ⋆ ind₁

𝟙-type'' : ∀ ℓ
           → (φ : ∀ (𝟙F : Set ℓ)
                  → (𝟙I : 𝟙F)
                  → (𝟙E : (C : 𝟙F → Set ℓ) (a : 𝟙F) → C a)
                  → Set ℓ)
           → Set _
𝟙-type'' _ φ = ∀ 𝟙 ⋆ ind₁ → φ 𝟙 ⋆ ind₁

𝟙-type' : ∀ ℓ-form ℓ-elim ℓ-theory → (∀ _ _ _ → Set ℓ-theory) → Set (lmax (lsuc (lmax ℓ-form ℓ-elim)) ℓ-theory)
𝟙-type' = λ ℓ-form ℓ-elim ℓ-theory φ →
  ∀ (𝟙 : Set ℓ-form) (⋆ : 𝟙)
  → (ind₁ : (C : 𝟙 → Set ℓ-elim) (a : 𝟙) → C a) → φ 𝟙 ⋆ ind₁

test-𝟙-type = 𝟙-type (lsuc lzero) (lsuc lzero) (lsuc (lsuc lzero)) λ 𝟙 ⋆ x →
              𝟙-type (lsuc lzero) lzero (lsuc lzero) λ 𝟙₁ ⋆₁ x₁ →
              {!!}

test-𝟙-type'' = 𝟙-type'' (lsuc (lsuc lzero)) λ 𝟙 ⋆ x →
                𝟙-type'' (lsuc lzero) λ 𝟙₁ ⋆₁ x₁ →
                𝟙-type'' (lzero) λ 𝟙₂ ⋆₂ x₂ →
                {!!}
```

Here I am trying out creating a Π-type.

The Π-type rules are

 Γ ⊢ A : 𝒰ᵢ    Γ , A : 𝒰ᵢ ⊢ B : 𝒰ᵢ
------------------------------------- Π-form
         Γ ⊢ ΠF A B ∶ 𝒰ᵢ

 Γ ⊢ A : 𝒰ᵢ    Γ , x : A ⊢ B : 𝒰ᵢ    Γ , a : A ⊢ b : B
------------------------------------------------------------ Π-intro
                   Γ ⊢ ΠI b : Π A B


 Γ ⊢ A : 𝒰ᵢ    Γ , x : A ⊢ B : 𝒰ᵢ   Γ ⊢ f : Π A B    Γ ⊢ a : A
--------------------------------------------------------------------- Π-elim
 Γ ⊢ ΠE f a : B[a/x]


```agda
Π-type : ∀ ℓ
         → (φ : ∀ (ΠF : (A : Set ℓ) (B : A → Set ℓ) → Set ℓ)
                → (ΠI : (A : Set ℓ)
                        (B : A → Set ℓ)
                        (b : (a : A) → B a)
                      → ΠF A B)
                → (ΠE : (A : Set ℓ)
                        (B : A → Set ℓ)
                        (f : ΠF A B)
                        (a : A)
                      → B a)
                → Set ℓ)
         → Set _
Π-type _ φ = ∀ ΠF ΠI ΠE → φ ΠF ΠI ΠE

test-Π = Π-type (lsuc lzero) λ ΠF ΠI ΠE --
       → ΠF Set λ A
       → ΠF Set λ B
       → ΠE (ΠF {!!} {!!}) -- I need a `Lift` b/c Agda is not so good a recognizing universe cumulativity
            {!!} {!!} {!!} {!!}
```
