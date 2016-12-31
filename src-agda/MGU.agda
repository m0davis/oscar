
module MGU where

--open import Agda.Builtin.Nat using () renaming (Nat to ℕ)
open import Agda.Primitive
open import Agda.Builtin.Equality

open import Prelude.Product using (Σ; _,_; fst; snd; _×_)
open import Prelude.Equality using (_≡_; eqReasoningStep; _∎; sym; trans; cong)
open import Prelude.Function using (_∘_)
open import Prelude.Empty using (⊥)
open import Prelude.Sum using () renaming (Either to _⊎_)
open import Prelude.Maybe using (Maybe; just; nothing)

∃ : ∀ {a b} {A : Set a} (B : A → Set b) → Set (a ⊔ b)
∃ = Σ _

open import Prelude using (_$_)

record MGU ℓⁱ ℓⱽ ℓᵀ ℓˢ : Set (lsuc (ℓⁱ ⊔ ℓⱽ ⊔ ℓᵀ ⊔ ℓˢ)) where
  field
    𝓲
      : Set ℓⁱ

    𝓥 -- variables
      : 𝓲 → Set ℓⱽ

    𝓣 -- terms
      : 𝓲 → Set ℓᵀ

  -- substitution
  _↦_ : (s t : 𝓲) → Set (ℓⱽ ⊔ ℓᵀ)
  _↦_ s t = 𝓥 s → 𝓣 t

  infix 14 _≐_
  _≐_ : {s t : 𝓲} → s ↦ t → s ↦ t → Set (ℓⱽ ⊔ ℓᵀ)
  _≐_ f g = ∀ x → f x ≡ g x

  field
    -- substitution applied to a term
    _◃_ : ∀ {s t} → s ↦ t → 𝓣 s → 𝓣 t
    -- applying extentionally-equal subsitutions preserves equality of terms
    ◃ext : ∀ {s t} {f g : s ↦ t} → f ≐ g → ∀ t → f ◃ t ≡ g ◃ t

  _◇_ : ∀ {r s t : 𝓲} → (f : s ↦ t) (g : r ↦ s) → r ↦ t
  _◇_ f g = (f ◃_) ∘ g

  field
    𝓢 : 𝓲 → 𝓲 → Set ℓˢ
    sub : ∀ {s t} → 𝓢 s t → s ↦ t
    mgu : ∀ {m} → (s t : 𝓣 m) → Maybe (∃ (𝓢 m))

  Property⋆ : ∀ {ℓ} → 𝓲 → Set (lsuc ℓ ⊔ ℓⁱ ⊔ ℓⱽ ⊔ ℓᵀ)
  Property⋆ {ℓ} s = ∀ {t} → s ↦ t → Set ℓ

  Property : ∀ {ℓ} → 𝓲 → Set (lsuc ℓ ⊔ ℓⁱ ⊔ ℓⱽ ⊔ ℓᵀ)
  Property {ℓ} s = Σ (Property⋆ {ℓ} s) λ P → ∀ {s f g} → f ≐ g → P {s} f → P g

  Nothing : ∀ {ℓ m} → (P : Property {ℓ} m) → Set (ℓ ⊔ ℓⁱ ⊔ ℓⱽ ⊔ ℓᵀ)
  Nothing P = ∀ {n} f → fst P {n} f → ⊥

  Unifies : ∀ {i} (t₁ t₂ : 𝓣 i) → Property i
  Unifies t₁ t₂ = (λ {_} f → f ◃ t₁ ≡ f ◃ t₂) , λ {_} {f} {g} f≐g f◃t₁=f◃t₂ →
      g ◃ t₁
    ≡⟨ sym (◃ext f≐g t₁) ⟩
      f ◃ t₁
    ≡⟨ f◃t₁=f◃t₂ ⟩
      f ◃ t₂
    ≡⟨ ◃ext f≐g t₂ ⟩
      g ◃ t₂
    ∎

  _≤_ : ∀ {m n n'} (f : m ↦ n) (g : m ↦ n') → Set (ℓⱽ ⊔ ℓᵀ)
  _≤_ f g = ∃ λ f' → f ≐ (f' ◇ g)

{-
  Max : ∀ {ℓ m} (P : Property {ℓ} m) → Property m
  Max P' =
    let open Σ P' using () renaming (fst to P; snd to Peq) in
    let lemma1 : {m : 𝓲} {f : _ ↦ m} {g : _ ↦ m} →
                 f ≐ g →
                 P f × ({n : 𝓲} (f' : _ ↦ n) → P f' → f' ≤ f) →
                 P g × ({n : 𝓲} (f' : _ ↦ n) → P f' → f' ≤ g)
        lemma1 {_} {_} {g} f≐g = λ { (Pf , MaxPf) →
          Peq f≐g Pf , λ {_} →
            let lemma2 : ∀ {n} f' → P {n} f' → ∃ λ f0 → f' ≐ (f0 ◇ g)
                lemma2 f' Pf' =
                  let f0 = fst (MaxPf f' Pf')
                      f'≐f0◇f = snd (MaxPf f' Pf') in
                  f0 , λ x → trans (f'≐f0◇f x) (cong (f0 ◃_) (f≐g x)) in
            lemma2 } in
    --(λ {_} f → P f × (∀ {n} f' → P {n} f' → f' ≤ f)) , λ {_} {_} {_} → lemma1
    (λ f → P f × (∀ {n} f' → P {n} f' → f' ≤ f)) , lemma1
-}

  Max : ∀ {ℓ m} (P : Property {ℓ} m) → Property⋆ m
  Max P' =
    let open Σ P' using () renaming (fst to P) in
    (λ f → P f × (∀ {n} f' → P {n} f' → f' ≤ f))

  field
{-
    mgu-c : ∀ {m} (t₁ t₂ : 𝓣 m) →
            (∃ λ n → ∃ λ σ → fst (Max (Unifies t₁ t₂)) (sub σ) × mgu t₁ t₂ ≡ just (n , σ))
            ⊎ (Nothing (Unifies t₁ t₂)                         × mgu t₁ t₂ ≡ nothing)

-}
    mgu-c : ∀ {m} (t₁ t₂ : 𝓣 m) →
            (∃ λ n → ∃ λ σ → (Max (Unifies t₁ t₂)) (sub σ) × mgu t₁ t₂ ≡ just (n , σ))
            ⊎ (Nothing (Unifies t₁ t₂)                     × mgu t₁ t₂ ≡ nothing)

{-
    -- trivial substitution
    -- ▹ : ∀ {s t} → (𝓥 s → 𝓥 t) → s ↦ t

  ≐-cong : ∀ {m n o} {f : m ↦ n} {g} (h : _ ↦ o) → f ≐ g → (h ◇ f) ≐ (h ◇ g)
  ≐-cong h f≐g t = cong (h ◃_) (f≐g t)

  ≐-sym : ∀ {m n} {f : m ↦ n} {g} → f ≐ g → g ≐ f
  ≐-sym f≐g = sym ∘ f≐g
-}
