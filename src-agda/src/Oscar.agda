-- the latest developments are tested here

module Oscar where

open import Oscar.Prelude
open import Oscar.Class
open import Oscar.Data
open import Oscar.Property
open import Test

module ṖropertyFactsSubstitunction {𝔭} (𝔓 : Ø 𝔭) (ℓ : Ł) where
  open Term 𝔓
  open Substitunction 𝔓

  test-epfs⋆ : ∀ {x y}
             → Substitunction x y → ArrowṖroperty ℓ Fin Term x → ArrowṖroperty ℓ Fin Term y
  test-epfs⋆ = surjectextensivity

  test-epfs : ∀ {x y}
            → Arrow Fin Term x y → ExtensionṖroperty ℓ (Arrow Fin Term x) (Pointwise Proposequality) → ArrowExtensionṖroperty ℓ Fin Term _≡_ y
  test-epfs = surjectextensivity

  test-epfs2 : ∀ {x y}
             → Arrow Fin Term x y → ≡-ExtensionṖroperty ℓ Fin Term x → ≡-ExtensionṖroperty ℓ Fin Term y
  test-epfs2 = surjectextensivity

  fact1⋆ : ∀ {m} (s t : Term m)
         → ≡-Unifies₀⟦ Substitunction ⟧ s t ≈ ≡-Unifies₀ t s
  fact1⋆ = symmetrical

  fact1 : ∀ {m} (s t : Term m)
        → ≡-ExtensionalUnifies {𝔄 = Fin} s t ≈ ≡-ExtensionalUnifies t s
  fact1 = symmetrical

  Properties-fact1'⋆ : ∀ {n} → 𝓹roperfact1 (≡-Unifies₀⟦ Arrow Fin Term ⟧) (_fork_ {n = n})
  Properties-fact1'⋆ = properfact1

  Properties-fact1' : ∀ {n} → 𝓹roperfact1 (≡-ExtensionalUnifies {𝔄 = Fin}) (_fork_ {n = n})
  Properties-fact1' = properfact1

  fact3⋆ : ∀ {m} {P : Ṗroperty ℓ (Arrow Fin Term m)}
         → P ≈ i ◃ P
  fact3⋆ = factsurj3

  fact3 : ∀ {m} {P : ExtensionṖroperty ℓ (Arrow Fin Term m) (Pointwise Proposequality)}
        → P ≈ i ◃ P
  fact3 .π₀ .π₀ = ¡ , ¡

  fact4⋆ : ∀{m n} (P : LeftṖroperty ℓ (Arrow Fin Term) m) (f : _ → Term n)
         → Nothing P → Nothing (f ◃ P)
  fact4⋆ _ _ nop = nop

  fact4 : ∀{m n} (P : LeftExtensionṖroperty ℓ (Arrow Fin Term) Proposextensequality m) (f : _ → Term n)
        → Nothing P → Nothing (f ◃ P)
  fact4 _ _ nop = nop

  fact5⋆ : ∀{m n} {P Q : ArrowṖroperty ℓ Fin Term m} (f : Arrow Fin Term m n)
         → P ≈ Q → f ◃ P ≈ f ◃ Q
  fact5⋆ = surjectextenscongruity

  fact5 : ∀{m n} {P Q : LeftExtensionṖroperty ℓ Substitunction Proposextensequality m} (f : Arrow Fin Term m n)
        → P ≈ Q → f ◃ P ≈ f ◃ Q
  fact5 = surjectextenscongruity

  fact6 : ∀{m n} (P : LeftExtensionṖroperty ℓ (Arrow Fin Term) _≈_ m) {f g : Arrow Fin Term m n}
        → f ≈ g → f ◃ P ≈ g ◃ P
  fact6 P f≐g .π₀ .π₀ {f = h} = π₁ P (congruity (surjectivity h) ∘ f≐g) , π₁ P (symmetry (congruity (surjectivity h) ∘ f≐g))

  left-identity-∧ : ∀ {m} (P : LeftṖroperty ℓ Substitunction m)
                  → ➊ ∧ P ≈ P
  left-identity-∧ P .π₀ = π₁ , (lift ∅ ,_)

  left-identity-∧-ext : ∀ {m} (P : LeftExtensionṖroperty ℓ Substitunction Proposextensequality m)
                      → ➊ ∧ P ≈ P
  left-identity-∧-ext P .π₀ .π₀ = π₁ , (lift ∅ ,_)
