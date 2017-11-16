
open import Oscar.Prelude
open import Oscar.Data.𝟘

module Oscar.Data.Proposequality where

module _ where

  data Proposequality {𝔬} {𝔒 : Ø 𝔬} (𝓞 : 𝔒) : 𝔒 → Ø₀ where
    instance ∅ : Proposequality 𝓞 𝓞

  {-# BUILTIN EQUALITY Proposequality #-}

  Proposequality⟦_⟧ : ∀ {𝔬} (𝔒 : Ø 𝔬) → 𝔒 → 𝔒 → Ø₀
  Proposequality⟦ _ ⟧ = Proposequality

  [Proposequality] : ∀ {𝔬} {𝔒 : Ø 𝔬} → {x y : 𝔒} → Ø₀
  [Proposequality] {x = x} {y = y} = Proposequality x y

module _ where

  infix 4 _≡_
  _≡_ = Proposequality

-- transport : ∀ {a b} {A : Set a} (B : A → Set b) {x y} → x ≡ y → B x → B y
-- transport _ ∅ = ¡

-- transport₂ : ∀ {a b c} {A : Set a} {B : Set b} (C : A → B → Set c) {x₁ x₂ y₁ y₂} → x₁ ≡ x₂ → y₁ ≡ y₂ → C x₁ y₁ → C x₂ y₂
-- transport₂ _ ∅ ∅ = ¡

module _ where

  Proposantiequality : ∀ {𝔬} {𝔒 : Ø 𝔬} → 𝔒 → 𝔒 → Ø₀
  Proposantiequality x y = Proposequality x y → 𝟘

  Proposantiequality⟦_⟧ : ∀ {𝔬} (𝔒 : Ø 𝔬) → 𝔒 → 𝔒 → Ø₀
  Proposantiequality⟦ _ ⟧ = Proposantiequality

  infix 4 _≢_
  _≢_ = Proposantiequality

module _ where

  Proposextensequality : ∀ {𝔬} {𝔒 : Ø 𝔬} {𝔭} {𝔓 : 𝔒 → Ø 𝔭} → ((𝓞 : 𝔒) → 𝔓 𝓞) → ((𝓞 : 𝔒) → 𝔓 𝓞) → Ø 𝔬
  Proposextensequality 𝓟₁ 𝓟₂ = ∀ 𝓞 → Proposequality (𝓟₁ 𝓞) (𝓟₂ 𝓞)

  Proposextensequality⟦_⟧ : ∀ {𝔬} {𝔒 : Ø 𝔬} {𝔭} (𝔓 : 𝔒 → Ø 𝔭) → ((𝓞 : 𝔒) → 𝔓 𝓞) → ((𝓞 : 𝔒) → 𝔓 𝓞) → Ø 𝔬
  Proposextensequality⟦ _ ⟧ = Proposextensequality

  Proposextensequality[_/_] : ∀ {𝔬} (𝔒 : Ø 𝔬) {𝔭} (𝔓 : 𝔒 → Ø 𝔭) → ((𝓞 : 𝔒) → 𝔓 𝓞) → ((𝓞 : 𝔒) → 𝔓 𝓞) → Ø 𝔬
  Proposextensequality[ _ / _ ] = Proposextensequality

module _ where

  infix 4 _≡̇_
  _≡̇_ = Proposextensequality

  infix 4 ≡̇⟦⟧-syntax
  ≡̇⟦⟧-syntax = Proposextensequality⟦_⟧
  syntax ≡̇⟦⟧-syntax t x y = x ≡̇⟦ t ⟧ y
