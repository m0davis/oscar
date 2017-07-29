
module Oscar.Data where

open import Oscar.Prelude
open import Oscar.Data.Maybe public
open import Oscar.Data.ṖropertyEquivalence public
open import Oscar.Data.¶ public

module _ where

  open import Agda.Builtin.List public
    using ()
    renaming ([] to ∅)
    renaming (_∷_ to _,_)
  ⟨_⟩¶ = Agda.Builtin.List.List

  List⟨_⟩ = ⟨_⟩¶

module _ where

  data ¶⟨<_⟩ : ¶ → Ø₀ where
    ∅ : ∀ ..{n} → ¶⟨< ↑ n ⟩
    ↑_ : ∀ ..{n} → ¶⟨< n ⟩ → ¶⟨< ↑ n ⟩

  Fin = ¶⟨<_⟩

  module Fin = ¶⟨<_⟩

module _ where

  data ⟨_⟩¶⟨≤_⟩ {𝔭} (𝔓 : ¶ → Ø 𝔭) : ¶ → Ø 𝔭 where
    ∅ : ⟨ 𝔓 ⟩¶⟨≤ ∅ ⟩
    _,_ : ∀ ..{n} → 𝔓 n → ⟨ 𝔓 ⟩¶⟨≤ n ⟩ → ⟨ 𝔓 ⟩¶⟨≤ ↑ n ⟩

  Vec⟨_⟩ = ⟨_⟩¶⟨≤_⟩

{-
module _ where

  -- m ≤ n, counting down from n-1 to m
  data ⟨_⟩¶⟨_≤_↓⟩ {a} (A : ¶ → Ø a) (m : ¶) : ¶ → Ø a where
    ∅ : ⟨ A ⟩¶⟨ m ≤ m ↓⟩
    _,_ : ∀ {n} → A n → ⟨ A ⟩¶⟨ m ≤ n ↓⟩ → ⟨ A ⟩¶⟨ m ≤ ↑ n ↓⟩

  AList⟨_⟩ = ⟨_⟩¶⟨_≤_↓⟩
-}

module _ where

  -- m ≤ n, counting down from n-1 to m
  data Descender⟨_⟩ {a} (A : ¶ → Ø a) (m : ¶) : ¶ → Ø a where
    ∅ : Descender⟨ A ⟩ m m
    _,_ : ∀ {n} → A n → Descender⟨ A ⟩ m n → Descender⟨ A ⟩ m (↑ n)

  Vec'⟨_⟩ = λ {a} (A : Ø a) N → Descender⟨ (λ _ → A) ⟩ 0 N

module _ where

  data 𝟘 : Ø₀ where

  ¬_ : ∀ {a} (A : Ø a) → Ø a
  ¬_ x = x → 𝟘

module _ where

  open import Agda.Builtin.Unit public
    using ()
    renaming (⊤ to 𝟙)
    renaming (tt to ∅)

module _ where

  open import Agda.Builtin.Bool public
    using ()
    renaming (Bool to 𝟚)
    renaming (false to ∅)
    renaming (true to ∅∅)

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

module Term {𝔭} (𝔓 : Ø 𝔭) where

  mutual

    Terms : ¶ → ¶ → Ø 𝔭
    Terms N n = ⟨ Term n ∞ ⟩¶⟨≤ N ⟩

    data Term (n : ¶) : Ø 𝔭 where
      i : (x : ¶⟨< n ⟩) → Term n
      leaf : Term n
      _fork_ : (s t : Term n) → Term n
      function : 𝔓 → ∀ {N} → Terms N n → Term n

module Substitunction {𝔭} (𝔓 : Ø 𝔭) where

  open Term 𝔓

  Substitunction : ¶ → ¶ → Ø 𝔭
  Substitunction m n = ¶⟨< m ⟩ → Term n

module SubstitunctionOperator {𝔭} (𝔓 : Ø 𝔭) where

  open Substitunction 𝔓

  _⊸_ = Substitunction

module Substitist {𝔭} (𝔓 : Ø 𝔭) where

  open Term 𝔓

  Substitist = flip Descender⟨ (λ n-o → Fin (↑ n-o) × Term n-o) ⟩

module _ where

  data Decidable {a} (A : Ø a) : Ø a where
    ↑_ : A → Decidable A
    ↓_ : ¬ A → Decidable A
