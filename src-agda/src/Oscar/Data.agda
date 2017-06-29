{-# OPTIONS --postfix-projections #-}
module Oscar.Data where

open import Oscar.Prelude

module _ where

  data ¶ : Set where
    ∅ : ¶
    ↑_  : ¶ → ¶

  {-# BUILTIN NATURAL ¶ #-}

  Nat = ¶

  record ℕ : Ø₀ where
    constructor ↑_
    field ⋆ : ¶

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

module _ where

  Extension : ∀ {𝔬} {𝔒 : Ø 𝔬} {𝔭} (𝔓 : 𝔒 → Ø 𝔭) → 𝔒 → 𝔒 → Ø 𝔭
  Extension 𝔓 m n = 𝔓 m → 𝔓 n

module _ where

  _⟨_⟩→_ : ∀ {𝔬} {𝔒 : Ø 𝔬} → 𝔒 → ∀ {𝔭} → (𝔒 → Ø 𝔭) → 𝔒 → Ø 𝔭
  m ⟨ 𝔓 ⟩→ n = Extension 𝔓 m n

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

  data Maybe {a} (A : Ø a) : Ø a where
    ∅ : Maybe A
    ↑_ : A → Maybe A

module _ where

  data Decidable {a} (A : Ø a) : Ø a where
    ↑_ : A → Decidable A
    ↓_ : ¬ A → Decidable A

Arrow : ∀
  {𝔵} {𝔛 : Ø 𝔵}
  {𝔞} (𝔄 : 𝔛 → Ø 𝔞)
  {𝔟} (𝔅 : 𝔛 → Ø 𝔟)
  → 𝔛 → 𝔛
  → Ø 𝔞 ∙̂ 𝔟
Arrow 𝔄 𝔅 x y = 𝔄 x → 𝔅 y

Extended : ∀
    {𝔞} {𝔄 : Ø 𝔞}
    {𝔟} {𝔅 : Ø 𝔟}
    {ℓ} (_≈_ : 𝔅 → 𝔅 → Ø ℓ)
    → (𝔄 → 𝔅) → (𝔄 → 𝔅)
    → Ø 𝔞 ∙̂ ℓ
Extended _≈_ = λ f g → ∀ x → f x ≈ g x

Property : ∀
  {𝔵} {𝔛 : Ø 𝔵}
  {𝔬} (𝔒 : 𝔛 → Ø 𝔬)
  ℓ
  → Ø 𝔵 ∙̂ 𝔬 ∙̂ ↑̂ ℓ
Property 𝔒 ℓ = ∀ {x} → 𝔒 x → Ø ℓ

ExtendedProperty : ∀
  {𝔵} {𝔛 : Ø 𝔵}
  {𝔬} (𝔒 : 𝔛 → Ø 𝔬)
  ℓ
  {ℓ̇} (_↦_ : ∀ {x} → 𝔒 x → 𝔒 x → Ø ℓ̇)
  → Ø 𝔵 ∙̂ 𝔬 ∙̂ ↑̂ ℓ ∙̂ ℓ̇
ExtendedProperty 𝔒 ℓ _↦_ = Σ (Property 𝔒 ℓ) (λ P → ∀ {x} {f g : 𝔒 x} → f ↦ g → P f → P g)

ArrowsourceProperty : ∀
  {𝔵} {𝔛 : Ø 𝔵}
  {𝔬₁} (𝔒₁ : 𝔛 → Ø 𝔬₁)
  {𝔬₂} (𝔒₂ : 𝔛 → Ø 𝔬₂)
  ℓ
  → 𝔛
  → Ø 𝔵 ∙̂ 𝔬₁ ∙̂ 𝔬₂ ∙̂ ↑̂ ℓ
ArrowsourceProperty 𝔒₁ 𝔒₂ ℓ x = Property (Arrow 𝔒₁ 𝔒₂ x) ℓ

ArrowsourceExtendedProperty :
  ∀
    {𝔵} {𝔛 : Ø 𝔵}
    {𝔬₁} (𝔒₁ : 𝔛 → Ø 𝔬₁)
    {𝔬₂} (𝔒₂ : 𝔛 → Ø 𝔬₂)
    ℓ
    → (x : 𝔛) → ∀
      {ℓ̇} (_↦_ : ∀ {y} → Arrow 𝔒₁ 𝔒₂ x y → Arrow 𝔒₁ 𝔒₂ x y → Ø ℓ̇) → Ø 𝔵 ∙̂ 𝔬₁ ∙̂ 𝔬₂ ∙̂ ↑̂ ℓ ∙̂ ℓ̇
ArrowsourceExtendedProperty 𝔒₁ 𝔒₂ ℓ x _↦_ = ExtendedProperty (Arrow 𝔒₁ 𝔒₂ x) ℓ _↦_
