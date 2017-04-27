
module Oscar.Data where

open import Oscar.Prelude

module _ where

  open import Agda.Builtin.Nat public
    using ()
    renaming (zero to ∅)
    renaming (suc to ↑_)

  ¶ = Agda.Builtin.Nat.Nat

module _ where

  open import Agda.Builtin.List public
    using ()
    renaming ([] to ∅)
    renaming (_∷_ to _,_)

  ⟨_⟩¶ = Agda.Builtin.List.List

module _ where

  data ¶⟨<_⟩ : ¶ → Ø₀ where
    ∅ : ∀ ..{n} → ¶⟨< ↑ n ⟩
    ↑_ : ∀ ..{n} → ¶⟨< n ⟩ → ¶⟨< ↑ n ⟩

module _ where

  data ⟨_⟩¶⟨≤_⟩ {𝔭} (𝔓 : ¶ → Ø 𝔭) : ¶ → Ø 𝔭 where
    ∅ : ⟨ 𝔓 ⟩¶⟨≤ ∅ ⟩
    _,_ : ∀ ..{n} → 𝔓 n → ⟨ 𝔓 ⟩¶⟨≤ n ⟩ → ⟨ 𝔓 ⟩¶⟨≤ ↑ n ⟩

module _ where

  data 𝟘 : Ø₀ where

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

module _ where

  infix 4 _≡̇_
  _≡̇_ = Proposextensequality

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
