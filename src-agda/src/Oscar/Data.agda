
module Oscar.Data where

open import Oscar.Prelude
open import Oscar.Data.Maybe public
open import Oscar.Data.ṖropertyEquivalence public
open import Oscar.Data.¶ public
open import Oscar.Data.List public
open import Oscar.Data.Fin public
open import Oscar.Data.Vec public
open import Oscar.Data.Descender public
open import Oscar.Data.𝟘 public
open import Oscar.Data.𝟙 public
open import Oscar.Data.𝟚 public
open import Oscar.Data.Proposequality public

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
