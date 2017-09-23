
open import Oscar.Prelude
open import Oscar.Data.¶

module Oscar.Data.Fin where

data ¶⟨<_⟩ : ¶ → Ø₀ where
  ∅ : ∀ {n} → ¶⟨< ↑ n ⟩
  ↑_ : ∀ {n} → ¶⟨< n ⟩ → ¶⟨< ↑ n ⟩

Fin = ¶⟨<_⟩

module Fin = ¶⟨<_⟩
