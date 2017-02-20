
module Binding where

open import Agda.Primitive

data Freer {ℓ} (F : Set ℓ → Set (lsuc ℓ)) (A : Set (lsuc ℓ)) : Set (lsuc ℓ) where
  pure : A → Freer F A
  free : ∀ {a : Set ℓ} → (a → Freer F A) → F a → Freer F A
