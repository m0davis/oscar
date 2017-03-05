
module Oscar.Data.Term.AlphaConversion {𝔣} (FunctionName : Set 𝔣) where

open import Oscar.Data.Term.Core FunctionName

open import Oscar.Data.Fin.Core
open import Oscar.Data.Vec.Core

mutual

  _◂_ : ∀ {n m} → (Fin n → Fin m) → Term n → Term m
  _◂_ x (i x₁) = i (x x₁)
  _◂_ x leaf = leaf
  _◂_ x (x₁ fork x₂) = (x ◂ x₁) fork (x ◂ x₂)
  _◂_ x (function x₁ x₂) = function x₁ (x ◂s x₂)

  _◂s_ : ∀ {n m N} → (Fin n → Fin m) → Vec (Term n) N → Vec (Term m) N
  _◂s_ x [] = []
  _◂s_ x (x₁ ∷ x₂) = x ◂ x₁ ∷ x ◂s x₂
