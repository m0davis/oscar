
module Oscar.Data.Term.Injectivity {𝔣} (FunctionName : Set 𝔣) where

open import Oscar.Data.Term.Core FunctionName

open import Data.Fin
open import Data.Nat
open import Data.Vec
open import Relation.Binary.PropositionalEquality

Term-function-inj-FunctionName : ∀ {fn₁ fn₂} {n N₁ N₂} {ts₁ : Vec (Term n) N₁} {ts₂ : Vec (Term n) N₂} → Term.function fn₁ ts₁ ≡ Term.function fn₂ ts₂ → fn₁ ≡ fn₂
Term-function-inj-FunctionName refl = refl

Term-function-inj-VecSize : ∀ {fn₁ fn₂} {n N₁ N₂} {ts₁ : Vec (Term n) N₁} {ts₂ : Vec (Term n) N₂} → Term.function fn₁ ts₁ ≡ Term.function fn₂ ts₂ → N₁ ≡ N₂
Term-function-inj-VecSize refl = refl

Term-function-inj-Vector : ∀ {fn₁ fn₂} {n N} {ts₁ : Vec (Term n) N} {ts₂ : Vec (Term n) N} → Term.function fn₁ ts₁ ≡ Term.function fn₂ ts₂ → ts₁ ≡ ts₂
Term-function-inj-Vector refl = refl

Term-fork-inj-left : ∀ {n} {l₁ r₁ l₂ r₂ : Term n} → l₁ fork r₁ ≡ l₂ fork r₂ → l₁ ≡ l₂
Term-fork-inj-left refl = refl

Term-fork-inj-right : ∀ {n} {l₁ r₁ l₂ r₂ : Term n} → l₁ fork r₁ ≡ l₂ fork r₂ → r₁ ≡ r₂
Term-fork-inj-right refl = refl
