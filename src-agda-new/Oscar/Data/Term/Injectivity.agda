
module Oscar.Data.Term.Injectivity {𝔣} (FunctionName : Set 𝔣) where

open import Oscar.Data.Term FunctionName

open import Data.Fin
open import Data.Nat
open import Data.Vec
open import Relation.Binary.PropositionalEquality

Term-i-inj : ∀ {m} {𝑥₁ 𝑥₂ : Fin m} → i 𝑥₁ ≡ i 𝑥₂ → 𝑥₁ ≡ 𝑥₂
Term-i-inj refl = refl

Term-functionName-inj : ∀ {fn₁ fn₂} {n N₁ N₂} {ts₁ : Vec (Term n) N₁} {ts₂ : Vec (Term n) N₂} → Term.function fn₁ ts₁ ≡ Term.function fn₂ ts₂ → fn₁ ≡ fn₂
Term-functionName-inj refl = refl

Term-functionArity-inj : ∀ {fn₁ fn₂} {n N₁ N₂} {ts₁ : Vec (Term n) N₁} {ts₂ : Vec (Term n) N₂} → Term.function fn₁ ts₁ ≡ Term.function fn₂ ts₂ → N₁ ≡ N₂
Term-functionArity-inj refl = refl

Term-functionTerms-inj : ∀ {fn₁ fn₂} {n N} {ts₁ : Vec (Term n) N} {ts₂ : Vec (Term n) N} → Term.function fn₁ ts₁ ≡ Term.function fn₂ ts₂ → ts₁ ≡ ts₂
Term-functionTerms-inj refl = refl

Term-forkLeft-inj : ∀ {n} {l₁ r₁ l₂ r₂ : Term n} → l₁ fork r₁ ≡ l₂ fork r₂ → l₁ ≡ l₂
Term-forkLeft-inj refl = refl

Term-forkRight-inj : ∀ {n} {l₁ r₁ l₂ r₂ : Term n} → l₁ fork r₁ ≡ l₂ fork r₂ → r₁ ≡ r₂
Term-forkRight-inj refl = refl
