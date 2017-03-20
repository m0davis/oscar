
module Oscar.Data.Term.Substitution.Core {𝔣} (FunctionName : Set 𝔣) where

open import Oscar.Data.Term.Core FunctionName
open import Oscar.Data.Term.Substitution.Core.bootstrap FunctionName public hiding (_◃Term_; _◃VecTerm_)
open import Oscar.Data.Nat.Core
open import Oscar.Data.Fin.Core
open import Oscar.Data.Vec.Core
open import Oscar.Data.Equality.Core
open import Oscar.Data.Product.Core
open import Oscar.Function
open import Oscar.Level

⊸-Property : {ℓ : Level} → ℕ → Set (lsuc ℓ ⊔ 𝔣)
⊸-Property {ℓ} m = ∀ {n} → m ⊸ n → Set ℓ

_≐_ : {m n : ℕ} → m ⊸ n → m ⊸ n → Set 𝔣
f ≐ g = ∀ x → f x ≡ g x

⊸-Extensional : {ℓ : Level} {m : ℕ} → ⊸-Property {ℓ} m → Set (ℓ ⊔ 𝔣)
⊸-Extensional P = ∀ {m f g} → f ≐ g → P {m} f → P g

⊸-ExtentionalProperty : {ℓ : Level} → ℕ → Set (lsuc ℓ ⊔ 𝔣)
⊸-ExtentionalProperty {ℓ} m = Σ (⊸-Property {ℓ} m) ⊸-Extensional
