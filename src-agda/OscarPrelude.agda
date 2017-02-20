
module OscarPrelude where

open import Prelude public
  renaming (_==_ to _≟_) -- TODO ask Agda to rename Eq._==_ to Eq._≟_
  renaming (force to force!) -- needed by ∞Delay
  renaming (forceLemma to force!Lemma)

_≢_ : ∀ {ℓ} {A : Set ℓ} → A → A → Set ℓ
x ≢ y = ¬ (x ≡ y)

infix 0 _↔_
_↔_ : {ℓ¹ : Level} → Set ℓ¹ → {ℓ² : Level} → Set ℓ² → Set (ℓ¹ ⊔ ℓ²)
P ↔ Q = (P → Q) × (Q → P)

infix 0 _←⊗→_
_←⊗→_ : {ℓ¹ : Level} → Set ℓ¹ → {ℓ² : Level} → Set ℓ² → Set (ℓ¹ ⊔ ℓ²)
P ←⊗→ Q = (P → ¬ Q) × (Q → ¬ P)

∃ : ∀ {ℓᴬ ℓᴮ} {A : Set ℓᴬ} (B : A → Set ℓᴮ) → Set (ℓᴬ ⊔ ℓᴮ)
∃ = Σ _

∄ : ∀ {ℓᴬ ℓᴮ} {A : Set ℓᴬ} (B : A → Set ℓᴮ) → Set (ℓᴬ ⊔ ℓᴮ)
∄ = ¬_ ∘ ∃

infixl 4 _⊎_
_⊎_ = Either

{-# DISPLAY Either = _⊎_ #-}

--open import Agda.Builtin.Size public
open import Size public

open import Control.Monad.State public
open import Control.Monad.Identity public
open import Container.Traversable public
open import Container.List renaming (_∈_ to _∈Container_) public

sequence : ∀ {a b} {A : Set a} {F : Set a → Set b} ⦃ _ : Applicative F ⦄ → List (F A) → F ⊤′
sequence [] = pure tt
sequence (x ∷ xs) = x *> sequence xs

open import Tactic.Nat public

open import Tactic.Deriving.Eq public
