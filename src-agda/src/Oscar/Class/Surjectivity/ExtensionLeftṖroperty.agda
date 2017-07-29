
open import Oscar.Prelude
open import Oscar.Class.Surjectivity

module Oscar.Class.Surjectivity.ExtensionLeftṖroperty where

instance

  [𝓢urjectivity]LeftṖroperty : ∀ {ℓ} {a} {f} {¶ : Set a} {_↦_ : ¶ → ¶ → Set f} → [𝓢urjectivity] _↦_ (Extension $ LeftṖroperty ℓ _↦_)
  [𝓢urjectivity]LeftṖroperty = ∁
