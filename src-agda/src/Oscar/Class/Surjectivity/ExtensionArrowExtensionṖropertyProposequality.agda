
open import Oscar.Prelude
open import Oscar.Class.Surjectivity
open import Oscar.Data.Proposequality

module Oscar.Class.Surjectivity.ExtensionArrowExtensionṖropertyProposequality where

instance

  [𝓢urjectivity]ArrowE : ∀ {ℓ} {a} {f} {t} {¶ : Set a} {Fin : ¶ → Set f} {Term : ¶ → Set t} → [𝓢urjectivity] (Arrow Fin Term) (Extension $ LeftExtensionṖroperty ℓ (Arrow Fin Term) _≡̇_)
  [𝓢urjectivity]ArrowE = ∁
