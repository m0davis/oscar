
open import Oscar.Prelude
open import Oscar.Data.Maybe
open import Oscar.Class.Fmap
open import Oscar.Class.Pure
open import Oscar.Class.Apply
open import Oscar.Class.Bind

module Oscar.Property.Monad.Maybe where

instance

  𝓕mapMaybe : ∀ {𝔬₁ 𝔬₂} → 𝓕map Maybe 𝔬₁ 𝔬₂
  𝓕mapMaybe .𝓕map.fmap f ∅ = ∅
  𝓕mapMaybe .𝓕map.fmap f (↑ x) = ↑ f x

  𝓟ureMaybe : ∀ {𝔬} → 𝓟ure (Maybe {𝔬})
  𝓟ureMaybe .𝓟ure.pure = ↑_

  𝓐pplyMaybe : ∀ {𝔬₁ 𝔬₂} → 𝓐pply Maybe 𝔬₁ 𝔬₂
  𝓐pplyMaybe .𝓐pply.apply ∅ x = ∅
  𝓐pplyMaybe .𝓐pply.apply (↑ f) x = fmap f x

  𝓑indMaybe : ∀ {𝔬₁ 𝔬₂} → 𝓑ind Maybe 𝔬₁ 𝔬₂
  𝓑indMaybe .𝓑ind.bind ∅ _ = ∅
  𝓑indMaybe .𝓑ind.bind (↑ x) f = f x
