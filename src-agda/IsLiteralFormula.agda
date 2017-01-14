
module IsLiteralFormula where

open import OscarPrelude
open import PredicateName
open import Term
open import Formula
open import HasNegation

data IsLiteralFormula : Formula → Set
 where
  atomic : (𝑃 : PredicateName) → (τs : Terms) → IsLiteralFormula $ 𝑃[ 𝑃 ♭ τs ]
  logical : (𝑃 : PredicateName) → (τs : Terms) → IsLiteralFormula ∘ ~ $ 𝑃[ 𝑃 ♭ τs ]

eqIsLiteralFormula : ∀ {φ} → (lf₁ lf₂ : IsLiteralFormula φ) → lf₁ ≡ lf₂
eqIsLiteralFormula (atomic _ _) (atomic _ _) = refl
eqIsLiteralFormula (logical _ _) (logical _ _) = refl

instance EqIsLiteralFormula : ∀ {φ} → Eq (IsLiteralFormula φ)
Eq._==_ EqIsLiteralFormula lf₁ lf₂ = yes $ eqIsLiteralFormula lf₁ lf₂
