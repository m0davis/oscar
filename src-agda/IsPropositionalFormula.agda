
module IsPropositionalFormula where

open import OscarPrelude
open import Formula
open import Term
open import PredicateName
open import HasNeitherNor


data IsPropositionalFormula : Formula → Set
 where
  atomic : (𝑃 : PredicateName) → (τs : Terms) → IsPropositionalFormula $ 𝑃[ 𝑃 ♭ τs ]
  logical : {φ₁ : Formula} → IsPropositionalFormula φ₁ → {φ₂ : Formula} → IsPropositionalFormula φ₂ → IsPropositionalFormula (φ₁ ⊗ φ₂)

instance EqIsPropositionalFormula : ∀ {φ} → Eq (IsPropositionalFormula φ)
Eq._==_ EqIsPropositionalFormula (atomic _ _) (atomic _ _ ) = yes refl
Eq._==_ EqIsPropositionalFormula (logical φ₁₁ φ₁₂) (logical φ₂₁ φ₂₂) with φ₁₁ ≟ φ₂₁ | φ₁₂ ≟ φ₂₂
Eq._==_ EqIsPropositionalFormula (logical φ₁₁ φ₁₂) (logical φ₂₁ φ₂₂) | yes refl | yes refl = yes refl
Eq._==_ EqIsPropositionalFormula (logical φ₁₁ φ₁₂) (logical φ₂₁ φ₂₂) | yes refl | no φ₁₂≢φ₂₂ = no λ {refl → φ₁₂≢φ₂₂ refl}
Eq._==_ EqIsPropositionalFormula (logical φ₁₁ φ₁₂) (logical φ₂₁ φ₂₂) | no φ₁₁≢φ₂₁ | _ = no λ {refl → φ₁₁≢φ₂₁ refl}

{-
-- need to use coinduction to prove this
foo : ¬ ∃ λ φ → ∃ λ (p₁ : IsPropositionalFormula φ) → ∃ λ (p₂ : IsPropositionalFormula φ) → p₁ ≢ p₂
foo (atomic x x₁ , atomic .x .x₁ , atomic .x .x₁ , snd₁) = snd₁ refl
foo (logical fst₁ fst₂ , logical fst₃ fst₄ , logical fst₅ fst₆ , snd₁) with fst₃ ≟ fst₅ | fst₄ ≟ fst₆
foo (logical fst₁ fst₂ , logical fst₃ fst₄ , logical .fst₃ .fst₄ , snd₁) | yes refl | (yes refl) = snd₁ refl
foo (logical fst₁ fst₂ , logical fst₃ fst₄ , logical .fst₃ fst₆ , snd₁) | yes refl | (no x₁) = foo (fst₂ , fst₄ , fst₆ , λ xs → x₁ xs)
foo (logical fst₁ fst₂ , logical fst₃ fst₄ , logical fst₅ fst₆ , snd₁) | no x | (yes x₁) = {!!}
foo (logical fst₁ fst₂ , logical fst₃ fst₄ , logical fst₅ fst₆ , snd₁) | no x | (no x₁) = {!!}
foo (quantified x fst₁ , () , fst₃ , snd₁)
-}
