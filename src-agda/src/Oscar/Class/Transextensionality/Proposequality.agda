
open import Oscar.Prelude
open import Oscar.Class
open import Oscar.Class.Congruity
open import Oscar.Class.Transextensionality
open import Oscar.Class.Transitivity
open import Oscar.Data.Proposequality
import Oscar.Class.Congruity.Proposequality

module Oscar.Class.Transextensionality.Proposequality where

instance

  𝓣ransextensionalityProposequality : ∀
    {a} {A : Ø a}
    {m} {_⊸_ : A → A → Ø m}
    ⦃ _ : Transitivity.class _⊸_ ⦄
    → Transextensionality.class _⊸_ Proposequality transitivity
  𝓣ransextensionalityProposequality .⋆ = congruity₂ _
