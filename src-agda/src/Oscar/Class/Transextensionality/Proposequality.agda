
open import Oscar.Prelude
open import Oscar.Class
open import Oscar.Data
open import Oscar.Class.Congruity.Proposequality

module Oscar.Class.Transextensionality.Proposequality where

instance

  [𝓣ransextensionality]Proposequality : ∀
    {a} {A : Ø a}
    {m} {_⊸_ : A → A → Ø m}
    → [𝓣ransextensionality] _⊸_ Proposequality
  [𝓣ransextensionality]Proposequality = ∁

  𝓣ransextensionalityProposequality : ∀
    {a} {A : Ø a}
    {m} {_⊸_ : A → A → Ø m}
    ⦃ _ : 𝓣ransitivity _⊸_ ⦄
    → 𝓣ransextensionality _⊸_ Proposequality
  𝓣ransextensionalityProposequality .𝓣ransextensionality.transextensionality = congruity₂ _
