
open import Oscar.Prelude
open import Oscar.Data
open import Oscar.Class.Congruity

module Oscar.Class.Congruity.Proposequality where

instance

  𝓒ongruityProposequality : ∀ {a b} → 𝓒ongruity Proposequality a b
  𝓒ongruityProposequality .𝓒ongruity.congruity _ ∅ = !

  𝓒ongruity₂Proposequality : ∀ {a b c} → 𝓒ongruity₂ Proposequality a b c
  𝓒ongruity₂Proposequality .𝓒ongruity₂.congruity₂ _ ∅ ∅ = !
