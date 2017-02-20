--{-# OPTIONS --allow-unsolved-metas #-}
module Theorem1 where

open import OscarPrelude

open import HasSatisfaction
open import HasSubstantiveDischarge

open import LiteralFormula

open import 𝑱udgement
open import HasSalvation

open import Membership

open import Interpretation
open import HasNegation

open import IsLiteralFormula

Theorem1 : (Φ : 𝑱udgement LiteralFormula) → ⊨ Φ ↔ ▷ Φ
Theorem1 Φ@(χs ⊢ ι) = Theorem1a , Theorem1b where
  Theorem1a : ⊨ Φ → ▷ Φ
  Theorem1a ⊨Φ with ▷? Φ
  … | yes ▷Φ = ▷Φ
  … | no ⋫Φ =
    let I , I⊨χs , I⊭ι = Lemma1a in
      ⊥-elim ∘ I⊭ι $ ⊨Φ I I⊨χs
    where
    Lemma1a : ∃ λ I → I ⊨ χs × I ⊭ ι
    Lemma1a = {!!}

{-
To construct the interpretation, consider a unique list, τ₀, τ₁, …, τₙ, of terms in ι ∷ χs. For each term, τ, we find <TODO> interpretations, 𝓘, such that for any I ∈ 𝓘, and any i ∈ 0, …, n, τ⟦ I ⟧ τᵢ = i. For each formula φ ∈ ι ∷ χs, we find <TODO> an interpretation I ∈ 𝓘 such that 𝑃⟦ I ⟧ φ = true when φ ∈ χs and 𝑃⟦ I ⟧ φ = false when φ = ι.
For all terms in ι ∷ χs, find a coding into Nat that uniquely determines each term. To do this, compute the maximum functional depth of terms, D, the maximal arity of terms, A, the maximal function name, F, and the maximal variable name, V. Each term can then be coded into Fin V + (D₀ = F + F * V + F * V ^ 2 + ... + F * V ^ A) + (D₀ ...
Encode each term in a discrimination network. Each new term stored is assigned a unique id
-}

  Theorem1b : ▷ Φ → ⊨ Φ
  Theorem1b (left ◁χs) I I⊨χs = {!!}
  Theorem1b (right χs≽ι) I I⊨χs = {!!}
