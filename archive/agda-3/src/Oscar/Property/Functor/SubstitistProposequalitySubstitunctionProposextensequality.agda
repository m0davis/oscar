
open import Oscar.Prelude
open import Oscar.Class
open import Oscar.Class.Reflexivity
open import Oscar.Class.Smap
open import Oscar.Class.Surjextensionality
open import Oscar.Class.Surjidentity
open import Oscar.Class.Surjtranscommutativity
open import Oscar.Class.HasEquivalence
open import Oscar.Class.Transitivity
open import Oscar.Class.Thickandthin
open import Oscar.Class.IsPrefunctor
open import Oscar.Class.IsFunctor
open import Oscar.Data.Maybe
open import Oscar.Data.¶
open import Oscar.Data.Fin
open import Oscar.Data.Proposequality
open import Oscar.Data.Substitunction
open import Oscar.Data.Term
open import Oscar.Data.Substitist
open import Oscar.Data.Descender
import Oscar.Property.Setoid.Proposextensequality
import Oscar.Property.Functor.SubstitunctionExtensionTerm
import Oscar.Property.Category.AListProposequality
import Oscar.Property.Category.ExtensionProposextensequality
import Oscar.Property.Thickandthin.FinFinProposequalityMaybeProposequality
import Oscar.Class.HasEquivalence.Substitunction
import Oscar.Class.Surjection.⋆

module Oscar.Property.Functor.SubstitistProposequalitySubstitunctionProposextensequality where

module _ {𝔭} {𝔓 : Ø 𝔭} where

  open Substitunction 𝔓
  open Term 𝔓
  open Substitist 𝔓

  _for_ : ∀ {n} (t' : Term n) (x : Fin (↑ n)) → Fin (↑ n) → Term n
  (t for x) y = maybe′ ε t (check[ Maybe ] x y)

  instance

    𝓢urjectivitySubstitist,Substitunction : Smap.class Substitist Substitunction ¡ ¡
    𝓢urjectivitySubstitist,Substitunction .⋆ _ _ ∅ = i
    𝓢urjectivitySubstitist,Substitunction .⋆ _ _ ((x , t) , σ) = 𝓢urjectivitySubstitist,Substitunction .⋆ _ _ σ ∙ (t for x)

    𝓢urjextensionalitySubstitist,Substitunction : Surjextensionality.class Substitist Proposequality Substitunction _≈_ ¡ smap
    𝓢urjextensionalitySubstitist,Substitunction .⋆ _ _ _ _ ∅ _ = ∅

    𝓢urjtranscommutativitySubstitist,Substitunction : Surjtranscommutativity.class Substitist Substitunction _≈_ smap transitivity transitivity
    𝓢urjtranscommutativitySubstitist,Substitunction .⋆ ∅ _ _ = ∅
    𝓢urjtranscommutativitySubstitist,Substitunction .⋆ ((π₀ , π₁) , f) g =
      let _⟪∙⟫′_ = flip (𝓢urjtranscommutativitySubstitist,Substitunction .⋆) in -- kludge for Agda's termination checker

        (
            § g ⟪∙⟫ §[ Substitunction ] f
          ∙
            ⟪ g ⟪∙⟫′ f ⟫[ Proposextensequality ]
        )
      ∘
        π₁ for π₀


    IsPrefunctorSubstitist,Substitunction : IsPrefunctor Substitist Proposequality transitivity Substitunction _≈_ transitivity smap
    IsPrefunctorSubstitist,Substitunction = ∁

    𝓢urjidentitySubstitist,Substitunction : Surjidentity.class Substitist Substitunction _≈_ smap ε ε
    𝓢urjidentitySubstitist,Substitunction .⋆ _ = ∅

    IsFunctorSubstitist,Substitunction : IsFunctor Substitist Proposequality ε transitivity Substitunction _≈_ ε transitivity smap
    IsFunctorSubstitist,Substitunction = ∁
