
import Oscar.Class.Reflexivity.Function
import Oscar.Class.Transextensionality.Proposequality -- FIXME why not use the instance here?
open import Oscar.Class
open import Oscar.Class.Category
open import Oscar.Class.HasEquivalence
open import Oscar.Class.IsCategory
open import Oscar.Class.IsPrecategory
open import Oscar.Class.Precategory
open import Oscar.Class.Reflexivity
open import Oscar.Class.Transassociativity
open import Oscar.Class.Transextensionality
open import Oscar.Class.Transitivity
open import Oscar.Class.Transleftidentity
open import Oscar.Class.Transrightidentity
open import Oscar.Class.[IsExtensionB]
open import Oscar.Data.Proposequality
open import Oscar.Prelude
open import Oscar.Property.Category.Function
open import Oscar.Property.Setoid.Proposextensequality
open import Oscar.Property.Setoid.Proposequality

module Oscar.Property.Category.Proposequality where

module _
  {a} {A : Ø a}
  where

  instance

    𝓣ransassociativityProposequality : Transassociativity.class Proposequality⟦ A ⟧ Proposequality transitivity
    𝓣ransassociativityProposequality .⋆ ∅ _ _ = !
{-
module _
  {a} {A : Ø a}
  where

  instance

    𝓣ransextensionalityProposequality : Transextensionality.class Proposequality⟦ A ⟧ Proposequality transitivity
    𝓣ransextensionalityProposequality .⋆ ∅ ∅ = !
-}
module _
  {a} {A : Ø a}
  where

  instance

    𝓣ransleftidentityProposequality : Transleftidentity.class Proposequality⟦ A ⟧ Proposequality ε transitivity
    𝓣ransleftidentityProposequality .⋆ {f = ∅} = ∅

module _
  {a} {A : Ø a}
  where

  instance

    𝓣ransrightidentityProposequality : Transrightidentity.class Proposequality⟦ A ⟧ Proposequality ε transitivity
    𝓣ransrightidentityProposequality .⋆ = ∅
{-
module _
  {a} (A : Ø a)
  where

  instance

    HasEquivalenceExtension : ∀ {x y : A} ⦃ _ : [IsExtensionB] B ⦄ → HasEquivalence (Extension B x y) _
    HasEquivalenceExtension = ∁ Proposextensequality
-}
module _
  {a} {A : Ø a}
  where

  instance

    IsPrecategoryProposequality : IsPrecategory Proposequality⟦ A ⟧ Proposequality transitivity
    IsPrecategoryProposequality = ∁

    IsCategoryProposequality : IsCategory Proposequality⟦ A ⟧ Proposequality ε transitivity
    IsCategoryProposequality = ∁

module _
  {a} (A : Ø a)
  where

  PrecategoryProposequality : Precategory _ _ _
  PrecategoryProposequality = ∁ Proposequality⟦ A ⟧ Proposequality transitivity

  CategoryProposequality : Category _ _ _
  CategoryProposequality = ∁ Proposequality⟦ A ⟧ Proposequality ε transitivity
