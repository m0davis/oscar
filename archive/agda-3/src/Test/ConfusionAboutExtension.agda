
import Oscar.Class.Transextensionality.Proposequality -- FIXME why not use the instance here?
open import Oscar.Class
open import Oscar.Class.IsPrecategory
open import Oscar.Class.Transextensionality
open import Oscar.Class.Transitivity
open import Oscar.Data.Proposequality
open import Oscar.Prelude
open import Oscar.Property.Setoid.Proposequality

module Test.ConfusionAboutExtension where

module _
  {a} {A : Ø a}
  where

  instance

    𝓣ransextensionalityProposequality : Transextensionality.class Proposequality⟦ A ⟧ Proposequality transitivity
    -- 𝓣ransextensionalityProposequality = Oscar.Class.Transextensionality.Proposequality.𝓣ransextensionalityProposequality -- using this instead avoids the below-mentioned errors
    𝓣ransextensionalityProposequality .⋆ ∅ ∅ = !

module _
  {a} {A : Ø a}
  where

  testme : Transextensionality.class Proposequality⟦ A ⟧ (Proposequality) (transitivity)
  testme = ! -- errors

  instance

    IsPrecategoryExtension : IsPrecategory Proposequality⟦ A ⟧ Proposequality transitivity
    IsPrecategoryExtension .IsPrecategory.`𝓣ransextensionality = {!!!} -- FIXME I'd like to use instance search to find this instance, but this errors b/c of
    IsPrecategoryExtension .IsPrecategory.`𝓣ransassociativity = magic
