
open import Oscar.Prelude
open import Oscar.Class
open import Oscar.Class.Congruity
open import Oscar.Class.Reflexivity
open import Oscar.Class.Symmetry
open import Oscar.Class.Transitivity
open import Oscar.Class.HasEquivalence
open import Oscar.Class.Transassociativity
open import Oscar.Class.Transleftidentity
open import Oscar.Class.Transrightidentity
open import Oscar.Class.IsPrecategory
open import Oscar.Class.IsCategory
open import Oscar.Class.Precategory
open import Oscar.Class.Category
open import Oscar.Data.¶
open import Oscar.Data.Descender
open import Oscar.Data.Proposequality
import Oscar.Property.Setoid.Proposequality
import Oscar.Class.Congruity.Proposequality
import Oscar.Class.Transextensionality.Proposequality
import Oscar.Data.Constraint

module Oscar.Property.Category.AListProposequality where

module _ {a} {A : ¶ → Set a} where

  private AList = Descender⟨ A ⟩

  instance

    𝓡eflexivityAList : 𝓡eflexivity AList
    𝓡eflexivityAList .⋆ = ∅

    𝓡eflexivityAList' : 𝓡eflexivity (flip AList)
    𝓡eflexivityAList' .⋆ = reflexivity[ AList ]

    𝓣ransitivityAList : 𝓣ransitivity AList
    𝓣ransitivityAList {x∼y = f} {∅} .⋆ = f
    𝓣ransitivityAList {x∼y = f} {x , g} .⋆ =
      let _∙'_ = λ g f → 𝓣ransitivityAList {x∼y = f} {g} .⋆ in -- FIXME needed to help Agda prove termination
      x , g ∙' f

    𝓣ransitivityAList' : 𝓣ransitivity (flip AList)
    𝓣ransitivityAList' {x∼y = f} {g} .⋆ = transitivity g f

    HasEquivalenceAList : ∀ {m n} → HasEquivalence (AList m n) _
    HasEquivalenceAList = ∁ Proposequality

    [𝓣ransassociativity]AList : [𝓣ransassociativity] AList Proposequality
    [𝓣ransassociativity]AList = ∁

    [𝓣ransassociativity]AList' : [𝓣ransassociativity] (flip AList) Proposequality
    [𝓣ransassociativity]AList' = ∁

    𝓣ransassociativityAList : 𝓣ransassociativity AList Proposequality
    𝓣ransassociativityAList .𝓣ransassociativity.transassociativity f g ∅ = ∅
    𝓣ransassociativityAList .𝓣ransassociativity.transassociativity f g (x , h) = congruity (x ,_) $ h ⟨∙ _ ⟨∙ _

    𝓣ransassociativityAList' : 𝓣ransassociativity (flip AList) Proposequality
    𝓣ransassociativityAList' .𝓣ransassociativity.transassociativity f g h = Sym.[] (transassociativity h g f)

    IsPrecategoryAList : IsPrecategory AList Proposequality
    IsPrecategoryAList = ∁

    IsPrecategoryAList' : IsPrecategory (flip AList) Proposequality
    IsPrecategoryAList' = ∁

    [𝓣ransleftidentity]AList : [𝓣ransleftidentity] AList Proposequality
    [𝓣ransleftidentity]AList = ∁

    [𝓣ransleftidentity]AList' : [𝓣ransleftidentity] (flip AList) Proposequality
    [𝓣ransleftidentity]AList' = ∁

    𝓣ransleftidentityAList : 𝓣ransleftidentity AList Proposequality
    𝓣ransleftidentityAList .𝓣ransleftidentity.transleftidentity = ∅

    [𝓣ransrightidentity]AList : [𝓣ransrightidentity] AList Proposequality
    [𝓣ransrightidentity]AList = ∁

    [𝓣ransrightidentity]AList' : [𝓣ransrightidentity] (flip AList) Proposequality
    [𝓣ransrightidentity]AList' = ∁

    𝓣ransrightidentityAList : 𝓣ransrightidentity AList Proposequality
    𝓣ransrightidentityAList .𝓣ransrightidentity.transrightidentity {f = ∅} = ∅
    𝓣ransrightidentityAList .𝓣ransrightidentity.transrightidentity {f = x , f} rewrite transrightidentity {_∼_ = AList} {_∼̇_ = Proposequality} {f = f} = ∅
    --𝓣ransrightidentityAList .𝓣ransrightidentity.transrightidentity {f = x , f} = congruity (x ,_) (transrightidentity {_∼_ = AList} {_∼̇_ = Proposequality})
    --𝓣ransrightidentityAList .𝓣ransrightidentity.transrightidentity {f = x , f} rewrite (f ∙ ε[ AList ] ≡ f) ∋ transrightidentity {_∼_ = AList} = ∅

    𝓣ransleftidentityAList' : 𝓣ransleftidentity (flip AList) Proposequality
    𝓣ransleftidentityAList' .𝓣ransleftidentity.transleftidentity = transrightidentity {_∼_ = AList}

    𝓣ransrightidentityAList' : 𝓣ransrightidentity (flip AList) Proposequality
    𝓣ransrightidentityAList' .𝓣ransrightidentity.transrightidentity = transleftidentity {_∼_ = AList}

    IsCategoryAList : IsCategory AList Proposequality
    IsCategoryAList = ∁

    IsCategoryAList' : IsCategory (flip AList) Proposequality
    IsCategoryAList' = ∁

module _ {a} (A : ¶ → Ø a) where

  private AList = Descender⟨ A ⟩

  PrecategoryAListProposequality : Precategory _ _ _
  PrecategoryAListProposequality = ∁ AList Proposequality

  CategoryAListProposequality : Category _ _ _
  CategoryAListProposequality = ∁ AList Proposequality

  PrecategoryAList'Proposequality : Precategory _ _ _
  PrecategoryAList'Proposequality = ∁ (flip AList) Proposequality

  CategoryAList'Proposequality : Category _ _ _
  CategoryAList'Proposequality = ∁ (flip AList) Proposequality
