
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

    𝓡eflexivityAList : Reflexivity.class AList
    𝓡eflexivityAList .⋆ = ∅

    𝓣ransitivityAList : Transitivity.class AList
    𝓣ransitivityAList .⋆ f ∅ = f
    𝓣ransitivityAList .⋆ f (x , g) =
      let _∙'_ = λ g f → 𝓣ransitivityAList .⋆ f g in -- FIXME needed to help Agda prove termination
      x , g ∙' f

    𝓣ransitivityAList' : Transitivity.class (flip AList)
    𝓣ransitivityAList' .⋆ f g = transitivity g f

    HasEquivalenceAList : ∀ {m n} → HasEquivalence (AList m n) _
    HasEquivalenceAList = ∁ Proposequality

    𝓣ransassociativityAList : Transassociativity.class AList Proposequality transitivity
    𝓣ransassociativityAList .⋆ f g ∅ = ∅
    𝓣ransassociativityAList .⋆ f g (x , h) = congruity (x ,_) $ 𝓣ransassociativityAList .⋆ _ _ h -- h ⟨∙ _ ⟨∙ _

    𝓣ransassociativityAList' : Transassociativity.class (flip AList) Proposequality transitivity
    𝓣ransassociativityAList' .⋆ f g h = symmetry (transassociativity h g f) -- Sym.[] {!!}

    IsPrecategoryAList : IsPrecategory AList Proposequality transitivity
    IsPrecategoryAList = ∁

    IsPrecategoryAList' : IsPrecategory (flip AList) Proposequality transitivity
    IsPrecategoryAList' = ∁

    𝓣ransleftidentityAList : Transleftidentity.class AList Proposequality ε transitivity
    𝓣ransleftidentityAList .⋆ = ∅

    𝓣ransrightidentityAList : Transrightidentity.class AList Proposequality ε transitivity
    𝓣ransrightidentityAList .⋆ {f = ∅} = ∅
    𝓣ransrightidentityAList .⋆ {f = x , f} rewrite 𝓣ransrightidentityAList .⋆ {f = f} = ∅
    -- 𝓣ransrightidentityAList .⋆ {f = x , f} = congruity (x ,_) (transrightidentity {_∼_ = AList} {_∼̇_ = Proposequality})
    -- 𝓣ransrightidentityAList .⋆ {f = x , f} rewrite (f ∙ ε[ AList ] ≡ f) ∋ transrightidentity {_∼_ = AList} = ∅

    𝓣ransleftidentityAList' : Transleftidentity.class (flip AList) Proposequality ε transitivity
    𝓣ransleftidentityAList' .⋆ = transrightidentity {_∼_ = AList}

    𝓣ransrightidentityAList' : Transrightidentity.class (flip AList) Proposequality ε transitivity
    𝓣ransrightidentityAList' .⋆ = transleftidentity {_∼_ = AList}

    IsCategoryAList : IsCategory AList Proposequality ε transitivity
    IsCategoryAList = ∁

    IsCategoryAList' : IsCategory (flip AList) Proposequality ε transitivity
    IsCategoryAList' = ∁

module _ {a} (A : ¶ → Ø a) where

  private AList = Descender⟨ A ⟩

  PrecategoryAListProposequality : Precategory _ _ _
  PrecategoryAListProposequality = ∁ AList Proposequality transitivity

  CategoryAListProposequality : Category _ _ _
  CategoryAListProposequality = ∁ AList Proposequality ε transitivity

  PrecategoryAList'Proposequality : Precategory _ _ _
  PrecategoryAList'Proposequality = ∁ (flip AList) Proposequality transitivity

  CategoryAList'Proposequality : Category _ _ _
  CategoryAList'Proposequality = ∁ (flip AList) Proposequality ε transitivity
