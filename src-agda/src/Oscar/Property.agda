--{-# OPTIONS --show-implicit #-}
{-# OPTIONS --postfix-projections #-}
--{-# OPTIONS -v30 #-}
{-# OPTIONS --rewriting #-}
module Oscar.Property where

open import Oscar.Prelude
open import Oscar.Class
open import Oscar.Data

-- SetoidProposequality
module _ where

  module _ {𝔬} {𝔒 : Ø 𝔬} where

    instance

      𝓡eflexivityProposequality : 𝓡eflexivity Proposequality⟦ 𝔒 ⟧
      𝓡eflexivityProposequality .𝓡eflexivity.reflexivity = !

      𝓢ymmetryProposequality : 𝓢ymmetry Proposequality⟦ 𝔒 ⟧
      𝓢ymmetryProposequality .𝓢ymmetry.symmetry ∅ = !

      𝓣ransitivityProposequality : 𝓣ransitivity Proposequality⟦ 𝔒 ⟧
      𝓣ransitivityProposequality .𝓣ransitivity.transitivity ∅ = ¡

      IsEquivalenceProposequality : IsEquivalence Proposequality⟦ 𝔒 ⟧
      IsEquivalenceProposequality = ∁

  module _ {𝔬} (𝔒 : Ø 𝔬) where

    SetoidProposequality : Setoid _ _
    SetoidProposequality = ∁ Proposequality⟦ 𝔒 ⟧

module _ where

  instance

    𝓒ongruityProposequality : ∀ {a b} → 𝓒ongruity Proposequality a b
    𝓒ongruityProposequality .𝓒ongruity.congruity _ ∅ = !

    𝓒ongruity₂Proposequality : ∀ {a b c} → 𝓒ongruity₂ Proposequality a b c
    𝓒ongruity₂Proposequality .𝓒ongruity₂.congruity₂ _ ∅ ∅ = !

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

-- SetoidProposextensequality
module _ where

  module _ {𝔬} {𝔒 : Ø 𝔬} {𝔭} {𝔓 : 𝔒 → Ø 𝔭} where

    instance

      𝓡eflexivityProposextensequality : 𝓡eflexivity Proposextensequality⟦ 𝔓 ⟧
      𝓡eflexivity.reflexivity 𝓡eflexivityProposextensequality _ = ∅

      𝓢ymmetryProposextensequality : 𝓢ymmetry Proposextensequality⟦ 𝔓 ⟧
      𝓢ymmetry.symmetry 𝓢ymmetryProposextensequality f₁≡̇f₂ x rewrite f₁≡̇f₂ x = ∅

      𝓣ransitivityProposextensequality : 𝓣ransitivity Proposextensequality⟦ 𝔓 ⟧
      𝓣ransitivity.transitivity 𝓣ransitivityProposextensequality f₁≡̇f₂ f₂≡̇f₃ x rewrite f₁≡̇f₂ x = f₂≡̇f₃ x

      IsEquivalenceProposextensequality : IsEquivalence Proposextensequality⟦ 𝔓 ⟧
      IsEquivalenceProposextensequality = ∁

  module _ {𝔬} {𝔒 : Ø 𝔬} {𝔭} (𝔓 : 𝔒 → Ø 𝔭) where

    SetoidProposextensequality : Setoid _ _
    SetoidProposextensequality = ∁ Proposextensequality⟦ 𝔓 ⟧

module _ where

  instance

    𝓒̇ongruityProposextensequality : ∀ {a b} → 𝓒̇ongruity a b Proposextensequality
    𝓒̇ongruity.ċongruity 𝓒̇ongruityProposextensequality _ f≡̇g x rewrite f≡̇g x = ∅

module _ where

  module _
    {a}
    where

    instance

      𝓡eflexivityFunction : 𝓡eflexivity Function⟦ a ⟧
      𝓡eflexivity.reflexivity 𝓡eflexivityFunction = ¡

      𝓣ransitivityFunction : 𝓣ransitivity Function⟦ a ⟧
      𝓣ransitivity.transitivity 𝓣ransitivityFunction f g = g ∘ f

-- CategoryExtensionProposextensequality
module _ where

  module _
    {a} {A : Ø a} {b} {B : A → Ø b}
    where

    instance

      𝓡eflexivityExtension : 𝓡eflexivity (Extension B)
      𝓡eflexivity.reflexivity 𝓡eflexivityExtension = ¡

      𝓣ransitivityExtension : 𝓣ransitivity (Extension B)
      𝓣ransitivity.transitivity 𝓣ransitivityExtension f g = g ∘ f

      [𝓣ransassociativity]ExtensionProposextensequality : [𝓣ransassociativity] (Extension B) Proposextensequality
      [𝓣ransassociativity]ExtensionProposextensequality = ∁

      𝓣ransassociativityExtensionProposextensequality : 𝓣ransassociativity (Extension B) Proposextensequality
      𝓣ransassociativityExtensionProposextensequality .𝓣ransassociativity.transassociativity _ _ _ _ = !

      [𝓣ransextensionality]ExtensionProposextensequality : [𝓣ransextensionality] (Extension B) Proposextensequality
      [𝓣ransextensionality]ExtensionProposextensequality = ∁

      𝓣ransextensionalityExtensionProposextensequality : 𝓣ransextensionality (Extension B) Proposextensequality
      𝓣ransextensionalityExtensionProposextensequality .𝓣ransextensionality.transextensionality {f₂ = f₂} f₁≡̇f₂ g₁≡̇g₂ x rewrite f₁≡̇f₂ x = g₁≡̇g₂ (f₂ x)

      [𝓣ransleftidentity]ExtensionProposextensequality : [𝓣ransleftidentity] (Extension B) Proposextensequality
      [𝓣ransleftidentity]ExtensionProposextensequality = ∁

      𝓣ransleftidentityExtensionProposextensequality : 𝓣ransleftidentity (Extension B) Proposextensequality
      𝓣ransleftidentityExtensionProposextensequality .𝓣ransleftidentity.transleftidentity _ = !

      [𝓣ransrightidentity]ExtensionProposextensequality : [𝓣ransrightidentity] (Extension B) Proposextensequality
      [𝓣ransrightidentity]ExtensionProposextensequality = ∁

      𝓣ransrightidentityExtensionProposextensequality : 𝓣ransrightidentity (Extension B) Proposextensequality
      𝓣ransrightidentityExtensionProposextensequality .𝓣ransrightidentity.transrightidentity _ = !

      HasEquivalenceExtension : ∀ {x y : A} ⦃ _ : [IsExtensionB] B ⦄ → HasEquivalence (Extension B x y) _
      HasEquivalenceExtension = ∁ Proposextensequality

  module _
    {a} {A : Ø a} {b} {B : A → Ø b}
    where

    instance

      IsPrecategoryExtension : IsPrecategory (Extension B) Proposextensequality
      IsPrecategoryExtension = ∁

      IsCategoryExtension : IsCategory (Extension B) Proposextensequality
      IsCategoryExtension = ∁

  module _
    {a} {A : Ø a} {b} (B : A → Ø b)
    where

    PrecategoryExtension : Precategory _ _ _
    PrecategoryExtension = ∁ (Extension B) Proposextensequality

    CategoryExtension : Category _ _ _
    CategoryExtension = ∁ (Extension B) Proposextensequality

module _
  {𝔬} {𝔒 : Ø 𝔬}
  where
  instance
    𝓢urjectionIdentity : 𝓢urjection 𝔒 𝔒
    𝓢urjectionIdentity .𝓢urjection.surjection = ¡

module _ {𝔭} {𝔓 : Ø 𝔭} where

  open Substitunction 𝔓
  open Term 𝔓

  private

    mutual

      𝓼urjectivitySubstitunctionExtensionTerm : 𝓼urjectivity Substitunction (Extension Term)
      𝓼urjectivitySubstitunctionExtensionTerm σ (i x) = σ x
      𝓼urjectivitySubstitunctionExtensionTerm σ leaf = leaf
      𝓼urjectivitySubstitunctionExtensionTerm σ (τ₁ fork τ₂) = 𝓼urjectivitySubstitunctionExtensionTerm σ τ₁ fork 𝓼urjectivitySubstitunctionExtensionTerm σ τ₂
      𝓼urjectivitySubstitunctionExtensionTerm σ (function p τs) = function p (𝓼urjectivitySubstitunctionExtensionTerms σ τs)

      𝓼urjectivitySubstitunctionExtensionTerms : ∀ {N} → 𝓼urjectivity Substitunction (Extension $ Terms N)
      𝓼urjectivitySubstitunctionExtensionTerms σ ∅ = ∅
      𝓼urjectivitySubstitunctionExtensionTerms σ (τ , τs) = 𝓼urjectivitySubstitunctionExtensionTerm σ τ , 𝓼urjectivitySubstitunctionExtensionTerms σ τs

  instance

    [𝓢urjectivity]SubstitunctionExtensionTerm : [𝓢urjectivity] Substitunction (Extension Term)
    [𝓢urjectivity]SubstitunctionExtensionTerm = ∁

    𝓢urjectivitySubstitunctionExtensionTerm : 𝓢urjectivity Substitunction (Extension Term)
    𝓢urjectivitySubstitunctionExtensionTerm .𝓢urjectivity.surjectivity = 𝓼urjectivitySubstitunctionExtensionTerm

    [𝓢urjectivity]SubstitunctionExtensionTerms : ∀ {N} → [𝓢urjectivity] Substitunction (Extension $ Terms N)
    [𝓢urjectivity]SubstitunctionExtensionTerms = ∁

    𝓢urjectivitySubstitunctionExtensionTerms : ∀ {N} → 𝓢urjectivity Substitunction (Extension $ Terms N)
    𝓢urjectivitySubstitunctionExtensionTerms .𝓢urjectivity.surjectivity = 𝓼urjectivitySubstitunctionExtensionTerms

  instance

    𝓣ransitivitySubstitunction : 𝓣ransitivity Substitunction
    𝓣ransitivitySubstitunction .𝓣ransitivity.transitivity f g = surjectivity g ∘ f

    HasEquivalenceSubstitunction : ∀ {x y} → HasEquivalence (Substitunction x y) _
    HasEquivalenceSubstitunction = ∁ Proposextensequality

    [IsExtensionB]Term : [IsExtensionB] Term
    [IsExtensionB]Term = ∁

    [IsExtensionB]Terms : ∀ {N} → [IsExtensionB] (Terms N)
    [IsExtensionB]Terms = ∁

  private

    mutual
      𝓼urjextensionalitySubstitunctionExtensionTerm : 𝓼urjextensionality Substitunction _≈_ (Extension Term) _≈_
      𝓼urjextensionalitySubstitunctionExtensionTerm p (i x) = p x
      𝓼urjextensionalitySubstitunctionExtensionTerm p leaf = ∅
      𝓼urjextensionalitySubstitunctionExtensionTerm p (s fork t) = congruity₂ _fork_ (𝓼urjextensionalitySubstitunctionExtensionTerm p s) (𝓼urjextensionalitySubstitunctionExtensionTerm p t)
      𝓼urjextensionalitySubstitunctionExtensionTerm p (function fn ts) = congruity (function fn) (𝓼urjextensionalitySubstitunctionExtensionTerms p ts)

      𝓼urjextensionalitySubstitunctionExtensionTerms : ∀ {N} → 𝓼urjextensionality Substitunction Proposextensequality (Extension $ Terms N) Proposextensequality
      𝓼urjextensionalitySubstitunctionExtensionTerms p ∅ = ∅
      𝓼urjextensionalitySubstitunctionExtensionTerms p (t , ts) = congruity₂ _,_ (𝓼urjextensionalitySubstitunctionExtensionTerm p t) (𝓼urjextensionalitySubstitunctionExtensionTerms p ts)

  instance

    [𝓢urjextensionality]Substitunction : [𝓢urjextensionality] Substitunction Proposextensequality (Extension Term) Proposextensequality
    [𝓢urjextensionality]Substitunction = ∁

    𝓢urjextensionalitySubstitunction : 𝓢urjextensionality Substitunction Proposextensequality (Extension Term) Proposextensequality
    𝓢urjextensionalitySubstitunction .𝓢urjextensionality.surjextensionality = 𝓼urjextensionalitySubstitunctionExtensionTerm

    [𝓢urjextensionality]Substitunctions : ∀ {N} → [𝓢urjextensionality] Substitunction Proposextensequality (Extension $ Terms N) Proposextensequality
    [𝓢urjextensionality]Substitunctions = ∁

    𝓢urjextensionalitySubstitunctions : ∀ {N} → 𝓢urjextensionality Substitunction Proposextensequality (Extension $ Terms N) Proposextensequality
    𝓢urjextensionalitySubstitunctions .𝓢urjextensionality.surjextensionality = 𝓼urjextensionalitySubstitunctionExtensionTerms

  private

    mutual

      𝓼urjtranscommutativitySubstitunctionExtensionTerm : 𝓼urjtranscommutativity Substitunction (Extension Term) Proposextensequality
      𝓼urjtranscommutativitySubstitunctionExtensionTerm _ _ (i _) = !
      𝓼urjtranscommutativitySubstitunctionExtensionTerm _ _ leaf = !
      𝓼urjtranscommutativitySubstitunctionExtensionTerm _ _ (τ₁ fork τ₂) = congruity₂ _fork_ (𝓼urjtranscommutativitySubstitunctionExtensionTerm _ _ τ₁) (𝓼urjtranscommutativitySubstitunctionExtensionTerm _ _ τ₂)
      𝓼urjtranscommutativitySubstitunctionExtensionTerm f g (function fn ts) = congruity (function fn) (𝓼urjtranscommutativitySubstitunctionExtensionTerms f g ts)

      𝓼urjtranscommutativitySubstitunctionExtensionTerms : ∀ {N} → 𝓼urjtranscommutativity Substitunction (Extension $ Terms N) Proposextensequality
      𝓼urjtranscommutativitySubstitunctionExtensionTerms _ _ ∅ = !
      𝓼urjtranscommutativitySubstitunctionExtensionTerms _ _ (τ , τs) = congruity₂ _,_ (𝓼urjtranscommutativitySubstitunctionExtensionTerm _ _ τ) (𝓼urjtranscommutativitySubstitunctionExtensionTerms _ _ τs)

  instance

    [𝓢urjtranscommutativity]SubstitunctionExtensionTerm = [𝓢urjtranscommutativity] Substitunction (Extension Term) Proposextensequality ∋ ∁
    𝓢urjtranscommutativitySubstitunctionExtensionTerm : 𝓢urjtranscommutativity Substitunction (Extension Term) Proposextensequality
    𝓢urjtranscommutativitySubstitunctionExtensionTerm .𝓢urjtranscommutativity.surjtranscommutativity = 𝓼urjtranscommutativitySubstitunctionExtensionTerm

    [𝓢urjtranscommutativity]SubstitunctionExtensionTerms = λ {N} → [𝓢urjtranscommutativity] Substitunction (Extension $ Terms N) Proposextensequality ∋ ∁
    𝓢urjtranscommutativitySubstitunctionExtensionTerms : ∀ {N} → 𝓢urjtranscommutativity Substitunction (Extension $ Terms N) Proposextensequality
    𝓢urjtranscommutativitySubstitunctionExtensionTerms .𝓢urjtranscommutativity.surjtranscommutativity = 𝓼urjtranscommutativitySubstitunctionExtensionTerms

  instance

    [𝓣ransassociativity]Substitunction : [𝓣ransassociativity] Substitunction _≈_
    [𝓣ransassociativity]Substitunction = ∁

    𝓣ransassociativitySubstitunction : 𝓣ransassociativity Substitunction _≈_
    𝓣ransassociativitySubstitunction .𝓣ransassociativity.transassociativity f g h = surjtranscommutativity g h ∘ f

    [𝓣ransextensionality]Substitunction : [𝓣ransextensionality] Substitunction _≈_
    [𝓣ransextensionality]Substitunction = ∁

    𝓣ransextensionalitySubstitunction : 𝓣ransextensionality Substitunction _≈_
    𝓣ransextensionalitySubstitunction .𝓣ransextensionality.transextensionality {f₂ = f₂} f₁≡̇f₂ g₁≡̇g₂ x rewrite f₁≡̇f₂ x = surjextensionality g₁≡̇g₂ $ f₂ x

    IsPrecategorySubstitunction : IsPrecategory Substitunction _≈_
    IsPrecategorySubstitunction = ∁

    IsPrefunctorSubstitunctionExtensionTerm : IsPrefunctor Substitunction _≈_ (Extension Term) _≈_
    IsPrefunctorSubstitunctionExtensionTerm = ∁

    IsPrefunctorSubstitunctionExtensionTerms : ∀ {N} → IsPrefunctor Substitunction _≈_ (Extension $ Terms N) _≈_
    IsPrefunctorSubstitunctionExtensionTerms = ∁

    𝓡eflexivitySubstitunction : 𝓡eflexivity Substitunction
    𝓡eflexivitySubstitunction .𝓡eflexivity.reflexivity = i

  private

    mutual

      𝓼urjidentitySubstitunctionExtensionTerm : 𝓼urjidentity Substitunction (Extension Term) _≈_
      𝓼urjidentitySubstitunctionExtensionTerm (i x) = ∅
      𝓼urjidentitySubstitunctionExtensionTerm leaf = ∅
      𝓼urjidentitySubstitunctionExtensionTerm (s fork t) = congruity₂ _fork_ (𝓼urjidentitySubstitunctionExtensionTerm s) (𝓼urjidentitySubstitunctionExtensionTerm t)
      𝓼urjidentitySubstitunctionExtensionTerm (function fn ts) = congruity (function fn) (𝓼urjidentitySubstitunctionExtensionTerms ts)

      𝓼urjidentitySubstitunctionExtensionTerms : ∀ {N} → 𝓼urjidentity Substitunction (Extension $ Terms N) _≈_
      𝓼urjidentitySubstitunctionExtensionTerms ∅ = ∅
      𝓼urjidentitySubstitunctionExtensionTerms (t , ts) = congruity₂ _,_ (𝓼urjidentitySubstitunctionExtensionTerm t) (𝓼urjidentitySubstitunctionExtensionTerms ts)

  instance

    [𝓢urjidentity]SubstitunctionExtensionTerm : [𝓢urjidentity] Substitunction (Extension Term) _≈_ _ _ _
    [𝓢urjidentity]SubstitunctionExtensionTerm = ∁ Substitunction (Extension Term) _≈_

    𝓢urjidentitySubstitunctionExtensionTerm : 𝓢urjidentity Substitunction (Extension Term) _≈_
    𝓢urjidentitySubstitunctionExtensionTerm .𝒮urjidentity.surjidentity = 𝓼urjidentitySubstitunctionExtensionTerm

    [𝓢urjidentity]SubstitunctionExtensionTerms : ∀ {N} → [𝓢urjidentity] Substitunction (Extension $ Terms N) _≈_ _ _ _
    [𝓢urjidentity]SubstitunctionExtensionTerms {N} = ∁ Substitunction (Extension $ Terms N) _≈_

    𝓢urjidentitySubstitunctionExtensionTerms : ∀ {N} → 𝓢urjidentity Substitunction (Extension $ Terms N) _≈_
    𝓢urjidentitySubstitunctionExtensionTerms .𝒮urjidentity.surjidentity = 𝓼urjidentitySubstitunctionExtensionTerms

    [𝓣ransleftidentitySubstitunction] : [𝓣ransleftidentity] Substitunction _≈_
    [𝓣ransleftidentitySubstitunction] = ∁

    𝓣ransleftidentitySubstitunction : 𝓣ransleftidentity Substitunction _≈_
    𝓣ransleftidentitySubstitunction .𝓣ransleftidentity.transleftidentity {f = f} = surjidentity ∘ f

    [𝓣ransrightidentitySubstitunction] : [𝓣ransrightidentity] Substitunction _≈_
    [𝓣ransrightidentitySubstitunction] = ∁

    𝓣ransrightidentitySubstitunction : 𝓣ransrightidentity Substitunction _≈_
    𝓣ransrightidentitySubstitunction .𝓣ransrightidentity.transrightidentity _ = !

    IsCategorySubstitunction : IsCategory Substitunction _≈_
    IsCategorySubstitunction = ∁

    IsFunctorSubstitunctionExtensionTerm : IsFunctor Substitunction _≈_ (Extension Term) _≈_
    IsFunctorSubstitunctionExtensionTerm = ∁

    IsFunctorSubstitunctionExtensionTerms : ∀ {N} → IsFunctor Substitunction _≈_ (Extension $ Terms N) _≈_
    IsFunctorSubstitunctionExtensionTerms = ∁

module _ {𝔭} (𝔓 : Ø 𝔭) where

  open Substitunction 𝔓
  open Term 𝔓

  PrecategorySubstitunction : Precategory _ _ _
  PrecategorySubstitunction = ∁ Substitunction _≈_

  PrefunctorSubstitunctionExtensionTerm : Prefunctor _ _ _ _ _ _
  PrefunctorSubstitunctionExtensionTerm = ∁ Substitunction _≈_ (Extension Term) _≈_

  CategorySubstitunction : Category _ _ _
  CategorySubstitunction = ∁ Substitunction _≈_

  FunctorSubstitunctionExtensionTerm : Functor _ _ _ _ _ _
  FunctorSubstitunctionExtensionTerm = ∁ Substitunction _≈_ (Extension Term) _≈_

  module _ (N : ¶) where

    FunctorSubstitunctionExtensionTerms : Functor _ _ _ _ _ _
    FunctorSubstitunctionExtensionTerms = ∁ Substitunction _≈_ (Extension $ Terms N) _≈_


-- CategoryAListProposequality
module _ where

  module _ {a} {A : ¶ → Set a} where

    private AList = Descender⟨ A ⟩

    instance

      𝓡eflexivityAList : 𝓡eflexivity AList
      𝓡eflexivityAList .𝓡eflexivity.reflexivity = ∅

      𝓡eflexivityAList' : 𝓡eflexivity (flip AList)
      𝓡eflexivityAList' .𝓡eflexivity.reflexivity = reflexivity[ AList ]

      𝓣ransitivityAList : 𝓣ransitivity AList
      𝓣ransitivityAList .𝓣ransitivity.transitivity f ∅ = f
      𝓣ransitivityAList .𝓣ransitivity.transitivity f (x , g) = x , g ∙ f

      𝓣ransitivityAList' : 𝓣ransitivity (flip AList)
      𝓣ransitivityAList' .𝓣ransitivity.transitivity = flip transitivity

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
      𝓣ransassociativityAList' .𝓣ransassociativity.transassociativity f g h = symmetry (transassociativity h g f)

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

module _ where

  instance

    𝓕mapMaybe : ∀ {𝔬₁ 𝔬₂} → 𝓕map Maybe 𝔬₁ 𝔬₂
    𝓕mapMaybe .𝓕map.fmap f ∅ = ∅
    𝓕mapMaybe .𝓕map.fmap f (↑ x) = ↑ f x

    𝓟ureMaybe : ∀ {𝔬} → 𝓟ure (Maybe {𝔬})
    𝓟ureMaybe .𝓟ure.pure = ↑_

    𝓐pplyMaybe : ∀ {𝔬₁ 𝔬₂} → 𝓐pply Maybe 𝔬₁ 𝔬₂
    𝓐pplyMaybe .𝓐pply.apply ∅ x = ∅
    𝓐pplyMaybe .𝓐pply.apply (↑ f) x = fmap f x

    𝓑indMaybe : ∀ {𝔬₁ 𝔬₂} → 𝓑ind Maybe 𝔬₁ 𝔬₂
    𝓑indMaybe .𝓑ind.bind ∅ _ = ∅
    𝓑indMaybe .𝓑ind.bind (↑ x) f = f x

module _ where

  instance

    𝓢uccessor₀¶ : 𝓢uccessor₀ ¶
    𝓢uccessor₀¶ .𝓢uccessor₀.successor₀ = ↑_

    [𝓢uccessor₁]Fin : [𝓢uccessor₁] Fin
    [𝓢uccessor₁]Fin = ∁

    𝓢uccessor₁Fin : 𝓢uccessor₁ Fin
    𝓢uccessor₁Fin .𝓢uccessor₁.successor₁ = ↑_

    [𝓘njectivity₁]Fin : ∀ {m} → [𝓘njectivity₁] (λ (_ : Fin m) → Fin (⇑₀ m)) Proposequality Proposequality
    [𝓘njectivity₁]Fin = ∁

    𝓘njectivity₁Fin : ∀ {m} → 𝓘njectivity₁ (λ (_ : Fin m) → Fin (⇑₀ m)) Proposequality Proposequality
    𝓘njectivity₁Fin .𝓘njectivity₁.injectivity₁ ∅ = ∅

    [𝓣hick]Fin,Fin : [𝓣hick] Fin Fin
    [𝓣hick]Fin,Fin = ∁

    𝓣hickFin,Fin : 𝓣hick Fin Fin
    𝓣hickFin,Fin .𝓣hick.thick {∅} () ∅
    𝓣hickFin,Fin .𝓣hick.thick {↑ _} _ ∅ = ∅
    𝓣hickFin,Fin .𝓣hick.thick ∅ (↑ y) = y
    𝓣hickFin,Fin .𝓣hick.thick (↑ x) (↑ y) = ↑ thick x y

    [𝓣hin]Fin,Fin : [𝓣hin] Fin Fin
    [𝓣hin]Fin,Fin = ∁

    𝓣hinFin,Fin : 𝓣hin Fin Fin
    𝓣hinFin,Fin .𝓣hin.thin ∅ = ↑_
    𝓣hinFin,Fin .𝓣hin.thin (↑ x) ∅ = ∅
    𝓣hinFin,Fin .𝓣hin.thin (↑ x) (↑ y) = ↑ (thin x y)

    [𝓘njectivity₂,₁]ThinFinFin : ∀ {m} → [𝓘njectivity₂,₁] (𝔱hin Fin Fin m) Proposequality Proposequality
    [𝓘njectivity₂,₁]ThinFinFin = ∁

    𝓘njectivity₂,₁ThinFinFin : ∀ {m} → 𝓘njectivity₂,₁ (𝔱hin Fin Fin m) Proposequality Proposequality
    𝓘njectivity₂,₁ThinFinFin .𝓘njectivity₂,₁.injectivity₂,₁ ∅ ∅ = ∅
    𝓘njectivity₂,₁ThinFinFin .𝓘njectivity₂,₁.injectivity₂,₁ (↑ _) {∅}    {∅} _ = ∅
    𝓘njectivity₂,₁ThinFinFin .𝓘njectivity₂,₁.injectivity₂,₁ (↑ _) {∅}    {↑ _} ()
    𝓘njectivity₂,₁ThinFinFin .𝓘njectivity₂,₁.injectivity₂,₁ (↑ _) {↑ _}  {∅}   ()
    𝓘njectivity₂,₁ThinFinFin .𝓘njectivity₂,₁.injectivity₂,₁ (↑ x) {↑ _}  {↑ _} = congruity ↑_ ∘ injectivity₂,₁ x ∘ injectivity₁[ Proposequality ]

    [𝓒heck]FinFinMaybe : [𝓒heck] Fin Fin Maybe
    [𝓒heck]FinFinMaybe = ∁

    𝓒heckFinFinMaybe : 𝓒heck Fin Fin Maybe
    𝓒heckFinFinMaybe .𝓒heck.check ∅ ∅ = ∅
    𝓒heckFinFinMaybe .𝓒heck.check ∅ (↑ y) = ↑ y
    𝓒heckFinFinMaybe .𝓒heck.check {∅} (↑ ()) _
    𝓒heckFinFinMaybe .𝓒heck.check {↑ _} (↑ x) ∅ = ↑ ∅
    𝓒heckFinFinMaybe .𝓒heck.check {↑ _} (↑ x) (↑ y) = fmap ¶⟨<_⟩.↑_ $ check x y

    [𝓣hick/thin=1]FinFin : [𝓣hick/thin=1] Fin Fin Proposequality
    [𝓣hick/thin=1]FinFin = ∁

    𝓣hick/thin=1FinFin : 𝓣hick/thin=1 Fin Fin Proposequality
    𝓣hick/thin=1FinFin .𝓣hick/thin=1.thick/thin=1 x ∅ = ∅
    𝓣hick/thin=1FinFin .𝓣hick/thin=1.thick/thin=1 ∅ (↑ y) = ∅
    𝓣hick/thin=1FinFin .𝓣hick/thin=1.thick/thin=1 (↑ x) (↑ y) = congruity ↑_ (thick/thin=1 x y)

    [𝓒heck/thin=1FinFin] : [𝓒heck/thin=1] Fin Fin Maybe Proposequality
    [𝓒heck/thin=1FinFin] = ∁

    𝓒heck/thin=1FinFin : 𝓒heck/thin=1 Fin Fin Maybe Proposequality
    𝓒heck/thin=1FinFin .𝓒heck/thin=1.check/thin=1 ∅ y = ∅
    𝓒heck/thin=1FinFin .𝓒heck/thin=1.check/thin=1 (↑ x) ∅ = ∅
    𝓒heck/thin=1FinFin .𝓒heck/thin=1.check/thin=1 (↑ x) (↑ y) rewrite check/thin=1 {_≈_ = Proposequality⟦ Maybe _ ⟧} x y = ∅

    IsThickandthinFinFin : IsThickandthin Fin Fin Proposequality Maybe Proposequality
    IsThickandthinFinFin = ∁

  ThickandthinFinFin : Thickandthin _ _ _ _ _ _
  ThickandthinFinFin = ∁ Fin Fin Proposequality Maybe Proposequality


module _ where

  instance

    𝓘njection₂Vec : ∀ {N} {𝔭} {𝔓 : ¶ → Ø 𝔭} → 𝓘njection₂ (λ (x : 𝔓 N) (_ : Vec⟨ 𝔓 ⟩ N) → Vec⟨ 𝔓 ⟩ (⇑₀ N))
    𝓘njection₂Vec .𝓘njection₂.injection₂ = _,_

    [𝓘njectivity₂,₀,₁]Vec : ∀ {N} {𝔭} {𝔓 : ¶ → Ø 𝔭} → [𝓘njectivity₂,₀,₁] (λ (x : 𝔓 N) (_ : Vec⟨ 𝔓 ⟩ N) → Vec⟨ 𝔓 ⟩ (⇑₀ N)) Proposequality Proposequality
    [𝓘njectivity₂,₀,₁]Vec = ∁

    𝓘njectivity₂,₀,₁Vec :   ∀ {N} {𝔭} {𝔓 : ¶ → Ø 𝔭} → 𝓘njectivity₂,₀,₁   (λ (x : 𝔓 N) (_ : Vec⟨ 𝔓 ⟩ N) → Vec⟨ 𝔓 ⟩ (⇑₀ N)) Proposequality Proposequality
    𝓘njectivity₂,₀,₁Vec .𝓘njectivity₂,₀,₁.injectivity₂,₀,₁ ∅ = ∅

    [𝓘njectivity₂,₀,₂]Vec : ∀ {N} {𝔭} {𝔓 : ¶ → Ø 𝔭} → [𝓘njectivity₂,₀,₂] (λ (x : 𝔓 N) (_ : Vec⟨ 𝔓 ⟩ N) → Vec⟨ 𝔓 ⟩ (⇑₀ N)) Proposequality Proposequality
    [𝓘njectivity₂,₀,₂]Vec = ∁

    𝓘njectivity₂,₀,₂Vec : ∀ {N} {𝔭} {𝔓 : ¶ → Ø 𝔭} → 𝓘njectivity₂,₀,₂ (λ (x : 𝔓 N) (_ : Vec⟨ 𝔓 ⟩ N) → Vec⟨ 𝔓 ⟩ (⇑₀ N)) Proposequality Proposequality
    𝓘njectivity₂,₀,₂Vec .𝓘njectivity₂,₀,₂.injectivity₂,₀,₂ ∅ = ∅

module _ where

  instance

    IsDecidableFin : ∀ {n} → IsDecidable (Fin n)
    IsDecidableFin .IsDecidable._≟_ ∅ ∅ = ↑ ∅
    IsDecidableFin .IsDecidable._≟_ ∅ (↑ _) = ↓ λ ()
    IsDecidableFin .IsDecidable._≟_ (↑ _) ∅ = ↓ λ ()
    IsDecidableFin .IsDecidable._≟_ (↑ x) (↑ y) with x ≟ y
    … | ↑ ∅ = ↑ ∅
    … | ↓ x≢y = ↓ λ {∅ → x≢y ∅}

  instance

    IsDecidable¶ : IsDecidable ¶
    IsDecidable¶ .IsDecidable._≟_ ∅ ∅ = ↑ ∅
    IsDecidable¶ .IsDecidable._≟_ ∅ (↑ _) = ↓ λ ()
    IsDecidable¶ .IsDecidable._≟_ (↑ _) ∅ = ↓ λ ()
    IsDecidable¶ .IsDecidable._≟_ (↑ x) (↑ y) with x ≟ y
    … | ↑ ∅ = ↑ ∅
    … | ↓ x≢y = ↓ λ {∅ → x≢y ∅}

module _ {𝔭} {𝔓 : Ø 𝔭} where

  open Substitunction 𝔓
  open Term 𝔓

  private

    mutual

      𝓼urjectivityExtensionFinExtensionTerm : 𝓼urjectivity (Extension Fin) (Extension Term)
      𝓼urjectivityExtensionFinExtensionTerm x (i y) = i (x y)
      𝓼urjectivityExtensionFinExtensionTerm x leaf = leaf
      𝓼urjectivityExtensionFinExtensionTerm x (l fork r) = 𝓼urjectivityExtensionFinExtensionTerm x l fork 𝓼urjectivityExtensionFinExtensionTerm x r
      𝓼urjectivityExtensionFinExtensionTerm x (function f ts) = function f $ 𝓼urjectivityExtensionFinExtensionTerms x ts

      𝓼urjectivityExtensionFinExtensionTerms : ∀ {N} → 𝓼urjectivity (Extension Fin) (Extension $ Terms N)
      𝓼urjectivityExtensionFinExtensionTerms x ∅ = ∅
      𝓼urjectivityExtensionFinExtensionTerms x (t , ts) = 𝓼urjectivityExtensionFinExtensionTerm x t , 𝓼urjectivityExtensionFinExtensionTerms x ts

  instance

    [𝓢urjectivity]ExtensionFinExtensionTerm : [𝓢urjectivity] (Extension Fin) (Extension Term)
    [𝓢urjectivity]ExtensionFinExtensionTerm = ∁

    𝓢urjectivityExtensionFinExtensionTerm : 𝓢urjectivity (Extension Fin) (Extension Term)
    𝓢urjectivityExtensionFinExtensionTerm .𝓢urjectivity.surjectivity = 𝓼urjectivityExtensionFinExtensionTerm

    [𝓢urjectivity]ExtensionFinExtensionTerms : ∀ {N} → [𝓢urjectivity] (Extension Fin) (Extension $ Terms N)
    [𝓢urjectivity]ExtensionFinExtensionTerms = ∁

    𝓢urjectivityExtensionFinExtensionTerms : ∀ {N} → 𝓢urjectivity (Extension Fin) (Extension $ Terms N)
    𝓢urjectivityExtensionFinExtensionTerms .𝓢urjectivity.surjectivity = 𝓼urjectivityExtensionFinExtensionTerms

  instance

    [𝓣hick]FinTerm : [𝓣hick] Fin Term
    [𝓣hick]FinTerm = ∁

    𝓣hickFinTerm : 𝓣hick Fin Term
    𝓣hickFinTerm .𝓣hick.thick x t = thick x ◃ t

    [𝓣hick]FinTerms : ∀ {N} → [𝓣hick] Fin (Terms N)
    [𝓣hick]FinTerms = ∁

    𝓣hickFinTerms : ∀ {N} → 𝓣hick Fin (Terms N)
    𝓣hickFinTerms .𝓣hick.thick x t = thick x ◃ t

    [𝓣hin]FinTerm : [𝓣hin] Fin Term
    [𝓣hin]FinTerm = ∁

    𝓣hinFinTerm : 𝓣hin Fin Term
    𝓣hinFinTerm .𝓣hin.thin = surjectivity ∘ thin

    [𝓣hin]FinTerms : ∀ {N} → [𝓣hin] Fin (Terms N)
    [𝓣hin]FinTerms = ∁

    𝓣hinFinTerms : ∀ {N} → 𝓣hin Fin (Terms N)
    𝓣hinFinTerms .𝓣hin.thin = surjectivity ∘ thin

    [𝓘njectivity₂,₁]FinTerm : ∀ {m} → [𝓘njectivity₂,₁] (𝔱hin Fin Term m) Proposequality Proposequality
    [𝓘njectivity₂,₁]FinTerm = ∁

    𝓘njection₂FinTerm : ∀ {m} → 𝓘njection₂ (λ (_ : ¶⟨< ↑ m ⟩) (_ : Term m) → Term (↑ m))
    𝓘njection₂FinTerm {m} .𝓘njection₂.injection₂ = thin

    [𝓘njectivity₂,₁]FinTerms : ∀ {N m} → [𝓘njectivity₂,₁] (𝔱hin Fin (Terms N) m) Proposequality Proposequality
    [𝓘njectivity₂,₁]FinTerms = ∁

    𝓘njection₂FinTerms : ∀ {N m} → 𝓘njection₂ (λ (_ : ¶⟨< ↑ m ⟩) (_ : Terms N m) → Terms N (↑ m))
    𝓘njection₂FinTerms {m} .𝓘njection₂.injection₂ = thin




    𝓘njection₁-TermI : ∀ {n} → 𝓘njection₁ (λ (_ : ¶⟨< n ⟩) → Term n)
    𝓘njection₁-TermI .𝓘njection₁.injection₁ = i

    [𝓘njectivity₁]TermI : ∀ {n} → [𝓘njectivity₁] (λ (_ : ¶⟨< n ⟩) → Term n) Proposequality Proposequality
    [𝓘njectivity₁]TermI = ∁

    𝓘njectivity₁TermI : ∀ {n} → 𝓘njectivity₁ (λ (_ : ¶⟨< n ⟩) → Term n) Proposequality Proposequality
    𝓘njectivity₁TermI {n} .𝓘njectivity₁.injectivity₁ ∅ = ∅

    𝓘njection₂-TermFork : ∀ {n} → 𝓘njection₂ (λ (_ : Term n) (_ : Term n) → Term n)
    𝓘njection₂-TermFork .𝓘njection₂.injection₂ = _fork_

    [𝓘njection₂,₀,₁]-TermFork : ∀ {n} → [𝓘njectivity₂,₀,₁] (λ (_ : Term n) (_ : Term n) → Term n) Proposequality Proposequality
    [𝓘njection₂,₀,₁]-TermFork = ∁

    𝓘njection₂,₀,₁-TermFork : ∀ {n} → 𝓘njectivity₂,₀,₁ (λ (_ : Term n) (_ : Term n) → Term n) Proposequality Proposequality
    𝓘njection₂,₀,₁-TermFork .𝓘njectivity₂,₀,₁.injectivity₂,₀,₁ ∅ = ∅

    [𝓘njection₂,₀,₂]-TermFork : ∀ {n} → [𝓘njectivity₂,₀,₂] (λ (_ : Term n) (_ : Term n) → Term n) Proposequality Proposequality
    [𝓘njection₂,₀,₂]-TermFork = ∁

    𝓘njection₂,₀,₂-TermFork : ∀ {n} → 𝓘njectivity₂,₀,₂ (λ (_ : Term n) (_ : Term n) → Term n) Proposequality Proposequality
    𝓘njection₂,₀,₂-TermFork .𝓘njectivity₂,₀,₂.injectivity₂,₀,₂ ∅ = ∅

    𝓘njection₃TermFunction : ∀ {n} → 𝓘njection₃ (λ (_ : 𝔓) (N : ¶) (_ : Terms N n) → Term n)
    𝓘njection₃TermFunction {n} .𝓘njection₃.injection₃ p N ts = function p ts

    [𝓘njectivity₃,₀,₁]TermFunction : ∀ {n} → [𝓘njectivity₃,₀,₁] (λ (_ : 𝔓) (N : ¶) (_ : Terms N n) → Term n) Proposequality Proposequality
    [𝓘njectivity₃,₀,₁]TermFunction = ∁

    𝓘njectivity₃,₀,₁TermFunction : ∀ {n} → 𝓘njectivity₃,₀,₁ (λ (_ : 𝔓) (N : ¶) (_ : Terms N n) → Term n) Proposequality Proposequality
    𝓘njectivity₃,₀,₁TermFunction .𝓘njectivity₃,₀,₁.injectivity₃,₀,₁ ∅ = ∅

    [𝓘njectivity₃,₀,₂]TermFunction : ∀ {n} → [𝓘njectivity₃,₀,₂] (λ (_ : 𝔓) (N : ¶) (_ : Terms N n) → Term n) Proposequality Proposequality
    [𝓘njectivity₃,₀,₂]TermFunction = ∁

    𝓘njectivity₃,₀,₂TermFunction : ∀ {n} → 𝓘njectivity₃,₀,₂ (λ (_ : 𝔓) (N : ¶) (_ : Terms N n) → Term n) Proposequality Proposequality
    𝓘njectivity₃,₀,₂TermFunction .𝓘njectivity₃,₀,₂.injectivity₃,₀,₂ ∅ = ∅

    𝓘njection₂TermFunction : ∀ {N n} → 𝓘njection₂ (λ (_ : 𝔓) (_ : Terms N n) → Term n)
    𝓘njection₂TermFunction {N} {n} .𝓘njection₂.injection₂ p ts = function p ts

    [𝓘njectivity₂,₀,₂]TermFunction : ∀ {N n} → [𝓘njectivity₂,₀,₂] (λ (_ : 𝔓) (_ : Terms N n) → Term n) Proposequality Proposequality
    [𝓘njectivity₂,₀,₂]TermFunction = ∁

    𝓘njectivity₂,₀,₂TermFunction : ∀ {N n} → 𝓘njectivity₂,₀,₂ (λ (_ : 𝔓) (_ : Terms N n) → Term n) Proposequality Proposequality
    𝓘njectivity₂,₀,₂TermFunction .𝓘njectivity₂,₀,₂.injectivity₂,₀,₂ ∅ = ∅

  mutual

    instance

      𝓘njectivity₂,₁FinTerm : ∀ {m} → 𝓘njectivity₂,₁ (𝔱hin Fin Term m) Proposequality Proposequality
      𝓘njectivity₂,₁FinTerm .𝓘njectivity₂,₁.injectivity₂,₁ x {i _} {i _} eq = congruity i (injectivity₂,₁ x (injectivity₁[ Proposequality ] eq))
      𝓘njectivity₂,₁FinTerm .𝓘njectivity₂,₁.injectivity₂,₁ _ {i _} {leaf} ()
      𝓘njectivity₂,₁FinTerm .𝓘njectivity₂,₁.injectivity₂,₁ _ {i _} {_ fork _} ()
      𝓘njectivity₂,₁FinTerm .𝓘njectivity₂,₁.injectivity₂,₁ _ {i _} {function _ _} ()
      𝓘njectivity₂,₁FinTerm .𝓘njectivity₂,₁.injectivity₂,₁ _ {leaf} {i _} ()
      𝓘njectivity₂,₁FinTerm .𝓘njectivity₂,₁.injectivity₂,₁ _ {leaf} {leaf} _ = ∅
      𝓘njectivity₂,₁FinTerm .𝓘njectivity₂,₁.injectivity₂,₁ _ {leaf} {_ fork _} ()
      𝓘njectivity₂,₁FinTerm .𝓘njectivity₂,₁.injectivity₂,₁ _ {leaf} {function _ _} ()
      𝓘njectivity₂,₁FinTerm .𝓘njectivity₂,₁.injectivity₂,₁ _ {_ fork _} {i _} ()
      𝓘njectivity₂,₁FinTerm .𝓘njectivity₂,₁.injectivity₂,₁ _ {_ fork _} {leaf} ()
      𝓘njectivity₂,₁FinTerm .𝓘njectivity₂,₁.injectivity₂,₁ x {y₁ fork y₂} {y₃ fork y₄} eq
        rewrite injectivity₂,₁ {_∼₂_ = Proposequality} x {y₁ = y₁} (injectivity₂,₀,₁[ Proposequality ] eq)
              | injectivity₂,₁ {_∼₂_ = Proposequality} x {y₁ = y₂} (injectivity₂,₀,₂[ Proposequality ] eq)
        = ∅
      𝓘njectivity₂,₁FinTerm .𝓘njectivity₂,₁.injectivity₂,₁ _ {y₁ fork y₂} {function x₁ x₂} ()
      𝓘njectivity₂,₁FinTerm .𝓘njectivity₂,₁.injectivity₂,₁ _ {function _ _} {i x₃} ()
      𝓘njectivity₂,₁FinTerm .𝓘njectivity₂,₁.injectivity₂,₁ _ {function _ _} {leaf} ()
      𝓘njectivity₂,₁FinTerm .𝓘njectivity₂,₁.injectivity₂,₁ _ {function _ _} {y₂ fork y₃} ()
      𝓘njectivity₂,₁FinTerm .𝓘njectivity₂,₁.injectivity₂,₁ x {function p1 {N1} ts1} {function p2 {N2} ts2} t₁≡t₂
        rewrite injectivity₃,₀,₁[ Proposequality ] {x₂ = p2} t₁≡t₂
        with injectivity₃,₀,₂[ Proposequality ] {y₂ = N2} t₁≡t₂
      … | ∅
        with injectivity₂,₀,₂[ Proposequality ] {y₂ = thin x ts2} t₁≡t₂
      … | ts₁≡ts₂ = congruity (function p2) (injectivity₂,₁ x ts₁≡ts₂)

      𝓘njectivity₂,₁FinTerms : ∀ {N m} → 𝓘njectivity₂,₁ (𝔱hin Fin (Terms N) m) Proposequality Proposequality
      𝓘njectivity₂,₁FinTerms .𝓘njectivity₂,₁.injectivity₂,₁ x {∅} {∅} x₁ = ∅
      𝓘njectivity₂,₁FinTerms .𝓘njectivity₂,₁.injectivity₂,₁ x {_ , _} {t₂ , ts₂} eq
        rewrite injectivity₂,₁ {_∼₂_ = Proposequality} x {y₂ = t₂} (injectivity₂,₀,₁[ Proposequality ] eq)
              | injectivity₂,₁ {_∼₂_ = Proposequality} x {y₂ = ts₂} (injectivity₂,₀,₂[ Proposequality ] eq)
        = ∅

  instance

    [𝓒heck]FinTermMaybe : [𝓒heck] Fin Term Maybe
    [𝓒heck]FinTermMaybe = ∁

    [𝓒heck]FinTermsMaybe : ∀ {N} → [𝓒heck] Fin (Terms N) Maybe
    [𝓒heck]FinTermsMaybe = ∁

  mutual

    instance

      𝓒heckFinTermMaybe : 𝓒heck Fin Term Maybe
      𝓒heckFinTermMaybe .𝓒heck.check x (i y) = ⦇ i (check x y) ⦈
      𝓒heckFinTermMaybe .𝓒heck.check x leaf = ⦇ leaf ⦈
      𝓒heckFinTermMaybe .𝓒heck.check x (y₁ fork y₂) = ⦇ _fork_ (check x y₁) (check x y₂) ⦈
      𝓒heckFinTermMaybe .𝓒heck.check x (function p ts) = ⦇ (function p) (check x ts) ⦈

      𝓒heckFinTermsMaybe : ∀ {N} → 𝓒heck Fin (Terms N) Maybe
      𝓒heckFinTermsMaybe .𝓒heck.check _ ∅ = ⦇ ∅ ⦈
      𝓒heckFinTermsMaybe .𝓒heck.check x (t , ts) = ⦇ check x t , check x ts ⦈

  instance

    [𝓣hick/thin=1]FinTermProposequality : [𝓣hick/thin=1] Fin Term Proposequality
    [𝓣hick/thin=1]FinTermProposequality = ∁

    [𝓣hick/thin=1]FinTermsProposequality : ∀ {N} → [𝓣hick/thin=1] Fin (Terms N) Proposequality
    [𝓣hick/thin=1]FinTermsProposequality = ∁

  mutual

    instance

      𝓣hick/thin=1FinTermProposequality : 𝓣hick/thin=1 Fin Term Proposequality
      𝓣hick/thin=1FinTermProposequality .𝓣hick/thin=1.thick/thin=1 x (i y) rewrite thick/thin=1 {_≈_ = Proposequality} x y = ∅ -- congruity i $ thick/thin=1 x y
      𝓣hick/thin=1FinTermProposequality .𝓣hick/thin=1.thick/thin=1 x leaf = ∅
      𝓣hick/thin=1FinTermProposequality .𝓣hick/thin=1.thick/thin=1 x (y₁ fork y₂) = congruity₂ _fork_ (thick/thin=1 x y₁) (thick/thin=1 x y₂)
      𝓣hick/thin=1FinTermProposequality .𝓣hick/thin=1.thick/thin=1 x (function p ts) = congruity (function p) (thick/thin=1 x ts)

      𝓣hick/thin=1FinTermsProposequality : ∀ {N} → 𝓣hick/thin=1 Fin (Terms N) Proposequality
      𝓣hick/thin=1FinTermsProposequality .𝓣hick/thin=1.thick/thin=1 x ∅ = ∅
      𝓣hick/thin=1FinTermsProposequality .𝓣hick/thin=1.thick/thin=1 x (t , ts) = congruity₂ _,_ (thick/thin=1 x t) (thick/thin=1 x ts)

  instance

    [𝓒heck/thin=1]FinTermMaybe : [𝓒heck/thin=1] Fin Term Maybe Proposequality
    [𝓒heck/thin=1]FinTermMaybe = ∁

    [𝓒heck/thin=1]FinTermsMaybe : ∀ {N} → [𝓒heck/thin=1] Fin (Terms N) Maybe Proposequality
    [𝓒heck/thin=1]FinTermsMaybe = ∁

  mutual

    instance

      𝓒heck/thin=1FinTermMaybe : 𝓒heck/thin=1 Fin Term Maybe Proposequality
      𝓒heck/thin=1FinTermMaybe .𝓒heck/thin=1.check/thin=1 x (i y) rewrite check/thin=1 {_≈_ = Proposequality⟦ Maybe _ ⟧} x y = ∅
      𝓒heck/thin=1FinTermMaybe .𝓒heck/thin=1.check/thin=1 x leaf = ∅
      𝓒heck/thin=1FinTermMaybe .𝓒heck/thin=1.check/thin=1 x (y₁ fork y₂)
        rewrite check/thin=1 {_≈_ = Proposequality⟦ Maybe _ ⟧} x y₁
              | check/thin=1 {_≈_ = Proposequality⟦ Maybe _ ⟧} x y₂
        = ∅
      𝓒heck/thin=1FinTermMaybe .𝓒heck/thin=1.check/thin=1 x (function p ys) rewrite check/thin=1 {_≈_ = Proposequality⟦ Maybe _ ⟧} x ys = ∅

      𝓒heck/thin=1FinTermsMaybe : ∀ {N} → 𝓒heck/thin=1 Fin (Terms N) Maybe Proposequality
      𝓒heck/thin=1FinTermsMaybe .𝓒heck/thin=1.check/thin=1 x ∅ = ∅
      𝓒heck/thin=1FinTermsMaybe .𝓒heck/thin=1.check/thin=1 x (y , ys)
        rewrite check/thin=1 {_≈_ = Proposequality⟦ Maybe _ ⟧} x y
              | check/thin=1 {_≈_ = Proposequality⟦ Maybe _ ⟧} x ys
        = ∅

  instance

    IsThickandthinFinTerm : IsThickandthin Fin Term Proposequality Maybe Proposequality
    IsThickandthinFinTerm = ∁

    IsThickandthinFinTerms : ∀ {N} → IsThickandthin Fin (Terms N) Proposequality Maybe Proposequality
    IsThickandthinFinTerms = ∁

module _ {𝔭} (𝔓 : Ø 𝔭) where

  open Substitunction 𝔓
  open Term 𝔓

  ThickandthinFinTerm : Thickandthin _ _ _ _ _ _
  ThickandthinFinTerm = ∁ Fin Term Proposequality Maybe Proposequality

  ThickandthinFinTerms : ∀ N → Thickandthin _ _ _ _ _ _
  ThickandthinFinTerms N = ∁ Fin (Terms N) Proposequality Maybe Proposequality

-- A dependent eliminator.

maybe : ∀ {a b} {A : Set a} {B : Maybe A → Set b} →
        ((x : A) → B (↑ x)) → B ∅ → (x : Maybe A) → B x
maybe j n (↑ x) = j x
maybe j n ∅  = n

-- A non-dependent eliminator.

maybe′ : ∀ {a b} {A : Set a} {B : Set b} → (A → B) → B → Maybe A → B
maybe′ = maybe

module _ {𝔭} {𝔓 : Ø 𝔭} where

  open Substitunction 𝔓
  open Term 𝔓
  open Substitist 𝔓

  _for_ : ∀ {n} (t' : Term n) (x : Fin (↑ n)) → Fin (↑ n) → Term n
  (t for x) y = maybe′ ε t (check[ Maybe ] x y)

  instance

    [𝓢urjectivity]Substitist,Substitunction : [𝓢urjectivity] Substitist Substitunction
    [𝓢urjectivity]Substitist,Substitunction = ∁

    𝓢urjectivitySubstitist,Substitunction : 𝓢urjectivity Substitist Substitunction
    𝓢urjectivitySubstitist,Substitunction .𝓢urjectivity.surjectivity ∅ = i
    𝓢urjectivitySubstitist,Substitunction .𝓢urjectivity.surjectivity ((x , t) , σ) = surjectivity σ ∙ (t for x)

    [𝓢urjextensionality]Substitist,Substitunction : [𝓢urjextensionality] Substitist Proposequality Substitunction _≈_
    [𝓢urjextensionality]Substitist,Substitunction = ∁

    𝓢urjextensionalitySubstitist,Substitunction : 𝓢urjextensionality Substitist Proposequality Substitunction _≈_
    𝓢urjextensionalitySubstitist,Substitunction .𝓢urjextensionality.surjextensionality ∅ _ = ∅

    [𝓢urjtranscommutativity]Substitist,Substitunction : [𝓢urjtranscommutativity] Substitist Substitunction _≈_
    [𝓢urjtranscommutativity]Substitist,Substitunction = ∁

    𝓢urjtranscommutativitySubstitist,Substitunction : 𝓢urjtranscommutativity Substitist Substitunction _≈_
    𝓢urjtranscommutativitySubstitist,Substitunction .𝓢urjtranscommutativity.surjtranscommutativity ∅ _ _ = ∅
    𝓢urjtranscommutativitySubstitist,Substitunction .𝓢urjtranscommutativity.surjtranscommutativity ((π₀ , π₁) , f) g =
        (
            § g ⟪∙⟫ §[ Substitunction ] f
          ∙
            ⟪ surjtranscommutativity {_∼̇₂_ = Proposextensequality} f g ⟫
        )
      ∘
        π₁ for π₀

    IsPrefunctorSubstitist,Substitunction : IsPrefunctor Substitist Proposequality Substitunction _≈_
    IsPrefunctorSubstitist,Substitunction = ∁

    [𝓢urjidentity]Substitist,Substitunction : [𝓢urjidentity] Substitist Substitunction _≈_ _ _ _
    [𝓢urjidentity]Substitist,Substitunction = ∁ Substitist Substitunction _≈_

    𝓢urjidentitySubstitist,Substitunction : 𝓢urjidentity Substitist Substitunction _≈_
    𝓢urjidentitySubstitist,Substitunction .𝒮urjidentity.surjidentity _ = ∅

    IsFunctorSubstitist,Substitunction : IsFunctor Substitist Proposequality Substitunction _≈_
    IsFunctorSubstitist,Substitunction = ∁

  flexFlex : ∀ {m} → Fin m → Fin m → ∃ Substitist m
  flexFlex {↑ m} x y with check[ Maybe ] x y
  … | ↑ y' = m , (x , i y') , ∅
  … | ∅ = ↑ m , ∅
  flexFlex {∅} ()

  flexRigid : ∀ {m} → Fin m → Term m → Maybe (∃ Substitist m)
  flexRigid {↑ m} x t with check[ Maybe ] x t
  … | ↑ t' = ↑ (m , (x , t') , ∅)
  … | ∅ = ∅
  flexRigid {∅} () _

module _ {𝔭} {𝔓 : Ø 𝔭} where

  open Substitunction 𝔓
  open Term 𝔓
  open Substitist 𝔓

  module _ ⦃ _ : IsDecidable 𝔓 ⦄ where

    mutual

      instance

        ⋆amguTerm : Amgu Term (∃_ ∘ Substitist) Maybe
        ⋆amguTerm .Amgu.amgu leaf leaf acc = ↑ acc
        ⋆amguTerm .Amgu.amgu leaf (function _ _) acc = ∅
        ⋆amguTerm .Amgu.amgu leaf (s' fork t') acc = ∅
        ⋆amguTerm .Amgu.amgu (s' fork t') leaf acc = ∅
        ⋆amguTerm .Amgu.amgu (s' fork t') (function _ _) acc = ∅
        ⋆amguTerm .Amgu.amgu (s1 fork s2) (t1 fork t2) acc = amgu s2 t2 =<< amgu s1 t1 acc
        ⋆amguTerm .Amgu.amgu (function fn₁ ts₁) leaf acc = ∅
        ⋆amguTerm .Amgu.amgu (function fn₁ {n₁} ts₁) (function fn₂ {n₂} ts₂) acc
         with fn₁ ≟ fn₂
        … | ↓ _ = ∅
        … | ↑ _
         with n₁ ≟ n₂
        … | ↓ _ = ∅
        … | ↑ ∅ = amgu ts₁ ts₂ acc
        ⋆amguTerm .Amgu.amgu (function fn₁ ts₁) (_ fork _) acc = ∅
        ⋆amguTerm .Amgu.amgu (i x) (i y) (m , ∅) = ↑ flexFlex x y
        ⋆amguTerm .Amgu.amgu (i x) t     (m , ∅) = flexRigid x t
        ⋆amguTerm .Amgu.amgu t     (i x) (m , ∅) = flexRigid x t
        ⋆amguTerm .Amgu.amgu s     t  (n , _,_ {n = m} (z , r) σ) = fmap (λ {(n' , σ') → n' , (z , r) , σ'}) (amgu {x = m} (§ (r for z) $ s) (§ (r for z) $ t) (n Σ., σ))

        ⋆amguVecTerm : ∀ {N} → Amgu (Terms N) (∃_ ∘ Substitist) Maybe
        ⋆amguVecTerm .Amgu.amgu ∅ ∅ acc = ↑ acc
        ⋆amguVecTerm .Amgu.amgu (t₁ , t₁s) (t₂ , t₂s) acc = amgu t₁s t₂s =<< amgu t₁ t₂ acc

module _ {𝔭} (𝔓 : Ø 𝔭) where

  open Substitunction 𝔓
  open Term 𝔓
  open Substitist 𝔓

  module _ ⦃ _ : IsDecidable 𝔓 ⦄ where

    mgu : ∀ {m} → Term m → Term m → Maybe $ ∃ Substitist m
    mgu {m} s t = amgu s t (m Σ., ∅)

module _ where

  instance
    PropIdFromTransleftidentity : ∀
      {𝔵} {𝔛 : Ø 𝔵}
      {𝔞} {𝔄 : 𝔛 → Ø 𝔞}
      {𝔟} {𝔅 : 𝔛 → Ø 𝔟}
      (let _∼_ = Arrow 𝔄 𝔅)
      {ℓ̇} {_∼̇_ : ∀ {x y} → x ∼ y → x ∼ y → Ø ℓ̇}
      ⦃ _ : 𝓣ransitivity _∼_ ⦄
      ⦃ _ : 𝓡eflexivity _∼_ ⦄
      {ℓ}
      ⦃ _ : [𝓣ransleftidentity] _∼_ _∼̇_ ⦄
      ⦃ _ : 𝓣ransleftidentity _∼_ _∼̇_ ⦄
      ⦃ _ : ∀ {x y} → 𝓢ymmetry (_∼̇_ {x} {y}) ⦄
      → PropId 𝔄 𝔅 _∼̇_ ℓ
    PropIdFromTransleftidentity .PropId.prop-id (_ , P₁) = P₁ $ symmetry transleftidentity

  𝓾nifies₀ : ∀
    {𝔵} {𝔒 : Ø 𝔵}
    {𝔭} (𝔓 : 𝔒 → Ø 𝔭)
    {𝔯₁} (_↦₁_ : π̂² 𝔯₁ 𝔒)
    𝔯₂
    → Ø 𝔵 ∙̂ 𝔭 ∙̂ 𝔯₁ ∙̂ ↑̂ 𝔯₂
  𝓾nifies₀ 𝔓 _↦₁_ 𝔯₂ = ∀ {m} → 𝔓 m → 𝔓 m → Ṗroperty 𝔯₂ (m ↦₁_)

  Unifies₀ : ∀
    {𝔵} {𝔒 : Ø 𝔵}
    {𝔭} {𝔓 : 𝔒 → Ø 𝔭}
    {𝔯₁} {_↦₁_ : π̂² 𝔯₁ 𝔒}
    ⦃ _ : [𝓢urjectivity] _↦₁_ (Extension 𝔓) ⦄
    ⦃ _ : 𝓢urjectivity _↦₁_ (Extension 𝔓) ⦄
    {𝔯₂} (_↦₂_ : Ṙelation 𝔯₂ 𝔓)
    → 𝓾nifies₀ 𝔓 _↦₁_ 𝔯₂
  Unifies₀ _↦₂_ p q x =
    let _↦₂_ = _↦₂_
        infix 4 _↦₂_
    in
    x ◃ p ↦₂ x ◃ q

  Unifies₀⟦_⟧ : ∀
    {𝔵} {𝔛 : Ø 𝔵}
    {𝔞} (𝔄 : 𝔛 → 𝔛 → Ø 𝔞)
    {𝔠} {ℭ : 𝔛 → Ø 𝔠}
    ⦃ _ : [𝓢urjectivity] 𝔄 (Extension ℭ) ⦄
    ⦃ _ : 𝓢urjectivity 𝔄 (Extension ℭ) ⦄
    {ℓ} (_≈_ : ∀ {y} → ℭ y → ℭ y → Ø ℓ)
    → ∀ {m} → ℭ m → ℭ m → Ṗroperty ℓ (𝔄 m)
  Unifies₀⟦ _ ⟧ = Unifies₀

  ≡-Unifies₀ : ∀
    {𝔵} {𝔛 : Ø 𝔵}
    {𝔞} {𝔄 : 𝔛 → 𝔛 → Ø 𝔞}
    {𝔠} {ℭ : 𝔛 → Ø 𝔠}
    ⦃ _ : [𝓢urjectivity] 𝔄 (Extension ℭ) ⦄
    ⦃ _ : 𝓢urjectivity 𝔄 (Extension ℭ) ⦄
    → ∀ {m} → ℭ m → ℭ m → Ṗroperty ∅̂ (𝔄 m)
  ≡-Unifies₀ = Unifies₀ _≡_

  ≡-Unifies₀⟦_⟧ : ∀
    {𝔵} {𝔛 : Ø 𝔵}
    {𝔞} (𝔄 : 𝔛 → 𝔛 → Ø 𝔞)
    {𝔠} {ℭ : 𝔛 → Ø 𝔠}
    ⦃ _ : [𝓢urjectivity] 𝔄 (Extension ℭ) ⦄
    ⦃ _ : 𝓢urjectivity 𝔄 (Extension ℭ) ⦄
    → ∀ {m} → ℭ m → ℭ m → Ṗroperty ∅̂ (𝔄 m)
  ≡-Unifies₀⟦ _ ⟧ = ≡-Unifies₀

  ExtensionalUnifies : ∀
    {𝔵} {𝔛 : Ø 𝔵}
    {𝔞} {𝔄 : 𝔛 → Ø 𝔞}
    {𝔟} {𝔅 : 𝔛 → Ø 𝔟}
    (let _↦_ = Arrow 𝔄 𝔅)
    {𝔠} {ℭ : 𝔛 → Ø 𝔠}
    {ℓ₁} (_∼₁_ : ∀ {y} → 𝔅 y → 𝔅 y → Ø ℓ₁)
    {ℓ₂} {_∼₂_ : ∀ {y} → ℭ y → ℭ y → Ø ℓ₂}
    ⦃ _ : ∀ {y} → 𝓢ymmetry (_∼₂_ {y}) ⦄
    ⦃ _ : ∀ {y} → 𝓣ransitivity (_∼₂_ {y}) ⦄
    ⦃ _ : [𝓢urjectivity] _↦_ (Extension ℭ) ⦄
    ⦃ _ : 𝓢urjectivity _↦_ (Extension ℭ) ⦄
    ⦃ _ : [𝓢urjextensionality] _↦_ (Pointwise _∼₁_) (Extension ℭ) (Pointwise _∼₂_) ⦄
    ⦃ _ : 𝓢urjextensionality _↦_ (Pointwise _∼₁_) (Extension ℭ) (Pointwise _∼₂_) ⦄
    → ∀ {m} → ℭ m → ℭ m → ArrowExtensionṖroperty 𝔄 𝔅 ℓ₂ _∼₁_ m
  ExtensionalUnifies _ {_∼₂_ = _∼₂_} s t =
    Unifies₀ _∼₂_ s t , λ f≐g f◃s=f◃t →
      ⟪ f≐g ⟫[ Pointwise _∼₂_ ] t ∙ f◃s=f◃t ∙ symmetry (⟪ f≐g ⟫[ Pointwise _∼₂_ ] s)

  ≡-ExtensionalUnifies : ∀
    {𝔵} {𝔛 : Ø 𝔵}
    {𝔞} {𝔄 : 𝔛 → Ø 𝔞}
    {𝔟} {𝔅 : 𝔛 → Ø 𝔟}
    (let _↦_ = Arrow 𝔄 𝔅)
    {𝔠} {ℭ : 𝔛 → Ø 𝔠}
    {ℓ₂} {_∼₂_ : ∀ {y} → ℭ y → ℭ y → Ø ℓ₂}
    ⦃ _ : ∀ {y} → 𝓢ymmetry (_∼₂_ {y}) ⦄
    ⦃ _ : ∀ {y} → 𝓣ransitivity (_∼₂_ {y}) ⦄
    ⦃ _ : [𝓢urjectivity] _↦_ (Extension ℭ) ⦄
    ⦃ _ : 𝓢urjectivity _↦_ (Extension ℭ) ⦄
    ⦃ _ : [𝓢urjextensionality] _↦_ (Pointwise _≡_) (Extension ℭ) (Pointwise _∼₂_) ⦄
    ⦃ _ : 𝓢urjextensionality _↦_ (Pointwise _≡_) (Extension ℭ) (Pointwise _∼₂_) ⦄
    → ∀ {m} → ℭ m → ℭ m → ArrowExtensionṖroperty 𝔄 𝔅 ℓ₂ _≡_ m
  ≡-ExtensionalUnifies {𝔄 = 𝔄} {𝔅 = 𝔅} {_∼₂_ = _∼₂_} s t = ExtensionalUnifies {𝔄 = 𝔄} {𝔅 = 𝔅} _≡_ {_∼₂_ = _∼₂_} s t

module _ {𝔭} (𝔓 : Ø 𝔭) where

  open Substitunction 𝔓
  open Term 𝔓
  open Substitist 𝔓

  prop-id-Substitunction : ∀ {m n ℓ} {f : Substitunction m n} (P : LeftExtensionṖroperty Substitunction ℓ Proposextensequality m) (let P₀ = π₀ P) → P₀ f → P₀ (ε ∙ f)
  prop-id-Substitunction = prop-id

  ≡-Unifies₀-Term : ∀ {m} → Term m → Term m → Ṗroperty ∅̂ (Arrow Fin Term m)
  ≡-Unifies₀-Term = ≡-Unifies₀

  ≡-Unifies₀-Terms : ∀ {N m} → Terms N m → Terms N m → Ṗroperty ∅̂ (Arrow Fin Term m)
  ≡-Unifies₀-Terms = λ x → ≡-Unifies₀ x

  ≡-ExtensionalUnifies-Term : ∀ {m} → Term m → Term m → ArrowExtensionṖroperty Fin Term ∅̂ _≡_ m
  ≡-ExtensionalUnifies-Term = ≡-ExtensionalUnifies

  ≡-ExtensionalUnifies-Terms : ∀ {N m} → Terms N m → Terms N m → LeftExtensionṖroperty (Arrow Fin Term) ∅̂ (Pointwise Proposequality) m
  ≡-ExtensionalUnifies-Terms = ExtensionalUnifies _≡_

module _
  {𝔵} {𝔛 : Ø 𝔵}
  {𝔬} {𝔒 : 𝔛 → Ø 𝔬}
  {ℓ : Ł}
  where

  ṖropertyEquivalence : Ṗroperty ℓ 𝔒 → Ṗroperty ℓ 𝔒 → Ø 𝔵 ∙̂ 𝔬 ∙̂ ℓ
  ṖropertyEquivalence P Q = ∀ {n f} → (P {n} f → Q f) × (Q f → P f)

  instance

    𝓡eflexivityṖroperty : 𝓡eflexivity ṖropertyEquivalence
    𝓡eflexivityṖroperty .𝓡eflexivity.reflexivity = ¡ , ¡

    𝓢ymmetryṖroperty : 𝓢ymmetry ṖropertyEquivalence
    𝓢ymmetryṖroperty .𝓢ymmetry.symmetry P⇔Q = π₁ P⇔Q , π₀ P⇔Q

    𝓣ransitivityṖroperty : 𝓣ransitivity ṖropertyEquivalence
    𝓣ransitivityṖroperty .𝓣ransitivity.transitivity P⇔Q Q⇔R = π₀ Q⇔R ∘ π₀ P⇔Q , π₁ P⇔Q ∘ π₁ Q⇔R

    IsEquivalenceṖroperty : IsEquivalence ṖropertyEquivalence
    IsEquivalenceṖroperty = ∁

instance

  HasEquivalenceṖroperty : ∀
    {𝔵} {𝔛 : Ø 𝔵}
    {𝔬} {𝔒 : 𝔛 → Ø 𝔬}
    {ℓ}
    → HasEquivalence (Ṗroperty ℓ 𝔒) (𝔵 ∙̂ 𝔬 ∙̂ ℓ)
  HasEquivalenceṖroperty .HasEquivalence.Equivalence P Q = ṖropertyEquivalence (λ {x} → P {x}) Q -- ∀ {n f} → (P {n} f → Q f) × (Q f → P f)

instance

  ProperthingṖroperty : ∀
    {𝔵} {𝔛 : Ø 𝔵}
    {𝔬} {𝔒 : 𝔛 → Ø 𝔬}
    {ℓ}
    → Properthing (𝔵 ∙̂ 𝔬 ∙̂ ℓ) (Ṗroperty ℓ 𝔒)
  ProperthingṖroperty .Properthing._∧_ P Q f = P f × Q f
  ProperthingṖroperty .Properthing._⇔_ P Q = ∀ {n f} → (P {n} f → Q f) × (Q f → P f)
  -- ProperthingṖroperty .Properthing.Symmetry⇔ .𝓢ymmetry.symmetry P⇔Q = π₁ P⇔Q , π₀ P⇔Q
  ProperthingṖroperty {𝔒 = 𝔒} .Properthing.Nothing P = ∀ {n} {f : 𝔒 n} → P f → 𝟘
  ProperthingṖroperty .Properthing.fact2 P⇔Q NoP Q = NoP $ π₁ P⇔Q Q

module _
  {𝔵} {𝔛 : Ø 𝔵}
  {𝔬} {𝔒 : 𝔛 → Ø 𝔬}
  {ℓ}
  {ℓ̇} {_↦_ : ∀ {x} → 𝔒 x → 𝔒 x → Ø ℓ̇}
  where

  ExtensionṖropertyEquivalence : ExtensionṖroperty 𝔒 ℓ _↦_ → ExtensionṖroperty 𝔒 ℓ _↦_ → Ø 𝔵 ∙̂ 𝔬 ∙̂ ℓ
  ExtensionṖropertyEquivalence P Q = (λ {x} → π₀ P {x}) ⇔ π₀ Q

  instance

    𝓡eflexivityExtensionṖroperty : 𝓡eflexivity ExtensionṖropertyEquivalence
    𝓡eflexivityExtensionṖroperty .𝓡eflexivity.reflexivity = ¡ , ¡

    𝓢ymmetryExtensionṖroperty : 𝓢ymmetry ExtensionṖropertyEquivalence
    𝓢ymmetryExtensionṖroperty .𝓢ymmetry.symmetry P⇔Q = π₁ P⇔Q , π₀ P⇔Q

  𝓣ransitivityExtensionṖroperty' : 𝓣ransitivity ExtensionṖropertyEquivalence
  𝓣ransitivityExtensionṖroperty' .𝓣ransitivity.transitivity P⇔Q Q⇔R = transitivity (λ {x} {f} → P⇔Q {x} {f}) Q⇔R

  instance

    𝓣ransitivityExtensionṖroperty : 𝓣ransitivity ExtensionṖropertyEquivalence
    𝓣ransitivityExtensionṖroperty = 𝓣ransitivityExtensionṖroperty'

    IsEquivalenceExtensionṖroperty : IsEquivalence ExtensionṖropertyEquivalence
    IsEquivalenceExtensionṖroperty = ∁

  instance

    ProperthingExtensionṖroperty : Properthing (𝔵 ∙̂ 𝔬 ∙̂ ℓ) (ExtensionṖroperty 𝔒 ℓ _↦_)
    ProperthingExtensionṖroperty .Properthing._∧_ P Q = (λ _ → π₀ P _ × π₀ Q _) , λ f≐g Pf×Qf → π₁ P f≐g (π₀ Pf×Qf) , π₁ Q f≐g (π₁ Pf×Qf)
    ProperthingExtensionṖroperty .Properthing._⇔_ P Q = ExtensionṖropertyEquivalence P Q -- ExtensionṖropertyEquivalence P Q -- (λ {x} → π₀ P {x}) ⇔ π₀ Q
    --ProperthingExtensionṖroperty .Properthing.Symmetry⇔ .𝓢ymmetry.symmetry P⇔Q = π₁ P⇔Q , π₀ P⇔Q
    ProperthingExtensionṖroperty .Properthing.Nothing P = ∀ {n} {f : 𝔒 n} → π₀ P f → 𝟘
    ProperthingExtensionṖroperty .Properthing.fact2 P⇔Q NoP Q = NoP $ π₁ P⇔Q Q

{-
module _
  {𝔵} {𝔛 : Ø 𝔵}
  {𝔬} {𝔒 : 𝔛 → Ø 𝔬}
  {ℓ : Ł}
  where

  instance

    𝓡eflexivityṖroperty : 𝓡eflexivity (_⇔_ {ℓ = (𝔵 ∙̂ 𝔬 ∙̂ ℓ)} {𝔒 = (Ṗroperty 𝔒 ℓ)})
    𝓡eflexivityṖroperty .𝓡eflexivity.reflexivity = ¡ , ¡
-}

instance

  ṖropertySurjectivity : ∀
    {𝔵} {𝔛 : Ø 𝔵}
    {𝔯} {_↦_ : 𝔛 → 𝔛 → Ø 𝔯}
    {ℓ : Ł}
    ⦃ _ : 𝓣ransitivity _↦_ ⦄
    ⦃ _ : [𝓢urjectivity] _↦_ (Extension $ LeftṖroperty ℓ _↦_) ⦄
    → 𝓢urjectivity _↦_ (Extension $ LeftṖroperty ℓ _↦_)
  ṖropertySurjectivity .𝓢urjectivity.surjectivity f P g = P (g ∙ f)

instance

  ExtensionṖropertySurjectivity : ∀
    {𝔵} {𝔛 : Ø 𝔵}
    {𝔞} {𝔒₁ : 𝔛 → Ø 𝔞}
    {𝔟} {𝔒₂ : 𝔛 → Ø 𝔟}
    (let _∼_ = Arrow 𝔒₁ 𝔒₂)
    {ℓ}
    {ℓ̇} {_↦_ : Ṙelation ℓ̇ 𝔒₂}
    ⦃ _ : [ExtensibleType] (λ {x} → _↦_ {x}) ⦄
    ⦃ _ : [𝓢urjectivity] _∼_ (Extension 𝔒₂) ⦄
    ⦃ _ : 𝓢urjectivity _∼_ (Extension 𝔒₂) ⦄
    ⦃ _ : [𝓢urjextensionality] _∼_ (Pointwise _↦_) (Extension 𝔒₂) (Pointwise _↦_) ⦄
    ⦃ _ : 𝓢urjextensionality _∼_ (Pointwise _↦_) (Extension 𝔒₂) (Pointwise _↦_) ⦄
    ⦃ _ : [𝓢urjectivity] _∼_ (Extension $ LeftExtensionṖroperty _∼_ ℓ (Pointwise _↦_)) ⦄
    → 𝓢urjectivity _∼_ (Extension $ LeftExtensionṖroperty _∼_ ℓ (Pointwise _↦_))
  ExtensionṖropertySurjectivity .𝓢urjectivity.surjectivity f P = (λ g → π₀ P (surjectivity g ∘ f)) , (λ f≐g Pf'◇f → π₁ P (surjextensionality f≐g ∘ f) Pf'◇f)

instance

  [ExtensibleType]Proposequality : ∀ {a} {b} {A : Set a} {B : A → Set b} → [ExtensibleType] (λ {w} → Proposequality⟦ B w ⟧)
  [ExtensibleType]Proposequality = ∁

  [𝓢urjectivity]ArrowE : ∀ {ℓ} {a} {f} {t} {¶ : Set a} {Fin : ¶ → Set f} {Term : ¶ → Set t} → [𝓢urjectivity] (Arrow Fin Term) (Extension $ LeftExtensionṖroperty (Arrow Fin Term) ℓ _≡̇_)
  [𝓢urjectivity]ArrowE = ∁

  [𝓢urjectivity]LeftṖroperty : ∀ {ℓ} {a} {f} {¶ : Set a} {_↦_ : ¶ → ¶ → Set f} → [𝓢urjectivity] _↦_ (Extension $ LeftṖroperty ℓ _↦_)
  [𝓢urjectivity]LeftṖroperty = ∁

module Test where
  postulate 𝔓 : Set
  postulate ℓ : Ł
  open Term 𝔓
  open Substitunction 𝔓

  test-epfs : ∀ {x y} → LeftExtensionṖroperty Substitunction ℓ Proposextensequality x → Arrow Fin Term x y → LeftExtensionṖroperty (Arrow Fin Term) ℓ _≡̇_ y
  test-epfs P f = f ◃ P

  test-epfs' : ∀ {x y} → ArrowṖroperty ℓ Fin Term x → Substitunction x y → ArrowṖroperty ℓ Fin Term y
  test-epfs' P f = f ◃ (λ {_} → P)

  fact1U : ∀ {m} {s t : Term m} → ≡-Unifies₀ s t ⇔[ ArrowṖroperty _ Fin Term _ ] ≡-Unifies₀ t s
  fact1U = symmetry , symmetry

  fact1U-test2 : ∀ {m} {s t : Term m} → (λ {x} → ≡-Unifies₀⟦ Substitunction ⟧ s t {x}) ⇔ ≡-Unifies₀ t s
  fact1U-test2 = symmetry , symmetry

  Properties-fact1 : ∀ {m} {s t : Term m} → ≡-ExtensionalUnifies {𝔄 = Fin} s t ⇔ ≡-ExtensionalUnifies t s
  Properties-fact1 = symmetry , symmetry

  Properties-fact1-test2 : ∀ {m} {s t : Term m} → ≡-ExtensionalUnifies s t ⇔[ LeftExtensionṖroperty Substitunction _ Proposextensequality _ ] ≡-ExtensionalUnifies t s
  Properties-fact1-test2 = symmetry , symmetry

  Properties-fact1'⋆ : ∀ {m} {s1 s2 t1 t2 : Term m}
         → (λ {m} → ≡-Unifies₀⟦ Arrow Fin Term ⟧ (s1 fork s2) (t1 fork t2) {m}) ⇔ ((λ {m} → ≡-Unifies₀ s1 t1 {m}) ∧ ≡-Unifies₀ s2 t2)
  Properties-fact1'⋆ = (λ s≡t → injectivity₂,₀,₁ s≡t , injectivity₂,₀,₂ s≡t) , uncurry (congruity₂ _fork_)

  Properties-fact1' : ∀ {m} {s1 s2 t1 t2 : Term m}
         → ≡-ExtensionalUnifies (s1 fork s2) (t1 fork t2) ⇔[ ExtensionṖroperty (Substitunction _) _ _ ] (≡-ExtensionalUnifies s1 t1 ∧ ≡-ExtensionalUnifies s2 t2)
  Properties-fact1' = (λ s≡t → injectivity₂,₀,₁ s≡t , injectivity₂,₀,₂ s≡t) , uncurry (congruity₂ _fork_)

  fact3 : ∀ {m} {P : ExtensionṖroperty (Arrow Fin Term m) ℓ (λ {y} → Pointwise Proposequality⟦ Term y ⟧)} → P ⇔ (i ◃ P)
  fact3 = ¡ , ¡

  fact4 : ∀{m n} {P : LeftExtensionṖroperty (Arrow Fin Term) ℓ Proposextensequality m} (f : _ → Term n)
          → Nothing P → Nothing (f ◃ P)
  fact4 f nop {f = g} Pf = nop {f = g ∙[ Arrow Fin Term ] f} Pf

  fact5⋆ : ∀{m n} {P Q : ArrowṖroperty ℓ Fin Term m} {f : Arrow Fin Term m n} → (λ {x} → P {x}) ⇔ Q
           → ((f ◃[ ArrowṖroperty _ Fin Term ] P)) ⇔[ ArrowṖroperty _ Fin Term _ ] (f ◃ λ {_} → Q)
  fact5⋆ P⇔Q = P⇔Q

  fact5 : ∀{m n} {P Q : LeftExtensionṖroperty Substitunction ℓ Proposextensequality m} {f : Arrow Fin Term m n} → P ⇔ Q
           → (f ◃ P) ⇔ (f ◃ Q)
  fact5 P⇔Q = P⇔Q

  fact6 : ∀{m n} (P : LeftExtensionṖroperty (Arrow Fin Term) ℓ Proposextensequality m) {f g : Arrow Fin Term m n} → f ≡̇ g → (f ◃ P) ⇔ (g ◃ P)
  fact6 P f≐g {f = h} = π₁ P (congruity (surjectivity h) ∘ f≐g) , π₁ P (symmetry (congruity (surjectivity h) ∘ f≐g))
