{-# OPTIONS --show-implicit #-}
{-# OPTIONS --postfix-projections #-}
module Oscar.Property where

open import Oscar.Prelude
open import Oscar.Class
open import Oscar.Data

module _ where

  module _ {𝔬} {𝔒 : Ø 𝔬} where

    instance

      𝓡eflexivityProposequality : 𝓡eflexivity Proposequality⟦ 𝔒 ⟧
      𝓡eflexivityProposequality .𝓡eflexivity.reflexivity = !

      𝓢ymmetryProposequality : 𝓢ymmetry Proposequality⟦ 𝔒 ⟧
      𝓢ymmetryProposequality .𝓢ymmetry.symmetry ∅ = !

      𝓣ransitivityProposequality : 𝓣ransitivity Proposequality⟦ 𝔒 ⟧
      𝓣ransitivityProposequality .𝓣ransitivity.transitivity ∅ = ¡

{-
      IsEquivalenceProposequality : IsEquivalence Proposequality⟦ 𝔒 ⟧
      IsEquivalenceProposequality .IsEquivalence.⌶𝓡eflexivity = !
      IsEquivalenceProposequality .IsEquivalence.⌶𝓢ymmetry = !
      IsEquivalenceProposequality .IsEquivalence.⌶𝓣ransitivity = !
-}

--   instance

--     𝓒ongruity∁Proposequality : ∀ {a b} → 𝓒ongruity∁ a b Proposequality
--     𝓒ongruity∁Proposequality .𝓒ongruity∁.congruity _ ∅ = !

--     𝓒ongruity₂∁Proposequality : ∀ {a b c} → 𝓒ongruity₂∁ a b c Proposequality
--     𝓒ongruity₂∁Proposequality .𝓒ongruity₂∁.congruity₂ _ ∅ ∅ = !

--     𝓣ransextensionality∁Proposequality : ∀
--       {a} {A : Ø a}
--       {m} {_⊸_ : A → A → Ø m}
--       ⦃ _ : 𝓣ransitivity∁ _⊸_ ⦄
--       → 𝓣ransextensionality∁ _⊸_ Proposequality
--     𝓣ransextensionality∁Proposequality .𝓣ransextensionality∁.⌶𝓣ransitivity∁ = !
--     𝓣ransextensionality∁Proposequality .𝓣ransextensionality∁.⌶𝓣ransextensionality/ .𝓣ransextensionality/.transextensionality = congruity₂ _

-- -- module _ where

-- --   module _ {𝔬} (𝔒 : Ø 𝔬) where

-- --     SetoidProposequality : Setoid _ _
-- --     Setoid.Object SetoidProposequality = _
-- --     Setoid.ObjectEquality SetoidProposequality = Proposequality⟦ 𝔒 ⟧
-- --     Setoid.isEquivalence SetoidProposequality = !

-- -- module _ where

-- --   module _ {𝔬} {𝔒 : Ø 𝔬} {𝔭} {𝔓 : 𝔒 → Ø 𝔭} where

-- --     instance

-- --       𝓡eflexivity∁Proposextensequality : 𝓡eflexivity∁ Proposextensequality⟦ 𝔓 ⟧
-- --       𝓡eflexivity∁.reflexivity 𝓡eflexivity∁Proposextensequality _ = ∅

-- --       𝓢ymmetry∁Proposextensequality : 𝓢ymmetry∁ Proposextensequality⟦ 𝔓 ⟧
-- --       𝓢ymmetry∁.symmetry 𝓢ymmetry∁Proposextensequality f₁≡̇f₂ x rewrite f₁≡̇f₂ x = ∅

-- --       𝓣ransitivity∁Proposextensequality : 𝓣ransitivity∁ Proposextensequality⟦ 𝔓 ⟧
-- --       𝓣ransitivity∁.transitivity 𝓣ransitivity∁Proposextensequality f₁≡̇f₂ f₂≡̇f₃ x rewrite f₁≡̇f₂ x = f₂≡̇f₃ x

-- --       IsEquivalence∁Proposextensequality : IsEquivalence∁ Proposextensequality⟦ 𝔓 ⟧
-- --       IsEquivalence∁.⌶𝓡eflexivity∁ IsEquivalence∁Proposextensequality = !
-- --       IsEquivalence∁.⌶𝓢ymmetry∁ IsEquivalence∁Proposextensequality = !
-- --       IsEquivalence∁.⌶𝓣ransitivity∁ IsEquivalence∁Proposextensequality = !

-- --       IsĊongruousProposextensequality : ∀ {a b} → IsĊongruous a b Proposextensequality
-- --       IsĊongruous.ċongruity IsĊongruousProposextensequality _ f≡̇g x rewrite f≡̇g x = ∅

-- -- module _ where

-- --   module _ {𝔬} {𝔒 : Ø 𝔬} {𝔭} (𝔓 : 𝔒 → Ø 𝔭) where

-- --     SetoidProposextensequality : Setoid _ _
-- --     Setoid.Object SetoidProposextensequality = _
-- --     Setoid.ObjectEquality SetoidProposextensequality = Proposextensequality⟦ 𝔓 ⟧
-- --     Setoid.isEquivalence SetoidProposextensequality = !

-- -- module _ where

-- --   module _
-- --     {a}
-- --     where

-- --     instance

-- --       𝓡eflexivity∁Function : 𝓡eflexivity∁ Function⟦ a ⟧
-- --       𝓡eflexivity∁.reflexivity 𝓡eflexivity∁Function = ¡

-- --       𝓣ransitivity∁Function : 𝓣ransitivity∁ Function⟦ a ⟧
-- --       𝓣ransitivity∁.transitivity 𝓣ransitivity∁Function f g = g ∘ f

-- -- module _ where

-- --   module _
-- --     {a} {A : Ø a} {b} {B : A → Ø b}
-- --     where

-- --     instance

-- --       𝓡eflexivity∁Extension : 𝓡eflexivity∁ (Extension B)
-- --       𝓡eflexivity∁.reflexivity 𝓡eflexivity∁Extension = ¡

-- --       𝓣ransitivity∁Extension : 𝓣ransitivity∁ (Extension B)
-- --       𝓣ransitivity∁.transitivity 𝓣ransitivity∁Extension f g = g ∘ f

-- --       IsTransassociativeExtension : IsTransassociative (Extension B) Proposextensequality
-- --       IsTransassociative.⌶𝓣ransitivity∁ IsTransassociativeExtension = !
-- --       IsTransassociative.transassociativity IsTransassociativeExtension _ _ _ _ = !

-- --       𝓣ransextensionality∁Extensional : 𝓣ransextensionality∁ (Extension B) (λ {x} {y} → Proposextensequality)
-- --       𝓣ransextensionality∁.⌶𝓣ransitivity∁ 𝓣ransextensionality∁Extensional = !
-- --       𝓣ransextensionality∁.transextensionality 𝓣ransextensionality∁Extensional {f₂ = f₂} f₁≡̇f₂ g₁≡̇g₂ x rewrite f₁≡̇f₂ x = g₁≡̇g₂ (f₂ x)

-- --       IsTransleftidentityExtension : IsTransleftidentity (Extension B) Proposextensequality
-- --       IsTransleftidentity.⌶𝓡eflexivity∁ IsTransleftidentityExtension = !
-- --       IsTransleftidentity.⌶𝓣ransitivity∁ IsTransleftidentityExtension = !
-- --       IsTransleftidentity.transleftidentity IsTransleftidentityExtension _ = !

-- --       IsTransrightidentityExtension : IsTransrightidentity (Extension B) Proposextensequality
-- --       IsTransrightidentity.⌶𝓡eflexivity∁ IsTransrightidentityExtension = !
-- --       IsTransrightidentity.⌶𝓣ransitivity∁ IsTransrightidentityExtension = !
-- --       IsTransrightidentity.transrightidentity IsTransrightidentityExtension _ = !

-- --       -- EqualityExtension : ∀ {x y : A} → Equality (Extension B x y) _
-- --       -- EqualityExtension .Equality._≋_ = Proposextensequality
-- --       -- EqualityExtension .Equality.isEquivalence = it

-- --   module _
-- --     {a} {A : Ø a} {b} (B : A → Ø b)
-- --     where

-- --     PrecategoryExtension : Precategory _ _ _
-- --     Precategory.Object PrecategoryExtension = _
-- --     Precategory.Arrow PrecategoryExtension = Extension B
-- --     Precategory.ArrowEquality PrecategoryExtension = Proposextensequality
-- --     Precategory.⌶𝓣ransitivity∁ PrecategoryExtension = !
-- --     Precategory.isEquivalence PrecategoryExtension = !
-- --     Precategory.isTransassociative PrecategoryExtension = !
-- --     Precategory.isTransextensional PrecategoryExtension = !
-- --     Precategory.⌶𝓣ransitivity∁∈isTransassociative PrecategoryExtension = !
-- --     Precategory.⌶𝓣ransitivity∁∈isTransextensional PrecategoryExtension = !

-- --     CategoryExtension : Category _ _ _
-- --     Category.precategory CategoryExtension = PrecategoryExtension
-- --     Category.isTransleftidentity CategoryExtension = it
-- --     Category.isTransrightidentity CategoryExtension = it
-- --     Category.⌶𝓣ransitivity∁∈isTransleftidentity CategoryExtension = !
-- --     Category.⌶𝓣ransitivity∁∈isTransrightidentity CategoryExtension = !
-- --     Category.⌶𝓡eflexivity∁∈Transleftidentity≡⌶𝓡eflexivity∁Transrightidentity CategoryExtension = !

-- -- record Substitunction⌶ {𝔭} (𝔓 : Ø 𝔭) : Ø₀ where
-- --   no-eta-equality

-- --   open Substitunction 𝔓
-- --   open Term 𝔓

-- --   private

-- --     mutual

-- --       𝓶apSubstitunctionExtensionTerm : 𝓶ap Substitunction (Extension Term) ¡
-- --       𝓶apSubstitunctionExtensionTerm σ (i x) = σ x
-- --       𝓶apSubstitunctionExtensionTerm σ leaf = leaf
-- --       𝓶apSubstitunctionExtensionTerm σ (τ₁ fork τ₂) = 𝓶apSubstitunctionExtensionTerm σ τ₁ fork 𝓶apSubstitunctionExtensionTerm σ τ₂
-- --       𝓶apSubstitunctionExtensionTerm σ (function p τs) = function p (𝓶apSubstitunctionExtensionTerms σ τs)

-- --       𝓶apSubstitunctionExtensionTerms : ∀ {N} → 𝓶ap Substitunction (Extension $ Terms N) ¡
-- --       𝓶apSubstitunctionExtensionTerms σ ∅ = ∅
-- --       𝓶apSubstitunctionExtensionTerms σ (τ , τs) = 𝓶apSubstitunctionExtensionTerm σ τ , 𝓶apSubstitunctionExtensionTerms σ τs

-- --   instance

-- --     IsMappableSubstitunctionExtensionTerm : IsMappable Substitunction (Extension Term)
-- --     IsMappable.μ IsMappableSubstitunctionExtensionTerm = _
-- --     IsMappable.map IsMappableSubstitunctionExtensionTerm = 𝓶apSubstitunctionExtensionTerm

-- --     IsMappableSubstitunctionExtensionTerms : ∀ {N} → IsMappable Substitunction (Extension $ Terms N)
-- --     IsMappableSubstitunctionExtensionTerms .IsMappable.μ = _
-- --     IsMappableSubstitunctionExtensionTerms .IsMappable.map = 𝓶apSubstitunctionExtensionTerms

-- --     𝓣ransitivity∁Substitunction : 𝓣ransitivity∁ Substitunction
-- --     𝓣ransitivity∁Substitunction .𝓣ransitivity∁.transitivity f g = map g ∘ f

-- --     EqualitySubstitunction : ∀ {x y} → Equality (Substitunction x y) _
-- --     EqualitySubstitunction {x} {y} .Equality._≋_ = Proposextensequality
-- --     EqualitySubstitunction {x} {y} .Equality.isEquivalence = it

-- --     EqualityExtensionTerm : ∀ {x y} → Equality (Extension Term x y) _
-- --     EqualityExtensionTerm .Equality._≋_ = Proposextensequality
-- --     EqualityExtensionTerm .Equality.isEquivalence = it

-- --     EqualityExtensionTerms : ∀ {N x y} → Equality (Extension (Terms N) x y) _
-- --     EqualityExtensionTerms .Equality._≋_ = Proposextensequality
-- --     EqualityExtensionTerms .Equality.isEquivalence = it

-- --   private

-- --     mutual

-- --       𝓶apextensionalitySubstitunctionExtensionTerm : 𝓶apextensionality! Substitunction (Extension Term)
-- --       𝓶apextensionalitySubstitunctionExtensionTerm p (i x) = p x
-- --       𝓶apextensionalitySubstitunctionExtensionTerm p leaf = ∅
-- --       𝓶apextensionalitySubstitunctionExtensionTerm p (s fork t) = congruity₂ _fork_ (𝓶apextensionalitySubstitunctionExtensionTerm p s) (𝓶apextensionalitySubstitunctionExtensionTerm p t)
-- --       𝓶apextensionalitySubstitunctionExtensionTerm p (function fn ts) = congruity (function fn) (𝓶apextensionalitySubstitunctionExtensionTerms p ts)

-- --       𝓶apextensionalitySubstitunctionExtensionTerms : ∀ {N} → 𝓶apextensionality! Substitunction (Extension $ Terms N)
-- --       𝓶apextensionalitySubstitunctionExtensionTerms p ∅ = ∅
-- --       𝓶apextensionalitySubstitunctionExtensionTerms p (t , ts) = congruity₂ _,_ (𝓶apextensionalitySubstitunctionExtensionTerm p t) (𝓶apextensionalitySubstitunctionExtensionTerms p ts)

-- --   instance

-- --     --IsMapextensionalSubstitunction : IsMapextensional Substitunction Proposextensequality (Extension Term) Proposextensequality
-- --     IsMapextensionalSubstitunction : IsMapextensional! Substitunction (Extension Term)
-- --     IsMapextensional.isMappable IsMapextensionalSubstitunction = !
-- --     IsMapextensional.mapextensionality IsMapextensionalSubstitunction = 𝓶apextensionalitySubstitunctionExtensionTerm

-- --     IsMapextensionalSubstitunctions : ∀ {N} → IsMapextensional! Substitunction (Extension $ Terms N)
-- --     IsMapextensionalSubstitunctions .IsMapextensional.isMappable = it
-- --     IsMapextensionalSubstitunctions .IsMapextensional.mapextensionality = 𝓶apextensionalitySubstitunctionExtensionTerms

-- --   private

-- --     mutual

-- --       𝓶aptranscommutativitySubstitunctionExtensionTerm : 𝓶aptranscommutativity! Substitunction (Extension Term) ! ! ! !
-- --       𝓶aptranscommutativitySubstitunctionExtensionTerm _ _ (i _) = !
-- --       𝓶aptranscommutativitySubstitunctionExtensionTerm _ _ leaf = !
-- --       𝓶aptranscommutativitySubstitunctionExtensionTerm _ _ (τ₁ fork τ₂) = congruity₂ _fork_ (𝓶aptranscommutativitySubstitunctionExtensionTerm _ _ τ₁) (𝓶aptranscommutativitySubstitunctionExtensionTerm _ _ τ₂)
-- --       𝓶aptranscommutativitySubstitunctionExtensionTerm f g (function fn ts) = congruity (function fn) (𝓶aptranscommutativitySubstitunctionExtensionTerms f g ts)

-- --       𝓶aptranscommutativitySubstitunctionExtensionTerms : ∀ {N} → 𝓶aptranscommutativity! Substitunction (Extension $ Terms N) ! ! ! !
-- --       𝓶aptranscommutativitySubstitunctionExtensionTerms _ _ ∅ = !
-- --       𝓶aptranscommutativitySubstitunctionExtensionTerms _ _ (τ , τs) = congruity₂ _,_ (𝓶aptranscommutativitySubstitunctionExtensionTerm _ _ τ) (𝓶aptranscommutativitySubstitunctionExtensionTerms _ _ τs)

-- --   instance

-- --     IsMaptranscommutativeSubstitunctionExtensionTerm : IsMaptranscommutative! Substitunction (Extension Term) !
-- --     IsMaptranscommutativeSubstitunctionExtensionTerm .IsMaptranscommutative.isMappable = !
-- --     IsMaptranscommutativeSubstitunctionExtensionTerm .IsMaptranscommutative.⌶𝓣ransitivity∁₁ = !
-- --     IsMaptranscommutativeSubstitunctionExtensionTerm .IsMaptranscommutative.⌶𝓣ransitivity∁₂ = !
-- --     IsMaptranscommutativeSubstitunctionExtensionTerm .IsMaptranscommutative.maptranscommutativity = 𝓶aptranscommutativitySubstitunctionExtensionTerm

-- --     IsMaptranscommutativeSubstitunctionExtensionTerms : ∀ {N} → IsMaptranscommutative! Substitunction (Extension $ Terms N) !
-- --     IsMaptranscommutativeSubstitunctionExtensionTerms .IsMaptranscommutative.isMappable = !
-- --     IsMaptranscommutativeSubstitunctionExtensionTerms .IsMaptranscommutative.⌶𝓣ransitivity∁₁ = !
-- --     IsMaptranscommutativeSubstitunctionExtensionTerms .IsMaptranscommutative.⌶𝓣ransitivity∁₂ = !
-- --     IsMaptranscommutativeSubstitunctionExtensionTerms .IsMaptranscommutative.maptranscommutativity = 𝓶aptranscommutativitySubstitunctionExtensionTerms

-- --   instance

-- --     IsTransassociativeSubstitunction : IsTransassociative Substitunction _≋_
-- --     IsTransassociativeSubstitunction .IsTransassociative.⌶𝓣ransitivity∁ = !
-- --     IsTransassociativeSubstitunction .IsTransassociative.transassociativity f g h = maptranscommutativity g h ∘ f

-- --     𝓣ransextensionality∁Substitunction : 𝓣ransextensionality∁ Substitunction _≋_
-- --     𝓣ransextensionality∁Substitunction .𝓣ransextensionality∁.⌶𝓣ransitivity∁ = !
-- --     𝓣ransextensionality∁Substitunction .𝓣ransextensionality∁.transextensionality {f₂ = f₂} f₁≡̇f₂ g₁≡̇g₂ x rewrite f₁≡̇f₂ x = mapextensionality g₁≡̇g₂ $ f₂ x

-- --   PrecategorySubstitunction : Precategory _ _ _
-- --   PrecategorySubstitunction .Precategory.Object = _
-- --   PrecategorySubstitunction .Precategory.Arrow = Substitunction
-- --   PrecategorySubstitunction .Precategory.ArrowEquality = _≋_
-- --   PrecategorySubstitunction .Precategory.⌶𝓣ransitivity∁ = !
-- --   PrecategorySubstitunction .Precategory.isEquivalence = !
-- --   PrecategorySubstitunction .Precategory.isTransassociative = !
-- --   PrecategorySubstitunction .Precategory.isTransextensional = !
-- --   PrecategorySubstitunction .Precategory.⌶𝓣ransitivity∁∈isTransassociative = !
-- --   PrecategorySubstitunction .Precategory.⌶𝓣ransitivity∁∈isTransextensional = !

-- --   instance

-- --     IsPrefunctorSubstitunctionExtensionTerm : IsPrefunctor PrecategorySubstitunction (PrecategoryExtension Term)
-- --     IsPrefunctorSubstitunctionExtensionTerm .IsPrefunctor.isMappable = !
-- --     IsPrefunctorSubstitunctionExtensionTerm .IsPrefunctor.isMapextensional = !
-- --     IsPrefunctorSubstitunctionExtensionTerm .IsPrefunctor.isMaptranscommutative = !
-- --     IsPrefunctorSubstitunctionExtensionTerm .IsPrefunctor.isMappable∈isMapextensional = !
-- --     IsPrefunctorSubstitunctionExtensionTerm .IsPrefunctor.isMappable∈isMaptranscommutative = !
-- --     IsPrefunctorSubstitunctionExtensionTerm .IsPrefunctor.⌶𝓣ransitivity∁₁∈isMaptranscommutative = !
-- --     IsPrefunctorSubstitunctionExtensionTerm .IsPrefunctor.⌶𝓣ransitivity∁₂∈isMaptranscommutative = !

-- --     IsPrefunctorSubstitunctionExtensionTermSC : IsPrefunctorSC PrecategorySubstitunction (PrecategoryExtension Term)
-- --     IsPrefunctorSubstitunctionExtensionTermSC

-- --     IsPrefunctorSubstitunctionExtensionTerms : ∀ {N} → IsPrefunctor PrecategorySubstitunction (PrecategoryExtension $ Terms N)
-- --     IsPrefunctorSubstitunctionExtensionTerms .IsPrefunctor.isMappable = !
-- --     IsPrefunctorSubstitunctionExtensionTerms .IsPrefunctor.isMapextensional = !
-- --     IsPrefunctorSubstitunctionExtensionTerms .IsPrefunctor.isMaptranscommutative = !
-- --     IsPrefunctorSubstitunctionExtensionTerms .IsPrefunctor.isMappable∈isMapextensional = !
-- --     IsPrefunctorSubstitunctionExtensionTerms .IsPrefunctor.isMappable∈isMaptranscommutative = !
-- --     IsPrefunctorSubstitunctionExtensionTerms .IsPrefunctor.⌶𝓣ransitivity∁₁∈isMaptranscommutative = !
-- --     IsPrefunctorSubstitunctionExtensionTerms .IsPrefunctor.⌶𝓣ransitivity∁₂∈isMaptranscommutative = !

-- --   PrefunctorSubstitunctionExtensionTerm : Prefunctor _ _ _ _ _ _
-- --   PrefunctorSubstitunctionExtensionTerm .Prefunctor.precategory₁ = PrecategorySubstitunction
-- --   PrefunctorSubstitunctionExtensionTerm .Prefunctor.precategory₂ = PrecategoryExtension Term
-- --   PrefunctorSubstitunctionExtensionTerm .Prefunctor.isPrefunctor = !

-- --   PrefunctorSubstitunctionExtensionTerms : ∀ N → Prefunctor _ _ _ _ _ _
-- --   PrefunctorSubstitunctionExtensionTerms _ .Prefunctor.precategory₁ = PrecategorySubstitunction
-- --   PrefunctorSubstitunctionExtensionTerms N .Prefunctor.precategory₂ = PrecategoryExtension $ Terms N
-- --   PrefunctorSubstitunctionExtensionTerms _ .Prefunctor.isPrefunctor = !

-- -- -- -- -- -- -- -- -- -- --     ReflexivitySubstitunction : Reflexivity Substitunction
-- -- -- -- -- -- -- -- -- -- --     Reflexivity.reflexivity ReflexivitySubstitunction = i

-- -- -- -- -- -- -- -- -- -- --   private

-- -- -- -- -- -- -- -- -- -- --     mutual

-- -- -- -- -- -- -- -- -- -- --       𝓲dentitySubstitunctionExtensionTerm : 𝓲dentity Substitunction (Extension Term) _ ¡
-- -- -- -- -- -- -- -- -- -- --       𝓲dentitySubstitunctionExtensionTerm (i x) = ∅
-- -- -- -- -- -- -- -- -- -- --       𝓲dentitySubstitunctionExtensionTerm leaf = ∅
-- -- -- -- -- -- -- -- -- -- --       𝓲dentitySubstitunctionExtensionTerm (s fork t) = congruity₂ _fork_ (𝓲dentitySubstitunctionExtensionTerm s) (𝓲dentitySubstitunctionExtensionTerm t)
-- -- -- -- -- -- -- -- -- -- --       𝓲dentitySubstitunctionExtensionTerm (function fn ts) = congruity (function fn) (𝓲dentitySubstitunctionExtensionTerms ts)

-- -- -- -- -- -- -- -- -- -- --       𝓲dentitySubstitunctionExtensionTerms : ∀ {N} → 𝓲dentity Substitunction (Extension $ Terms N) _ ¡
-- -- -- -- -- -- -- -- -- -- --       𝓲dentitySubstitunctionExtensionTerms ∅ = ∅
-- -- -- -- -- -- -- -- -- -- --       𝓲dentitySubstitunctionExtensionTerms (t , ts) = congruity₂ _,_ (𝓲dentitySubstitunctionExtensionTerm t) (𝓲dentitySubstitunctionExtensionTerms ts)

-- -- -- -- -- -- -- -- -- -- --   instance

-- -- -- -- -- -- -- -- -- -- -- {-
-- -- -- -- -- -- -- -- -- -- --     Identity!SubstitunctionExtensionTerm : Identity! Substitunction (Extension Term) _ ¡
-- -- -- -- -- -- -- -- -- -- --     Identity!.identity! Identity!SubstitunctionExtensionTerm = {!!} -- 𝓲dentitySubstitunctionExtensionTerm

-- -- -- -- -- -- -- -- -- -- --     Identity!SubstitunctionExtensionTerms : ∀ {N} → Identity! Substitunction (Extension $ Terms N) _ ¡
-- -- -- -- -- -- -- -- -- -- --     Identity!.identity! Identity!SubstitunctionExtensionTerms = {!!} -- 𝓲dentitySubstitunctionExtensionTerms

-- -- -- -- -- -- -- -- -- -- --     Identity?SubstitunctionExtensionTerm : Identity? Substitunction (Extension Term) _ ¡
-- -- -- -- -- -- -- -- -- -- --     Identity?.identity? Identity?SubstitunctionExtensionTerm = 𝓲dentitySubstitunctionExtensionTerm

-- -- -- -- -- -- -- -- -- -- --     Identity?SubstitunctionExtensionTerms : ∀ {N} → Identity? Substitunction (Extension $ Terms N) _ ¡
-- -- -- -- -- -- -- -- -- -- --     Identity?.identity? Identity?SubstitunctionExtensionTerms = 𝓲dentitySubstitunctionExtensionTerms

-- -- -- -- -- -- -- -- -- -- --     LeftIdentity!Substitunction : LeftIdentity! Substitunction _
-- -- -- -- -- -- -- -- -- -- --     LeftIdentity!.left-identity! LeftIdentity!Substitunction f x = ((Term _ → Proposequality (𝓶apSubstitunctionExtensionTerm i (f x)) (f x)) ∋ identity?) (f x) -- {!{!identity!!} ∘ f!}
-- -- -- -- -- -- -- -- -- -- -- -}

-- -- -- -- -- -- -- -- -- -- --     IdentitySubstitunctionExtensionTerm : Identity Substitunction (Extension Term) _ ¡
-- -- -- -- -- -- -- -- -- -- --     Identity′.identity IdentitySubstitunctionExtensionTerm = 𝓲dentitySubstitunctionExtensionTerm

-- -- -- -- -- -- -- -- -- -- --     IdentitySubstitunctionExtensionTerms : ∀ {N} → Identity Substitunction (Extension $ Terms N) _ ¡
-- -- -- -- -- -- -- -- -- -- --     Identity′.identity IdentitySubstitunctionExtensionTerms = 𝓲dentitySubstitunctionExtensionTerms

-- -- -- -- -- -- -- -- -- -- --     LeftIdentitySubstitunction : LeftIdentity Substitunction _
-- -- -- -- -- -- -- -- -- -- --     LeftIdentity.left-identity LeftIdentitySubstitunction f = identity ∘ f

-- -- -- -- -- -- -- -- -- -- --     RightIdentitySubstitunction : RightIdentity Substitunction _
-- -- -- -- -- -- -- -- -- -- --     RightIdentity.right-identity RightIdentitySubstitunction _ _ = ∅

-- -- -- -- -- -- -- -- -- -- --     IsCategorySubstitunction : IsCategory Substitunction _
-- -- -- -- -- -- -- -- -- -- --     IsCategorySubstitunction = record {}

-- -- -- -- -- -- -- -- -- -- --     IsFunctorSubstitunctionExtensionTerm : IsFunctor Substitunction _ (Extension Term) _ ¡
-- -- -- -- -- -- -- -- -- -- --     IsFunctorSubstitunctionExtensionTerm = record {}

-- -- -- -- -- -- -- -- -- -- --     IsFunctorSubstitunctionExtensionTerms : ∀ {N} → IsFunctor Substitunction _ (Extension $ Terms N) _ ¡
-- -- -- -- -- -- -- -- -- -- --     IsFunctorSubstitunctionExtensionTerms = record {}

-- -- -- -- -- -- -- -- -- -- -- module SubstitunctionØ {𝔭} (𝔓 : Ø 𝔭) where

-- -- -- -- -- -- -- -- -- -- --   open Substitunction 𝔓
-- -- -- -- -- -- -- -- -- -- --   open Term 𝔓

-- -- -- -- -- -- -- -- -- -- --   open Substitunction⌶ (Substitunction⌶ 𝔓 ∋ record {})

-- -- -- -- -- -- -- -- -- -- --   SemigroupoidSubstitunction : Semigroupoid _ _ _
-- -- -- -- -- -- -- -- -- -- --   Semigroupoid.Object SemigroupoidSubstitunction = _
-- -- -- -- -- -- -- -- -- -- --   Semigroupoid.Morphism SemigroupoidSubstitunction = Substitunction

-- -- -- -- -- -- -- -- -- -- --   SemifunctorSubstitunctionExtensionTerm : Semifunctor _ _ _ _ _ _
-- -- -- -- -- -- -- -- -- -- --   Semifunctor.Object₁ SemifunctorSubstitunctionExtensionTerm = _
-- -- -- -- -- -- -- -- -- -- --   Semifunctor.Morphism₁ SemifunctorSubstitunctionExtensionTerm = Substitunction
-- -- -- -- -- -- -- -- -- -- --   Semifunctor.Object₂ SemifunctorSubstitunctionExtensionTerm = _
-- -- -- -- -- -- -- -- -- -- --   Semifunctor.Morphism₂ SemifunctorSubstitunctionExtensionTerm = Extension Term
-- -- -- -- -- -- -- -- -- -- --   Semifunctor.μ SemifunctorSubstitunctionExtensionTerm = ¡

-- -- -- -- -- -- -- -- -- -- --   CategorySubstitunction : Category _ _ _
-- -- -- -- -- -- -- -- -- -- --   Category.Object CategorySubstitunction = _
-- -- -- -- -- -- -- -- -- -- --   Category.Morphism CategorySubstitunction = Substitunction

-- -- -- -- -- -- -- -- -- -- --   FunctorSubstitunctionExtensionTerm : Functor _ _ _ _ _ _
-- -- -- -- -- -- -- -- -- -- --   Functor.Object₁ FunctorSubstitunctionExtensionTerm = _
-- -- -- -- -- -- -- -- -- -- --   Functor.Morphism₁ FunctorSubstitunctionExtensionTerm = Substitunction
-- -- -- -- -- -- -- -- -- -- --   Functor.Object₂ FunctorSubstitunctionExtensionTerm = _
-- -- -- -- -- -- -- -- -- -- --   Functor.Morphism₂ FunctorSubstitunctionExtensionTerm = Extension Term
-- -- -- -- -- -- -- -- -- -- --   Functor.μ FunctorSubstitunctionExtensionTerm = ¡

-- -- -- -- -- -- -- -- -- -- --   module _ (N : ¶) where

-- -- -- -- -- -- -- -- -- -- --     FunctorSubstitunctionExtensionTerms : Functor _ _ _ _ _ _
-- -- -- -- -- -- -- -- -- -- --     Functor.Object₁ FunctorSubstitunctionExtensionTerms = _
-- -- -- -- -- -- -- -- -- -- --     Functor.Morphism₁ FunctorSubstitunctionExtensionTerms = Substitunction
-- -- -- -- -- -- -- -- -- -- --     Functor.Object₂ FunctorSubstitunctionExtensionTerms = _
-- -- -- -- -- -- -- -- -- -- --     Functor.Morphism₂ FunctorSubstitunctionExtensionTerms = Extension $ Terms N
-- -- -- -- -- -- -- -- -- -- --     Functor.μ FunctorSubstitunctionExtensionTerms = ¡

-- -- -- -- -- -- -- -- -- -- -- open SubstitunctionØ public

-- -- -- -- -- -- -- -- -- -- -- module AList⌶ {a} {A : Nat → Set a} where

-- -- -- -- -- -- -- -- -- -- --   private AList = Descender⟨ A ⟩

-- -- -- -- -- -- -- -- -- -- --   instance

-- -- -- -- -- -- -- -- -- -- --     Reflexivity⌶AList : Reflexivity AList
-- -- -- -- -- -- -- -- -- -- --     Reflexivity.reflexivity Reflexivity⌶AList = ∅

-- -- -- -- -- -- -- -- -- -- --     Transitivity⌶AList : Transitivity AList
-- -- -- -- -- -- -- -- -- -- --     Contiguity.contiguity Transitivity⌶AList f ∅ = f
-- -- -- -- -- -- -- -- -- -- --     Contiguity.contiguity Transitivity⌶AList f (x , g) = x , contiguity f g

-- -- -- -- -- -- -- -- -- -- --     MorphismEquivalence⌶AList : MorphismEquivalence AList _
-- -- -- -- -- -- -- -- -- -- --     MorphismEquivalence.morphismEquivalence MorphismEquivalence⌶AList = Proposequality

-- -- -- -- -- -- -- -- -- -- --     Associativity⌶AList : Associativity AList _
-- -- -- -- -- -- -- -- -- -- --     Associativity.associativity Associativity⌶AList _ _ ∅ = ∅
-- -- -- -- -- -- -- -- -- -- --     Associativity.associativity Associativity⌶AList f g (x , h) = congruity (x ,_) $ associativity f g h

-- -- -- -- -- -- -- -- -- -- --     IsSemigroupoid⌶AList : IsSemigroupoid AList _
-- -- -- -- -- -- -- -- -- -- --     IsSemigroupoid⌶AList = record {}

-- -- -- -- -- -- -- -- -- -- --     LeftIdentity⌶AList : LeftIdentity AList _
-- -- -- -- -- -- -- -- -- -- --     LeftIdentity.left-identity LeftIdentity⌶AList _ = ∅

-- -- -- -- -- -- -- -- -- -- --     RightIdentity⌶AList : RightIdentity AList _
-- -- -- -- -- -- -- -- -- -- --     RightIdentity.right-identity RightIdentity⌶AList ∅ = ∅
-- -- -- -- -- -- -- -- -- -- --     RightIdentity.right-identity RightIdentity⌶AList (x , f) = congruity (x ,_) $ right-identity f

-- -- -- -- -- -- -- -- -- -- --     IsCategory⌶AList : IsCategory AList _
-- -- -- -- -- -- -- -- -- -- --     IsCategory⌶AList = record {}

-- -- -- -- -- -- -- -- -- -- -- module Substitist⌶ {𝔭} {𝔓 : Ø 𝔭} where

-- -- -- -- -- -- -- -- -- -- --   open Substitunction 𝔓
-- -- -- -- -- -- -- -- -- -- --   open Term 𝔓
-- -- -- -- -- -- -- -- -- -- --   open Substitist 𝔓
-- -- -- -- -- -- -- -- -- -- --   open Substitunction⌶ (Substitunction⌶ 𝔓 ∋ record {})

-- -- -- -- -- -- -- -- -- -- --   postulate
-- -- -- -- -- -- -- -- -- -- --     _for_ : ∀ {n} (t' : Term n) (x : Fin (↑ n)) -> Fin (↑ n) -> Term n

-- -- -- -- -- -- -- -- -- -- --   instance

-- -- -- -- -- -- -- -- -- -- --     Map⌶Substitist,Substitunction : Map Substitist Substitunction
-- -- -- -- -- -- -- -- -- -- --     Map.map Map⌶Substitist,Substitunction ∅ = i
-- -- -- -- -- -- -- -- -- -- --     Map.map Map⌶Substitist,Substitunction ((x , t) , σ) = map σ ∙ (t for x)

-- -- -- -- -- -- -- -- -- -- -- module Fin⌶ where

-- -- -- -- -- -- -- -- -- -- --   instance

-- -- -- -- -- -- -- -- -- -- --     Map⌶Maybe : ∀ {x} → Map {A = Ø x} (λ x y → x → y) (λ x y → Maybe x → Maybe y)
-- -- -- -- -- -- -- -- -- -- --     Map.map Map⌶Maybe f ∅ = ∅
-- -- -- -- -- -- -- -- -- -- --     Map.map Map⌶Maybe f (↑ x) = ↑ (f x)

-- -- -- -- -- -- -- -- -- -- --   instance

-- -- -- -- -- -- -- -- -- -- --     Successor₀⌶¶ : Successor₀ ¶
-- -- -- -- -- -- -- -- -- -- --     Successor₀.⇑₀ Successor₀⌶¶ = ↑_

-- -- -- -- -- -- -- -- -- -- --     Principal₁Fin : Principal₁ Fin
-- -- -- -- -- -- -- -- -- -- --     Principal₁Fin = record {}

-- -- -- -- -- -- -- -- -- -- --     Successor₁⌶Fin : Successor₁ Fin
-- -- -- -- -- -- -- -- -- -- --     Successor₁.⇑₁ Successor₁⌶Fin = ↑_

-- -- -- -- -- -- -- -- -- -- --     Thin⌶Fin,Fin : Thin Fin Fin
-- -- -- -- -- -- -- -- -- -- --     Thin.thin Thin⌶Fin,Fin ∅ = ↑_
-- -- -- -- -- -- -- -- -- -- --     Thin.thin Thin⌶Fin,Fin (↑ x) ∅ = ∅
-- -- -- -- -- -- -- -- -- -- --     Thin.thin Thin⌶Fin,Fin (↑ x) (↑ y) = ↑ (thin x y)

-- -- -- -- -- -- -- -- -- -- --     Equivalence⌶Fin : ∀ {n} → Equivalence (Fin n) ∅̂
-- -- -- -- -- -- -- -- -- -- --     Equivalence.equivalence Equivalence⌶Fin = Proposequality

-- -- -- -- -- -- -- -- -- -- --     Equivalence⌶¶ : Equivalence ¶ ∅̂
-- -- -- -- -- -- -- -- -- -- --     Equivalence.equivalence Equivalence⌶¶ = Proposequality

-- -- -- -- -- -- -- -- -- -- --     pattern Fin↑ n = ¶⟨<_⟩.↑_ {n = n}

-- -- -- -- -- -- -- -- -- -- --     Injectivity₀⌶¶↑ : Injectivity₀ ¶.↑_ ∅̂ ∅̂
-- -- -- -- -- -- -- -- -- -- --     Injectivity₀⌶¶↑ = {!!}

-- -- -- -- -- -- -- -- -- -- --     Injectivity₀⌶Fin↑ : ∀ {n} → Injectivity₀ (Fin↑ n) ∅̂ ∅̂
-- -- -- -- -- -- -- -- -- -- --     Injectivity₀.injectivity₀ (Injectivity₀⌶Fin↑ {n}) = {!!}

-- -- -- -- -- -- -- -- -- -- --     Injectivity₁⌶Fin↑ : Injectivity₁ Fin↑ ∅̂ ∅̂
-- -- -- -- -- -- -- -- -- -- --     Injectivity₁.injectivity₁ Injectivity₁⌶Fin↑ = {!!}

-- -- -- -- -- -- -- -- -- -- --     Injectivity!⌶Fin↑ : Injectivity? Fin↑ ∅̂ ∅̂
-- -- -- -- -- -- -- -- -- -- --     Injectivity!.injectivity! Injectivity!⌶Fin↑ = {!!}

-- -- -- -- -- -- -- -- -- -- --     Injectivity₁⌶ThinFin : ∀ {m} → Injectivity₁ (thin {A = Fin} {B = Fin} {m = m}) ∅̂ ∅̂
-- -- -- -- -- -- -- -- -- -- --     Injectivity₁.injectivity₁ (Injectivity₁⌶ThinFin {m}) (∅ {n = .m}) {x} {y} x₁ = injectivity₁[ Fin↑ ] _ x₁
-- -- -- -- -- -- -- -- -- -- --     Injectivity₁.injectivity₁ (Injectivity₁⌶ThinFin {m}) (↑_ {n = .m} w) {x} {y} x₁ = {!!}

-- -- -- -- -- -- -- -- -- -- --     Injectivity!⌶ThinFin : ∀ {m} → Injectivity? (thin {A = Fin} {B = Fin} {m = m}) ∅̂ ∅̂
-- -- -- -- -- -- -- -- -- -- --     Injectivity!.injectivity! (Injectivity!⌶ThinFin {m}) (∅ {n = .m}) {x} {y} x₁ = injectivity?[ Fin↑ ] _ x₁
-- -- -- -- -- -- -- -- -- -- --     Injectivity!.injectivity! (Injectivity!⌶ThinFin {m}) (↑_ {n = .m} w) {x} {y} x₁ = {!!}

-- -- -- -- -- -- -- -- -- -- --     Injectivity₂⌶ThinFin : ∀ {m} → Injectivity₂ (thin {A = Fin} {B = Fin} {m = m}) ∅̂ ∅̂
-- -- -- -- -- -- -- -- -- -- --     Injectivity₂.injectivity₂ (Injectivity₂⌶ThinFin {m}) (∅ {n = .m}) {x} {y} x₁ = injectivity₀[ Fin↑ m ] x₁
-- -- -- -- -- -- -- -- -- -- --     Injectivity₂.injectivity₂ (Injectivity₂⌶ThinFin {m}) (↑_ {n = .m} w) {x} {y} x₁ = {!!}

-- -- -- -- -- -- -- -- -- -- --   test-thin-injective : ∀ {m} (x : Fin (↑ m)) {y₁ y₂ : Fin m} → thin x y₁ ≋ thin x y₂ → y₁ ≋ y₂
-- -- -- -- -- -- -- -- -- -- --   test-thin-injective x eq = injectivity₂[ thin[ Fin ] ] x eq

-- -- -- -- -- -- -- -- -- -- --   -- injectivity₂[ thin[ Fin ] ] x eq
-- -- -- -- -- -- -- -- -- -- --   -- injectivity₁[ thin[ Fin ] ] x eq

-- -- -- -- -- -- -- -- -- -- --     -- ∀ {n} → Injectivity₁ (thin {A = Fin} {B = Fin} {m = n}) ∅̂ ∅̂
-- -- -- -- -- -- -- -- -- -- --     -- Injectivity₁⌶ThinFin = ?


-- -- -- -- -- -- -- -- -- -- -- --     Injectivity₁.injectivity₁ (Injectivity₁⌶ThinFin {n}) (∅ {n = .n}) {x} {y} eq = injectivity![ (λ n → ¶⟨<_⟩.↑_ {n = n}) ] _ _ _ eq
-- -- -- -- -- -- -- -- -- -- -- --       -- injectivity₁⋆[ (λ {n} → ¶⟨<_⟩.↑_ {n}) ] eq -- injectivity₀[ ¶⟨<_⟩.↑_ {n = n} ] eq
-- -- -- -- -- -- -- -- -- -- -- --     Injectivity₁.injectivity₁ (Injectivity₁⌶ThinFin {n}) (↑_ {n = .n} w) {x} {y} eq = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- --     InjThinFin : ∀ {m} {x : Fin (↑ m)} → INJ (thin[ Fin ] x) ∅̂ ∅̂
-- -- -- -- -- -- -- -- -- -- -- -- -- --     INJ.inj (InjThinFin {m} {∅ {n = .m}}) {x} {y} = INj (¶⟨<_⟩.↑_ {m}) ⦃ it ⦄ ⦃ it ⦄ ⦃ {!InjThinFin {m = m} {x = ∅}!} ⦄ {x} {y}
-- -- -- -- -- -- -- -- -- -- -- -- -- --     INJ.inj (InjThinFin {m} {↑_ {n = .m} x}) {x₁} {y} = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- --   test-thin-injective : ∀ {m} {x : Fin (↑ m)} {y₁ y₂ : Fin m} → thin x y₁ ≋ thin x y₂ → y₁ ≋ y₂
-- -- -- -- -- -- -- -- -- -- -- -- -- --   test-thin-injective {m = m} {x = x} eq = INj2 (thin {A = Fin} {B = Fin}) {w = x} eq -- INj2 (thin[ Fin ]) {w = x} eq -- INj2 (thin {A = Fin} {B = Fin}) eq

-- -- -- -- -- -- -- -- -- -- -- -- -- --   test-thin-injective2 : ∀ {m} {x : Fin (↑ m)} {y₁ y₂ : Fin m} → thin x y₁ ≋ thin x y₂ → y₁ ≋ y₂
-- -- -- -- -- -- -- -- -- -- -- -- -- --   test-thin-injective2 {x = x} = test-thin-injective {x = x}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   instance

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Injectivity⌶↑¶ : Injectivity ¶.↑_ ∅̂ ∅̂
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Injectivity.injectivity Injectivity⌶↑¶ ∅ = ∅

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Injectivity⌶↑Fin : ∀ {n} → Injectivity {A = ¶⟨< n ⟩} {B = ¶⟨< ↑ n ⟩} ¶⟨<_⟩.↑_ ∅̂ ∅̂
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Injectivity.injectivity (Injectivity⌶↑Fin {n}) {x} {.x} ∅ = ∅

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   Injectivity⌶ThinFin : ∀ {m} {x : Fin (⇑₀ m)} → Injectivity (thin[ Fin ] x) ∅̂ ∅̂
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   Injectivity.injectivity (Injectivity⌶ThinFin {m = m} {x = ∅}) e = injectivity {B = Fin (↑ m)} {f = ↑_ {n = m}} e -- injectivity {B = Fin m} {f = ↑_ {n = _}} e -- injectivity {f = ¶⟨<_⟩.↑_ {n = _}} ⦃ r = {!!} ⦄ {!e!} -- injectivity {f = ¶⟨<_⟩.↑_} e
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --       -- injectivity[ ¶⟨<_⟩.↑_ ] ⦃ e1 = ! ⦄ ⦃ e2 = Equivalence⌶Fin ⦄ ⦃ i1 = Injectivity⌶↑Fin ⦄ e
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --       -- injectivity[ ¶.↑_ ] e
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   Injectivity.injectivity (Injectivity⌶ThinFin {.(↑ _)} {↑_ {n = .(↑ n)} x}) {∅ {n = n}} {y} x₂ = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   Injectivity.injectivity (Injectivity⌶ThinFin {.(↑ _)} {↑_ {n = .(↑ n)} x}) {↑_ {n = n} x₁} {y} x₂ = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   instance

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ThinInjective⌶Fin,Fin : ThinInjective Fin Fin ∅̂
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ThinInjective.iInjectivity ThinInjective⌶Fin,Fin {m} {x} = Injectivity⌶ThinFin {m} {x} -- Injectivity⌶ThinFin

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   test-thin-injective : ∀ {m} {x : Fin (↑ m)} {y₁ y₂ : Fin m} → thin x y₁ ≋ thin x y₂ → y₁ ≋ y₂
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   test-thin-injective {x = x} = thin-injective {B = Fin} { x = x }

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   instance I1 = Injectivity⌶ThinFin

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   test-thin-injective' : ∀ {m} {x : Fin (↑ m)} {y₁ y₂ : Fin m} → thin x y₁ ≋ thin x y₂ → y₁ ≋ y₂
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   test-thin-injective' {m} {x = x} eq = injectivity {A = Fin m} {B = Fin (↑ m)} {f = thin {A = Fin} {B = λ v → Fin v} x} ⦃ r = I1 {m} {{!!}} ⦄ eq --

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   instance

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     InjectivityP⌶Fin : ∀ {m} {x : Fin m} → InjectivityP (¶⟨<_⟩.↑_ {n = m})
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     InjectivityP.injectivityP (InjectivityP⌶Fin {m} {x}) = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     InjectivityP⌶ThinFin : ∀ {m} {x : Fin (⇑₀ m)} → InjectivityP (thin[ Fin ] x)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     InjectivityP.injectivityP (InjectivityP⌶ThinFin {m} {∅ {n = .m}}) {x} {y} x₂ = injectivityP x₂
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     InjectivityP.injectivityP (InjectivityP⌶ThinFin {m} {↑_ {n = .m} x}) {x₁} {y} x₂ = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   test-fin-injective : ∀ {m} {y₁ y₂ : Fin m} → ¶⟨<_⟩.↑ y₁ ≋ ↑ y₂ → y₁ ≋ y₂
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   test-fin-injective {m} = injectivity {f = λ v → ¶⟨<_⟩.↑_ {m} v}


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- {-
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ThinInjective⌶Fin,Fin : ThinInjective Fin Fin ∅̂
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ThinInjective.thin-injective ThinInjective⌶Fin,Fin {x = ∅} e = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ThinInjective.thin-injective ThinInjective⌶Fin,Fin {x = ↑ x} {∅} {∅} _ = ∅
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ThinInjective.thin-injective ThinInjective⌶Fin,Fin {x = ↑ x} {∅} {↑ _} ()
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ThinInjective.thin-injective ThinInjective⌶Fin,Fin {x = ↑ x} {↑ _} {∅} ()
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ThinInjective.thin-injective ThinInjective⌶Fin,Fin {x = ↑ x} {↑ y₁} {↑ y₂} = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Thick⌶Fin,Fin : Thick Fin Fin
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Thick.thick Thick⌶Fin,Fin = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ThickThinId⌶Fin,Fin : ThickThinId Fin Fin ∅̂
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ThickThinId.thick∘thin=id ThickThinId⌶Fin,Fin = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Maybe*⌶ : ∀ {a} → Maybe* a
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Maybe*.Maybe Maybe*⌶ = Maybe
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Maybe*.just Maybe*⌶ = ↑_

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Check⌶Fin,Fin : Check Fin Fin
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Check.check Check⌶Fin,Fin ∅ ∅ = ∅
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Check.check Check⌶Fin,Fin ∅ (↑ y) = ↑ y
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Check.check Check⌶Fin,Fin {∅} (↑ ()) _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Check.check Check⌶Fin,Fin {↑ _} (↑ x) ∅ = ↑ ∅
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Check.check Check⌶Fin,Fin {↑ _} (↑ x) (↑ y) = map ¶⟨<_⟩.↑_ $ check x y

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- {-
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Equivalence⌶Maybe : ∀ {a} {A : Ø a} {ℓ} ⦃ _ : Equivalence A ℓ ⦄ → Equivalence (Maybe A) ℓ
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Equivalence.equivalence Equivalence⌶Maybe ∅ ∅ = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Equivalence.equivalence Equivalence⌶Maybe ∅ (↑ x₁) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Equivalence.equivalence Equivalence⌶Maybe (↑ x₁) ∅ = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Equivalence.equivalence Equivalence⌶Maybe (↑ x₁) (↑ x₂) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Equivalence.⌶IsSetoid Equivalence⌶Maybe = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Equivalence⌶MaybeFin : ∀ {n} → Equivalence (Maybe (Fin n)) ∅̂
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Equivalence.equivalence Equivalence⌶MaybeFin = Proposequality

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ThinCheckId⌶Fin,Fin : ThinCheckId Fin Fin ∅̂ ∅̂
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ThinCheckId.thin-check-id ThinCheckId⌶Fin,Fin x y y' x₁ = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ThickAndThin⌶FinFin : ThickAndThin Fin Fin ∅̂ ∅̂
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ThickAndThin⌶FinFin = record {}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   module _ {𝔭} {𝔓 : Ø 𝔭} where

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     open Term 𝔓

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     instance

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       Principal₁⌶Term : Principal₁ Term
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       Principal₁⌶Term = record {}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     private

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       mutual

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         𝓶ap⌶ExtensionFin,ExtensionTerm : 𝓶ap (Extension Fin) (Extension Term)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         𝓶ap⌶ExtensionFin,ExtensionTerm f (i x) = i (f x)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         𝓶ap⌶ExtensionFin,ExtensionTerm f leaf = leaf
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         𝓶ap⌶ExtensionFin,ExtensionTerm f (t1 fork t2) = (𝓶ap⌶ExtensionFin,ExtensionTerm f t1) fork 𝓶ap⌶ExtensionFin,ExtensionTerm f t2
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         𝓶ap⌶ExtensionFin,ExtensionTerm f (function F ts) = function F (𝓶ap⌶ExtensionFin,ExtensionTerms f ts)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         𝓶ap⌶ExtensionFin,ExtensionTerms : ∀ {N} → 𝓶ap (Extension Fin) (Extension (Terms N))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         𝓶ap⌶ExtensionFin,ExtensionTerms f ∅ = ∅
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         𝓶ap⌶ExtensionFin,ExtensionTerms f (t , ts) = 𝓶ap⌶ExtensionFin,ExtensionTerm f t , 𝓶ap⌶ExtensionFin,ExtensionTerms f ts

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     instance

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       Map⌶ExtensionFin,ExtensionTerm : Map (Extension Fin) (Extension Term)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       Map.map Map⌶ExtensionFin,ExtensionTerm = 𝓶ap⌶ExtensionFin,ExtensionTerm

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       Map⌶ExtensionFin,ExtensionTerms : ∀ {N} → Map (Extension Fin) (Extension (Terms N))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       Map.map Map⌶ExtensionFin,ExtensionTerms = 𝓶ap⌶ExtensionFin,ExtensionTerms

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       Thin⌶Fin,Term : Thin Fin Term
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       Thin.thin Thin⌶Fin,Term = map ∘ thin

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       Equivalence⌶Term : ∀ {n} → Equivalence (Term n) ∅̂
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       Equivalence.equivalence Equivalence⌶Term = Proposequality

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       Injectivity⌶ASD : Injectivity

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       ThinInjective⌶Fin,Term : ThinInjective Fin Term ∅̂
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       ThinInjective.thin-injective ThinInjective⌶Fin,Term = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Successor₀⌶¶ : Upper Fin
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Upper.up Upper⌶Fin = ↑_

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ThickAndThin⌶Fin : ThickAndThin Fin Fin
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ThickAndThin.thin ThickAndThin⌶Fin ∅ y = ↑ y
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ThickAndThin.thin ThickAndThin⌶Fin (↑ x) ∅ = ∅
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ThickAndThin.thin ThickAndThin⌶Fin (↑ x) (↑ y) = ↑ thin x y
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ThickAndThin.thin-injective ThickAndThin⌶Fin x x₁ = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ThickAndThin.thick ThickAndThin⌶Fin = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ThickAndThin.thick∘thin=id ThickAndThin⌶Fin = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ThickAndThin.check ThickAndThin⌶Fin = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ThickAndThin.thin-check-id ThickAndThin⌶Fin = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- module Term⌶ {𝔭} {𝔓 : Ø 𝔭} where

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   open Term 𝔓

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   instance

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ThickAndThin⌶Term : ThickAndThin Term
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ThickAndThin.thin ThickAndThin⌶Term x (i x₁) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ThickAndThin.thin ThickAndThin⌶Term x leaf = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ThickAndThin.thin ThickAndThin⌶Term x (x₁ fork x₂) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ThickAndThin.thin ThickAndThin⌶Term x (function x₁ x₂) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ThickAndThin.thin-injective ThickAndThin⌶Term = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ThickAndThin.thick ThickAndThin⌶Term = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ThickAndThin.thick∘thin=id ThickAndThin⌶Term = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ThickAndThin.check ThickAndThin⌶Term = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ThickAndThin.thin-check-id ThickAndThin⌶Term = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- {-
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Data
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   Nat
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   ≤↓List -- m ≤ n, n-1...m
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   Substitunction
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   Substitist
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Record
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   Product
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   Functor
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Class
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   Reflexivity
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   IsFunctor
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   ThickAndThin

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -}
