{-# OPTIONS --allow-unsolved-metas #-}

module Test.Functor where

import Oscar.Class.Surjection.⋆
open import Oscar.Class
open import Oscar.Class.Functor
open import Oscar.Class.Hmap
open import Oscar.Class.IsCategory
open import Oscar.Class.IsFunctor
open import Oscar.Class.IsPrecategory
open import Oscar.Class.IsPrefunctor
open import Oscar.Class.Reflexivity
open import Oscar.Class.Smap
open import Oscar.Class.Surjection
open import Oscar.Class.Transitivity
open import Oscar.Class.Transleftidentity
open import Oscar.Class.Transrightidentity
open import Oscar.Data.List
open import Oscar.Data.Proposequality
open import Oscar.Data.¶
open import Oscar.Data.𝟙
open import Oscar.Prelude

List = List⟨_⟩

module _
  {a b} {A : Set a} {B : Set b}
  where

  map-list : (A → B) → List A → List B
  map-list f ∅ = ∅
  map-list f (x , xs) = f x , map-list f xs

module Fmap
  {a b}
  (F : Ø a → Ø b)
  = Hmap ¡ ¡ (λ x y → x → y) (λ x y → F x → F y)

instance
  HmapList : ∀ {ℓ} → Fmap.class (List {ℓ})
  HmapList .⋆ _ _ = map-list

instance

  isFunctorList : ∀ {ℓ} → IsFunctor (λ (x y : Ø ℓ) → x → y)
                                    Proposextensequality
                                    (flip _∘′_)
                                    (λ (x y : Ø ℓ) → List x → List y)
                                    Proposextensequality
                                    (flip _∘′_)
                                    smap
  isFunctorList .IsFunctor.`IsPrefunctor .IsPrefunctor.`IsPrecategory₁ = {!!}
  isFunctorList .IsFunctor.`IsPrefunctor .IsPrefunctor.`IsPrecategory₂ = {!!}
  isFunctorList .IsFunctor.`IsPrefunctor .IsPrefunctor.`𝓢urjtranscommutativity = {!!}
  isFunctorList .IsFunctor.`IsPrefunctor .IsPrefunctor.`𝓢urjextensionality = {!!}
  isFunctorList .IsFunctor.`IsCategory₁ .IsCategory.`IsPrecategory = {!!}
  isFunctorList .IsFunctor.`IsCategory₁ .IsCategory.`𝓡eflexivity .⋆ = {!!}
  isFunctorList .IsFunctor.`IsCategory₁ .IsCategory.`𝓣ransleftidentity = {!!}
  isFunctorList .IsFunctor.`IsCategory₁ .IsCategory.`𝓣ransrightidentity = {!!}
  isFunctorList .IsFunctor.`IsCategory₂ .IsCategory.`IsPrecategory = {!!}
  isFunctorList .IsFunctor.`IsCategory₂ .IsCategory.`𝓡eflexivity .⋆ = {!!}
  isFunctorList .IsFunctor.`IsCategory₂ .IsCategory.`𝓣ransleftidentity = {!!}
  isFunctorList .IsFunctor.`IsCategory₂ .IsCategory.`𝓣ransrightidentity = {!!}
  isFunctorList .IsFunctor.`𝒮urjidentity .⋆ = {!!}

module _
  {a b}
  {F : Ø a → Ø b}
  where
  fmap : {smap : {x y : Set a} → (x → y) → F x → F y}
         ⦃ I : IsFunctor (λ (x y : Ø a) → x → y)
                               Proposextensequality
                               (flip _∘′_)
                               (λ x y → F x → F y)
                               Proposextensequality
                               (flip _∘′_)
                               smap ⦄
             → Smap.type (λ x y → x → y) (λ x y → F x → F y) ¡ ¡
  fmap {smap} = smap

module _
  {a} {A : Set a} {B : Set a}
  where
  test-map-list : (A → B) → List A → List B
  test-map-list = fmap -- FIXME yellow; the intention here is to try to say "I want to invoke a functoral mapping, so that I can be sure that, for example, that `test-map-list ε₁ ≡ ε₂`. A trouble with this intention (which perhaps explains the yellow) is that ε₁ and ε₂ are not uniquely determined here.
