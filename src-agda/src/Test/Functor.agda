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

suc = ¶.↑_

module _
  {a b} {A : Set a} {B : Set b}
  where

  map-list : (A → B) → List A → List B
  map-list f ∅ = ∅
  map-list f (x , xs) = f x , map-list f xs

module _
  {a b}
  where
  hmap-list :
    Hmap.class {𝔛₁ = Ø a} {𝔛₁' = Ø a}
               {𝔛₂ = Ø b} {𝔛₂' = Ø b}
               ¡
               ¡
               (λ x y → x → y)
               (λ x y → List x → List y)
  hmap-list .⋆ _ _ = map-list

module _
  {ℓ ℓ′} (F : Ø ℓ → Ø ℓ′)
  where
  smap!-list :
    Smap.class (λ (x y : Ø ℓ) → x → y)
               (λ (x y : {!!}) → F x → F y)
               {!!} {!!}
  smap!-list .⋆ _ _ = {!!}

module _
  {ℓ ℓ′} (F : Ø ℓ → Ø ℓ′)
  where

  isFunctorF : IsFunctor (λ (x y : Ø ℓ) → x → y)
                         Proposextensequality
                         (λ (x y : Ø ℓ′) → x → y)
                         Proposextensequality
  isFunctorF .IsFunctor.`IsPrefunctor .IsPrefunctor.`IsPrecategory₁ .IsPrecategory.`𝓣ransitivity {_} {_} {_} {f} {g} .⋆ = g ∘ f
  isFunctorF .IsFunctor.`IsPrefunctor .IsPrefunctor.`IsPrecategory₁ .IsPrecategory.`[𝓣ransassociativity] = {!!}
  isFunctorF .IsFunctor.`IsPrefunctor .IsPrefunctor.`IsPrecategory₁ .IsPrecategory.`𝓣ransextensionality .⋆ = {!!}
  isFunctorF .IsFunctor.`IsPrefunctor .IsPrefunctor.`IsPrecategory₁ .IsPrecategory.`𝓣ransassociativity = {!!}
  isFunctorF .IsFunctor.`IsPrefunctor .IsPrefunctor.`IsPrecategory₂ = {!!}
  isFunctorF .IsFunctor.`IsPrefunctor .IsPrefunctor.`𝓢urjection .⋆ = F
  isFunctorF .IsFunctor.`IsPrefunctor .IsPrefunctor.`𝓢urjectivity .⋆ _ _ = {!!}
  isFunctorF .IsFunctor.`IsPrefunctor .IsPrefunctor.`𝓢urjtranscommutativity = {!!}
  isFunctorF .IsFunctor.`IsPrefunctor .IsPrefunctor.`𝓢urjextensionality .⋆ = {!!}
  isFunctorF .IsFunctor.`IsCategory₁ .IsCategory.`IsPrecategory = {!!}
  isFunctorF .IsFunctor.`IsCategory₁ .IsCategory.`[𝓣ransleftidentity] = {!!}
  isFunctorF .IsFunctor.`IsCategory₁ .IsCategory.`[𝓣ransrightidentity] = {!!}
  isFunctorF .IsFunctor.`IsCategory₁ .IsCategory.`𝓡eflexivity = {!!}
  isFunctorF .IsFunctor.`IsCategory₁ .IsCategory.`𝓣ransleftidentity = {!!}
  isFunctorF .IsFunctor.`IsCategory₁ .IsCategory.`𝓣ransrightidentity = {!!}
  isFunctorF .IsFunctor.`IsCategory₂ = {!!}
  isFunctorF .IsFunctor.`𝒮urjidentity = {!!}

module _
  where

  isFunctorList : ∀ {ℓ} → IsFunctor (λ (x y : Ø ℓ) → x → y)
                                    Proposextensequality
                                    (λ (x y : Ø ℓ) → List x → List y)
                                    Proposextensequality
  isFunctorList .IsFunctor.`IsPrefunctor .IsPrefunctor.`IsPrecategory₁ = {!!}
  isFunctorList .IsFunctor.`IsPrefunctor .IsPrefunctor.`IsPrecategory₂ = {!!}
  isFunctorList .IsFunctor.`IsPrefunctor .IsPrefunctor.`𝓢urjection = !
  isFunctorList .IsFunctor.`IsPrefunctor .IsPrefunctor.`𝓢urjectivity .⋆ _ _ = map-list
  isFunctorList .IsFunctor.`IsPrefunctor .IsPrefunctor.`𝓢urjtranscommutativity = {!!}
  isFunctorList .IsFunctor.`IsPrefunctor .IsPrefunctor.`𝓢urjextensionality = {!!}
  isFunctorList .IsFunctor.`IsCategory₁ = {!!}
  isFunctorList .IsFunctor.`IsCategory₂ = {!!}
  isFunctorList .IsFunctor.`𝒮urjidentity = {!!}
