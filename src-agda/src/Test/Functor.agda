{-# OPTIONS --allow-unsolved-metas #-}

open import Everything

module Test.Functor where

List = List⟨_⟩

module _
  {a b} {A : Set a} {B : Set b}
  where

  map-list : (A → B) → List A → List B
  map-list f ∅ = ∅
  map-list f (x , xs) = f x , map-list f xs

instance

  SurjtranscommutativityList : ∀ {ℓ} → Surjtranscommutativity.class Function⟦ ℓ ⟧ (MFunction List) _≡̇_ map-list transitivity transitivity
  SurjtranscommutativityList .⋆ f g ∅ = ∅
  SurjtranscommutativityList .⋆ f g (x , xs) rewrite SurjtranscommutativityList .⋆ f g xs = ∅

  SurjextensionalityList : ∀ {ℓ} → Surjextensionality.class Function⟦ ℓ ⟧ _≡̇_ (MFunction List) _≡̇_ _ map-list
  SurjextensionalityList .⋆ _ _ f₁ f₂ f₁≡̇f₂ ∅ = ∅
  SurjextensionalityList .⋆ _ _ f₁ f₂ f₁≡̇f₂ (x , xs) rewrite SurjextensionalityList .⋆ _ _ f₁ f₂ f₁≡̇f₂ xs | f₁≡̇f₂ x = ∅

  SurjidentityList : ∀ {ℓ} → Surjidentity.class Function⟦ ℓ ⟧ (MFunction List) _≡̇_ map-list ε ε
  SurjidentityList .⋆ ∅ = ∅
  SurjidentityList .⋆ (x , xs) rewrite SurjidentityList .⋆ xs = ∅

test-isprecategory-1 : ∀ {ℓ} → IsPrecategory Function⟦ ℓ ⟧ _≡̇_ (flip _∘′_)
test-isprecategory-1 = IsPrecategoryExtension

test-isprecategory-2 : ∀ {ℓ} → IsPrecategory Function⟦ ℓ ⟧ _≡̇_ (flip _∘′_)
test-isprecategory-2 = IsPrecategoryFunction

-- FIXME confused between Function and Extension

instance

  isFunctorList : ∀ {ℓ} → IsFunctor (λ (x y : Ø ℓ) → x → y)
                                    Proposextensequality
                                    ε
                                    (flip _∘′_)
                                    (λ (x y : Ø ℓ) → List x → List y)
                                    Proposextensequality
                                    ε
                                    (flip _∘′_)
                                    map-list
  isFunctorList .IsFunctor.`IsPrefunctor .IsPrefunctor.`IsPrecategory₁ = {!!}
  isFunctorList .IsFunctor.`IsPrefunctor .IsPrefunctor.`IsPrecategory₂ = !
  isFunctorList .IsFunctor.`IsPrefunctor .IsPrefunctor.`𝓢urjtranscommutativity = !
  isFunctorList .IsFunctor.`IsPrefunctor .IsPrefunctor.`𝓢urjextensionality = !
  isFunctorList .IsFunctor.`IsCategory₁ .IsCategory.`IsPrecategory = {!!}
  isFunctorList .IsFunctor.`IsCategory₁ .IsCategory.`𝓣ransleftidentity = !
  isFunctorList .IsFunctor.`IsCategory₁ .IsCategory.`𝓣ransrightidentity = !
  isFunctorList .IsFunctor.`IsCategory₂ .IsCategory.`IsPrecategory = !
  isFunctorList .IsFunctor.`IsCategory₂ .IsCategory.`𝓣ransleftidentity = !
  isFunctorList .IsFunctor.`IsCategory₂ .IsCategory.`𝓣ransrightidentity = !
  isFunctorList .IsFunctor.`𝒮urjidentity = !

instance

  FmapList : ∀ {ℓ} → Fmap (List {ℓ})
  FmapList = ∁ map-list

  HmapList : ∀ {a} → Hmap.class Function⟦ a ⟧ (MFunction List)
  HmapList = ∁ (λ x y → map-list {A = x} {B = y})

module _
  {a} {A : Set a} {B : Set a}
  where
  test-smap-list : (A → B) → List A → List B
  test-smap-list = smap

module _
  {a} {A : Set a} {B : Set a}
  where
  test-fmap-list : (A → B) → List A → List B
  test-fmap-list = fmap -- the intention here is to try to say "I want to invoke a functoral mapping, so that I can be sure that, for example, that `test-map-list ε₁ ≡ ε₂`.
