
open import Oscar.Prelude
open import Oscar.Class.IsPrecategory
open import Oscar.Class.IsCategory
open import Oscar.Class.Category
open import Oscar.Class.IsFunctor
open import Oscar.Class.Functor

open import Oscar.Class.Reflexivity
open import Oscar.Class.Transitivity
open import Oscar.Class.Surjection
open import Oscar.Class.Smap
open import Oscar.Class.Transextensionality
open import Oscar.Class.Transassociativity
open import Oscar.Class.Transleftidentity
open import Oscar.Class.Transrightidentity
open import Oscar.Class.Surjidentity
open import Oscar.Class

module Oscar.Class.Kitten where

productCat : ∀ {𝔬₁ 𝔯₁ ℓ₁ 𝔬₂ 𝔯₂ ℓ₂} → Category 𝔬₁ 𝔯₁ ℓ₁ → Category 𝔬₂ 𝔯₂ ℓ₂ → Category (𝔬₁ ∙̂ 𝔬₂) (𝔯₁ ∙̂ 𝔯₂) (ℓ₁ ∙̂ ℓ₂)
Category.𝔒 (productCat c₁ c₂) = Category.𝔒 c₁ × Category.𝔒 c₂
Category._∼_ (productCat c₁ c₂) (x₁ , x₂) (y₁ , y₂) = Category._∼_ c₁ x₁ y₁ × Category._∼_ c₂ x₂ y₂
Category._∼̇_ (productCat c₁ c₂) {x₁ , x₂} {y₁ , y₂} (f₁ , g₁) (f₂ , g₂) = Category._∼̇_ c₁ f₁ f₂ × Category._∼̇_ c₂ g₁ g₂
Category.category-ε (productCat c₁ c₂) = (Category.category-ε c₁) , (Category.category-ε c₂)
Category._↦_ (productCat c₁ c₂) (f₁ , f₂) (g₁ , g₂) = (Category._↦_ c₁ f₁ g₁) , (Category._↦_ c₂ f₂ g₂)
Category.`IsCategory (productCat c₁ c₂) .IsCategory.`IsPrecategory .IsPrecategory.`𝓣ransextensionality .⋆ (x₁ , y₁) (x₂ , y₂) = transextensionality x₁ x₂ , transextensionality y₁ y₂
Category.`IsCategory (productCat c₁ c₂) .IsCategory.`IsPrecategory .IsPrecategory.`𝓣ransassociativity .⋆ f g h = transassociativity (f .π₀) (g .π₀) (h .π₀) , transassociativity (f .π₁) (g .π₁) (h .π₁)
Category.`IsCategory (productCat c₁ c₂) .IsCategory.`𝓣ransleftidentity .⋆ = transleftidentity , transleftidentity
Category.`IsCategory (productCat c₁ c₂) .IsCategory.`𝓣ransrightidentity = ∁ (transrightidentity , transrightidentity)

record AFunctor {𝔬₁ 𝔯₁ ℓ₁ 𝔬₂ 𝔯₂ ℓ₂} (source : Category 𝔬₁ 𝔯₁ ℓ₁) (target : Category 𝔬₂ 𝔯₂ ℓ₂) : Ø 𝔬₁ ∙̂ 𝔯₁ ∙̂ ℓ₁ ∙̂ 𝔬₂ ∙̂ 𝔯₂ ∙̂ ℓ₂ where
  constructor ∁
  private module S = Category source
  private module T = Category target
  field
    F₀ : S.𝔒 → T.𝔒
    F₁ : Smap.type S._∼_ T._∼_ F₀ F₀
    isFunctor : IsFunctor S._∼_ S._∼̇_ S.category-ε S._↦_ T._∼_ T._∼̇_ T.category-ε T._↦_ F₁

record MonoidalCategory 𝔬 𝔯 ℓ : Ø ↑̂ (𝔬 ∙̂ 𝔯 ∙̂ ℓ) where
  constructor ∁
  field
    thecat : Category 𝔬 𝔯 ℓ
    thefunc : AFunctor (productCat thecat thecat) thecat
  O : Ø 𝔬
  O = Category.𝔒 thecat
  field
    𝟏 : O
  _⟶_ : O → O → Ø 𝔯
  _⟶_ = Category._∼_ thecat
  _⊗_ : O → O → O
  _⊗_ = λ x y → AFunctor.F₀ thefunc (x , y)
  _⨂_ : ∀ {w x y z} → w ⟶ x → y ⟶ z → (w ⊗ y) ⟶ (x ⊗ z)
  _⨂_ f g = AFunctor.F₁ thefunc (f , g)
  _↦_ : ∀ {x y z} (f : x ⟶ y) (g : y ⟶ z) → x ⟶ z
  _↦_ = Category._↦_ thecat
  i : ∀ {x} → x ⟶ x
  i = Category.category-ε thecat
  _≈̇_ = Category._∼̇_ thecat
  -- infixr 9 _⊗_
  field
    associator : ∀ (x y z : O)
                 → Σ (((x ⊗ y) ⊗ z) ⟶ (x ⊗ (y ⊗ z))) λ f
                 → Σ ((x ⊗ (y ⊗ z)) ⟶ ((x ⊗ y) ⊗ z)) λ f⁻¹
                 → ((f ↦ f⁻¹) ≈̇ i) × ((f⁻¹ ↦ f) ≈̇ i)
    left-unitor : ∀ (x : O)
                  → Σ ((𝟏 ⊗ x) ⟶ x) λ f
                  → Σ (x ⟶ (𝟏 ⊗ x)) λ f⁻¹
                  → ((f ↦ f⁻¹) ≈̇ i) × ((f⁻¹ ↦ f) ≈̇ i)
    right-unitor : ∀ (x : O)
                   → Σ ((x ⊗ 𝟏) ⟶ x) λ f
                   → Σ (x ⟶ (x ⊗ 𝟏)) λ f⁻¹
                   → ((f ↦ f⁻¹) ≈̇ i) × ((f⁻¹ ↦ f) ≈̇ i)
  assoc : ∀ (x y z : O) → ((x ⊗ y) ⊗ z) ⟶ (x ⊗ (y ⊗ z))
  assoc x y z = π₀ (associator x y z)
  ru : ∀ x → (x ⊗ 𝟏) ⟶ x
  ru x = π₀ (right-unitor x)
  lu : ∀ x → (𝟏 ⊗ x) ⟶ x
  lu x = π₀ (left-unitor x)
  field
    triangle-identity : ∀ (x y : O)
                        → (ru x ⨂ i) ≈̇ (assoc x 𝟏 y ↦ (i ⨂ lu y))
    pentagon-identity : ∀ (w x y z : O)
      → (((assoc w x y ⨂ i) ↦ assoc w (x ⊗ y) z) ↦ (i ⨂ assoc x y z))
      ≈̇ (assoc (w ⊗ x) y z ↦ assoc w x (y ⊗ z))

module _
  {𝔬₁ 𝔯₁ ℓ₁ 𝔬₂ 𝔯₂ ℓ₂}
  (source : MonoidalCategory 𝔬₁ 𝔯₁ ℓ₁)
  (target : MonoidalCategory 𝔬₂ 𝔯₂ ℓ₂)
  where
  record LaxMonoidalFunctor : Ø 𝔬₁ ∙̂ 𝔯₁ ∙̂ ℓ₁ ∙̂ 𝔬₂ ∙̂ 𝔯₂ ∙̂ ℓ₂ where
    module C = MonoidalCategory source
    module D = MonoidalCategory target
    field
      𝓕 : AFunctor C.thecat D.thecat
    open AFunctor 𝓕 public
    field
      e : D.𝟏 D.⟶ F₀ C.𝟏
      μ : ∀ x y → (F₀ x D.⊗ F₀ y) D.⟶ F₀ (x C.⊗ y) -- F A → F B → F (A × B)
      associativity : ∀ x y z
        → ((μ x y D.⨂ D.i) D.↦ (μ (x C.⊗ y) z D.↦ F₁ (C.assoc x y z)))
              D.≈̇
          (D.assoc (F₀ x) (F₀ y) (F₀ z) D.↦ ((D.i D.⨂ μ y z) D.↦ μ x (y C.⊗ z)))
      left-unitality : ∀ x → (D.lu (F₀ x)) D.≈̇ ((e D.⨂ D.i) D.↦ (μ C.𝟏 x D.↦ F₁ (C.lu x)))
      right-unitality : ∀ x → (D.ru (F₀ x)) D.≈̇ ((D.i D.⨂ e) D.↦ (μ x C.𝟏 D.↦ F₁ (C.ru x)))

module _
  {𝔬₁ 𝔯₁ ℓ₁ 𝔬₂ 𝔯₂ ℓ₂}
  (source : MonoidalCategory 𝔬₁ 𝔯₁ ℓ₁)
  (target : MonoidalCategory 𝔬₂ 𝔯₂ ℓ₂)
  (let module C = MonoidalCategory source)
  (let module D = MonoidalCategory target)
  (𝓕 : AFunctor C.thecat D.thecat)
  (open AFunctor 𝓕)
  (e : D.𝟏 D.⟶ F₀ C.𝟏)
  (μ : ∀ x y → (F₀ x D.⊗ F₀ y) D.⟶ F₀ (x C.⊗ y))
  where
  record IsLaxMonoidalFunctor : Ø 𝔬₁ ∙̂ 𝔯₁ ∙̂ ℓ₁ ∙̂ 𝔬₂ ∙̂ 𝔯₂ ∙̂ ℓ₂ where
    field
      associativity : ∀ x y z
        → ((μ x y D.⨂ D.i) D.↦ (μ (x C.⊗ y) z D.↦ F₁ (C.assoc x y z)))
              D.≈̇
          (D.assoc (F₀ x) (F₀ y) (F₀ z) D.↦ ((D.i D.⨂ μ y z) D.↦ μ x (y C.⊗ z)))
      left-unitality : ∀ x → (D.lu (F₀ x)) D.≈̇ ((e D.⨂ D.i) D.↦ (μ C.𝟏 x D.↦ F₁ (C.lu x)))
      right-unitality : ∀ x → (D.ru (F₀ x)) D.≈̇ ((D.i D.⨂ e) D.↦ (μ x C.𝟏 D.↦ F₁ (C.ru x)))

record GenericApplicativeRaw
  {lc ld} {Oc : Ø lc} {Od : Ø ld}
  (F : Oc → Od)
  (1c : Oc) (1d : Od)
  (_⊗c_ : Oc → Oc → Oc) (_⊗d_ : Od → Od → Od)
  {ℓc} (_⟶c_ : Oc → Oc → Ø ℓc)
  {ℓd} (_⟶d_ : Od → Od → Ø ℓd)
  : Ø ℓd ∙̂ lc ∙̂ ℓc
  where
  field
    m : ∀ {x y} → x ⟶c y → F x ⟶d F y -- fmap
    e : 1d ⟶d F 1c -- pure
    μ : ∀ {x y} → (F x ⊗d F y) ⟶d F (x ⊗c y) -- apply

  -- _<*>_ : ∀ {x y : Oc} → ? → ? → {!!} --  F (x ⟶c y) → F x ⟶d F y
  -- _<*>_ f x = m ? (μ )

{-
  _<*>_ : ∀ {A B} → F (A → B) → F A → F B
  _<*>_ f x = sfmap (λ {(f , x) → f x}) (f <s> x)
-}

{-
record ContainedGenericApplicativeRaw
  {lc ld} {Oc : Ø lc} {Od : Ø ld}
  (F : Oc → Od)
  (1c : Oc) (1d : Od)
  (_⊗c_ : Oc → Oc → Oc) (_⊗d_ : Od → Od → Od)
  {ℓd} (_⟶d_ : Od → Od → Ø ℓd)
  : Ø ℓd ∙̂ lc
  where
  field
    e : 1d ⟶d F 1c
    μ : ∀ {x y} → (F x ⊗d F y) ⟶d F (x ⊗c y)
-}
open import Oscar.Data.𝟙
open import Oscar.Data.Proposequality

record Action {a b} {A : Set a} {B : Set b} {f g h} (F : A → B → Set f) (G : A → Set g) (H : B → Set h) : Ø a ∙̂ b ∙̂ f ∙̂ g ∙̂ h where
  field
    act : ∀ {x y} → F x y → G x → H y

record SetApplyM {a b} (F : Set a → Set b)
  -- (𝟏ᴬ : Set a) (𝟏ᴮ : Set b) (_⊕_ : Set p → Set p → Set p) (_⟶_ : A → A → Set ℓ)
  : Ø ↑̂ a ∙̂ b where
  field
    sfmap : ∀ {A B} → (A → B) → F A → F B
    sunit : Lift {_} {a} 𝟙 → F (Lift 𝟙)
    _<s>_ : ∀ {A B} → F A → F B → F (A × B)
  _<*>_ : ∀ {A B} → F (A → B) → F A → F B
  _<*>_ f x = sfmap (λ {(f , x) → f x}) (f <s> x)
  _⨂_ : ∀ {A B C D : Ø a} → (A → B) → (C → D) → A × C → B × D
  _⨂_ f g ac = let (a , c) = ac in f a , g c
  assoc : ∀ {A B C : Ø a} → A × (B × C) → (A × B) × C
  assoc abc = let (a , (b , c)) = abc in (a , b) , c
  field
    law-nat : ∀ {A B C D} (f : A → B) (g : C → D) u v → sfmap (f ⨂ g) (u <s> v) ≡ (sfmap f u <s> sfmap g v)
    leftid : ∀ {B} (v : F B) → sfmap π₁ (sunit _ <s> v) ≡ v
    righttid : ∀ {A} (u : F A) → sfmap π₀ (u <s> sunit _) ≡ u
    associativity : ∀ {A B C} u v w → sfmap (assoc {A} {B} {C}) (u <s> (v <s> w)) ≡ ((u <s> v) <s> w)

  source-cat : MonoidalCategory _ _ _
  source-cat .MonoidalCategory.thecat .Category.𝔒 = Ø a
  source-cat .MonoidalCategory.thecat .Category._∼_ = Function
  source-cat .MonoidalCategory.thecat .Category._∼̇_ = _≡̇_
  source-cat .MonoidalCategory.thecat .Category.category-ε = ¡
  source-cat .MonoidalCategory.thecat .Category._↦_ = flip _∘′_
  source-cat .MonoidalCategory.thecat .Category.`IsCategory = {!!}
  source-cat .MonoidalCategory.thefunc .AFunctor.F₀ (A , B) = A × B
  source-cat .MonoidalCategory.thefunc .AFunctor.F₁ = {!!}
  source-cat .MonoidalCategory.thefunc .AFunctor.isFunctor = {!!}
  source-cat .MonoidalCategory.𝟏 = Lift 𝟙
  source-cat .MonoidalCategory.associator = {!!}
  source-cat .MonoidalCategory.left-unitor = {!!}
  source-cat .MonoidalCategory.right-unitor = {!!}
  source-cat .MonoidalCategory.triangle-identity = {!!}
  source-cat .MonoidalCategory.pentagon-identity = {!!}

  target-cat : MonoidalCategory _ _ _
  target-cat .MonoidalCategory.thecat .Category.𝔒 = Ø b
  target-cat .MonoidalCategory.thecat .Category._∼_ = Function
  target-cat .MonoidalCategory.thecat .Category._∼̇_ = _≡̇_
  target-cat .MonoidalCategory.thecat .Category.category-ε = ¡
  target-cat .MonoidalCategory.thecat .Category._↦_ = flip _∘′_
  target-cat .MonoidalCategory.thecat .Category.`IsCategory = {!!}
  target-cat .MonoidalCategory.thefunc .AFunctor.F₀ (A , B) = A × B
  target-cat .MonoidalCategory.thefunc .AFunctor.F₁ = {!!}
  target-cat .MonoidalCategory.thefunc .AFunctor.isFunctor = {!!}
  target-cat .MonoidalCategory.𝟏 = Lift 𝟙
  target-cat .MonoidalCategory.associator = {!!}
  target-cat .MonoidalCategory.left-unitor = {!!}
  target-cat .MonoidalCategory.right-unitor = {!!}
  target-cat .MonoidalCategory.triangle-identity = {!!}
  target-cat .MonoidalCategory.pentagon-identity = {!!}

  module C = MonoidalCategory source-cat
  module D = MonoidalCategory target-cat

  the-functor : AFunctor C.thecat D.thecat
  the-functor .AFunctor.F₀ = F
  the-functor .AFunctor.F₁ = sfmap
  the-functor .AFunctor.isFunctor = {!!}

  open AFunctor the-functor

  the-e : D.𝟏 D.⟶ F₀ C.𝟏 -- F (Lift 𝟙)
  the-e = {!!}

  the-μ : ∀ x y → (F₀ x D.⊗ F₀ y) D.⟶ F₀ (x C.⊗ y) -- F A → F B → F (A × B)
  the-μ A B (FA , FB) = FA <s> FB

toSetApply : ∀ {a b} (F : Set a → Set b) (gar : GenericApplicativeRaw F (Lift 𝟙) (Lift 𝟙) (λ A B → A × B) (λ A B → A × B) Function Function) → SetApplyM F
toSetApply F gar .SetApplyM.sfmap = GenericApplicativeRaw.m gar
toSetApply F gar .SetApplyM.sunit _ = GenericApplicativeRaw.e gar !
toSetApply F gar .SetApplyM._<s>_ FA FB = GenericApplicativeRaw.μ gar (FA , FB)
toSetApply F gar .SetApplyM.law-nat = {!!}
toSetApply F gar .SetApplyM.leftid = {!!}
toSetApply F gar .SetApplyM.righttid = {!!}
toSetApply F gar .SetApplyM.associativity = {!!}

module _
  {𝔬₁ 𝔯₁ ℓ₁ 𝔬₂ 𝔯₂ ℓ₂}
  (C : MonoidalCategory 𝔬₁ 𝔯₁ ℓ₁)
  (D : MonoidalCategory 𝔬₂ 𝔯₂ ℓ₂)
  where
  record LaxMonoidalFunctorWithStrength : Ø 𝔬₁ ∙̂ 𝔯₁ ∙̂ ℓ₁ ∙̂ 𝔬₂ ∙̂ 𝔯₂ ∙̂ ℓ₂ where
    field
      laxMonoidalFunctor : LaxMonoidalFunctor C D
    open LaxMonoidalFunctor laxMonoidalFunctor
    {-
    field
      β : ∀ v w → (v D.⊗ F₀ w) D.⟶ F₀ (v C.⊗ w)
      commute-5 : ∀ u v w → (C.assoc u v (F₀ w) C.↦ ((C.i C.⨂ β v w) C.↦ β u (v C.⊗ w))) C.≈̇ (β (u C.⊗ v) w C.↦ F₁ (C.assoc u v w))
      commute-3 : ∀ v → C.lu (F₀ v) C.≈̇ (β C.𝟏 v C.↦ F₁ (C.lu v))
      -- strength : TensorialStrength C (LaxMonoidalFunctor.𝓕 laxMonoidalEndofunctor)
    -}

module _ {𝔬 𝔯 ℓ} (V : MonoidalCategory 𝔬 𝔯 ℓ) (let C = MonoidalCategory.thecat V) (F : AFunctor C C) where
  open MonoidalCategory V
  open AFunctor F
  record TensorialStrength : Ø 𝔬 ∙̂ 𝔯 ∙̂ ℓ where
    field
      β : ∀ v w → (v ⊗ F₀ w) ⟶ F₀ (v ⊗ w)
      commute-5 : ∀ u v w → (assoc u v (F₀ w) ↦ ((i ⨂ β v w) ↦ β u (v ⊗ w))) ≈̇ (β (u ⊗ v) w ↦ F₁ (assoc u v w))
      commute-3 : ∀ v → lu (F₀ v) ≈̇ (β 𝟏 v ↦ F₁ (lu v))

module _
  {𝔬 𝔯 ℓ}
  (C : MonoidalCategory 𝔬 𝔯 ℓ)
  where
  record LaxMonoidalEndofunctorWithStrength : Ø 𝔬 ∙̂ 𝔯 ∙̂ ℓ where
    field
      laxMonoidalEndofunctor : LaxMonoidalFunctor C C
      strength : TensorialStrength C (LaxMonoidalFunctor.𝓕 laxMonoidalEndofunctor)

{- want parameters :
  X : Set a
  Y : Set b
  X₀ : X
  F : X → Y
  _⨁_ : X → X → Set a

  LaxMonoidalFunctor.e = unit : F X₀
  LaxMonoidalFunctor.μ = apply : ∀ {A B : X} → F A → F B → F (A ⨁ B)
  LaxMonoidalFunctor.𝓕.F₀ = F : X → Y

-}

record GenericApplyM {a ℓ} {A : Set a} (F : A → A) (𝟏 : A) (_⊕_ : A → A → A) (_⟶_ : A → A → Set ℓ) : Ø a ∙̂ ℓ where
  field
    gunit : 𝟏 ⟶ F 𝟏
    gproduct : ∀ {x y : A} → (F x ⊕ F y) ⟶ F (x ⊕ y)

open import Oscar.Data.𝟙
-- open import Oscar.Class.Kitten
open import Oscar.Class.Category
open import Oscar.Class.IsPrefunctor
open import Oscar.Class.IsCategory
open import Oscar.Class.IsPrecategory
open import Oscar.Property.Category.Function
open import Oscar.Class
open import Oscar.Class.Fmap
import Oscar.Class.Reflexivity.Function

module _
  {𝔬₁ 𝔬₂} (𝓕 : Ø 𝔬₁ → Ø 𝔬₂)
  (fmapper : Fmap 𝓕)
  (fpure : ∀ {𝔄} → 𝔄 → 𝓕 𝔄)
  (fapply : ∀ {𝔄 𝔅} → 𝓕 (𝔄 → 𝔅) → 𝓕 𝔄 → 𝓕 𝔅)
  where
  -- instance _ = fmapper
  fmap' = λ {A B} (f : A → B) → fapply (fpure f)
  mkProductMonoidalCategory : MonoidalCategory _ _ _
  mkProductMonoidalCategory .MonoidalCategory.thecat .Category.𝔒 = Ø 𝔬₁
  mkProductMonoidalCategory .MonoidalCategory.thecat .Category._∼_ = MFunction 𝓕
  mkProductMonoidalCategory .MonoidalCategory.thecat .Category._∼̇_ = Proposextensequality
  mkProductMonoidalCategory .MonoidalCategory.thecat .Category.category-ε = ε
  mkProductMonoidalCategory .MonoidalCategory.thecat .Category._↦_ = (flip _∘′_)
  mkProductMonoidalCategory .MonoidalCategory.thecat .Category.`IsCategory = ?
  mkProductMonoidalCategory .MonoidalCategory.thefunc .AFunctor.F₀ (A , B) = A × B
  mkProductMonoidalCategory .MonoidalCategory.thefunc .AFunctor.F₁ (f , g) xy = fapply (fmap' _,_ (f (fmap' π₀ xy))) (g (fmap' π₁ xy))
  mkProductMonoidalCategory .MonoidalCategory.thefunc .AFunctor.isFunctor .IsFunctor.`IsPrefunctor .IsPrefunctor.`𝓢urjtranscommutativity = {!!}
  mkProductMonoidalCategory .MonoidalCategory.thefunc .AFunctor.isFunctor .IsFunctor.`IsPrefunctor .IsPrefunctor.`𝓢urjextensionality = {!!}
  mkProductMonoidalCategory .MonoidalCategory.thefunc .AFunctor.isFunctor .IsFunctor.`𝒮urjidentity = {!!}
  mkProductMonoidalCategory .MonoidalCategory.𝟏 = {!!}
  mkProductMonoidalCategory .MonoidalCategory.associator = {!!}
  mkProductMonoidalCategory .MonoidalCategory.left-unitor = {!!}
  mkProductMonoidalCategory .MonoidalCategory.right-unitor = {!!}
  mkProductMonoidalCategory .MonoidalCategory.triangle-identity = {!!}
  mkProductMonoidalCategory .MonoidalCategory.pentagon-identity = {!!}

record HApplicativeFunctor {𝔬₁ 𝔬₂} (𝓕 : Ø 𝔬₁ → Ø 𝔬₂) : Ø (↑̂ (↑̂ 𝔬₁ ∙̂ 𝔬₂)) where
  constructor ∁
  field
    fmapper : Fmap 𝓕
    fpure : ∀ {𝔄} → 𝔄 → 𝓕 𝔄
    fapply : ∀ {𝔄 𝔅} → 𝓕 (𝔄 → 𝔅) → 𝓕 𝔄 → 𝓕 𝔅


  field
    isStrongLaxMonoidalEndofunctor : LaxMonoidalEndofunctorWithStrength (mkProductMonoidalCategory 𝓕 fmapper fpure fapply)

  module LMF = LaxMonoidalFunctor (LaxMonoidalEndofunctorWithStrength.laxMonoidalEndofunctor isStrongLaxMonoidalEndofunctor)
  derive-fpure : ∀ {𝔄} → 𝔄 → 𝓕 𝔄
  derive-fpure = {!LMF!} where

  {-
    ⦃ isFunctor ⦄ : IsFunctor
                       {𝔒₁ = Ø 𝔬₁} (λ A B → A × 𝓕 B)
                         {!(λ { {A} {B} (x₁ , f₁) (x₂ , f₂) → {!(x₁ ≡ x₂) × !}})!} (λ {A} → {!!} , {!!}) {!!}
                       {𝔒₂ = Ø 𝔬₁} {!!}
                         {!!} {!!} {!!}
                       {!!}
  -}

record MonoidalFunctor {𝔬₁ 𝔬₂} (𝓕 : Ø 𝔬₁ → Ø 𝔬₂) : Ø (↑̂ (↑̂ 𝔬₁ ∙̂ 𝔬₂)) where
  constructor ∁
  field
    ⦃ isFmap ⦄ : Fmap 𝓕
    unit : 𝓕 (Lift 𝟙)
    mappend : ∀ {𝔄 𝔅} → 𝓕 𝔄 → 𝓕 𝔅 → 𝓕 (𝔄 × 𝔅)
    {-
    ⦃ isFunctor ⦄ : IsFunctor
                       Function⟦ 𝔬₁ ⟧
                         Proposextensequality ε (flip _∘′_)
                       (MFunction 𝓕)
                         Proposextensequality ε (flip _∘′_)
                       {!!}
    -}
  pure : ∀ {𝔄} → 𝔄 → 𝓕 𝔄
  pure x = fmap (x ∞) unit

  infixl 4 _<*>_
  _<*>_ : ∀ {𝔄 𝔅} → 𝓕 (𝔄 → 𝔅) → 𝓕 𝔄 → 𝓕 𝔅
  f <*> x = fmap (λ {(f , x) → f x}) (mappend f x)

  app-identity : ∀ {𝔄} (v : 𝓕 𝔄) → (pure ¡[ 𝔄 ] <*> v) ≡ v
  app-identity v = {!!}

open MonoidalFunctor ⦃ … ⦄ public using (unit; mappend)


-- record ApplicativeFunctor where
module Purity
  {𝔵₁ 𝔵₂ 𝔯} {𝔛₁ : Ø 𝔵₁} {𝔛₂ : Ø 𝔵₂} (F : 𝔛₁ → 𝔛₂) (x₁ : 𝔛₁) (x₂ : 𝔛₂) (_⟶_ : 𝔛₂ → 𝔛₂ → Ø 𝔯)
  = ℭLASS (F , x₁ , x₂ , _⟶_) (x₂ ⟶ F x₁)

module Applicativity
  {𝔵₁ 𝔵₂ 𝔯} {𝔛₁ : Ø 𝔵₁} {𝔛₂ : Ø 𝔵₂} (F : 𝔛₁ → 𝔛₂) (_⊗₁_ : 𝔛₁ → 𝔛₁ → 𝔛₁) (_⊗₂_ : 𝔛₂ → 𝔛₂ → 𝔛₂) (_⟶_ : 𝔛₂ → 𝔛₂ → Ø 𝔯)
  = ℭLASS (F , _⊗₁_ , _⊗₂_ , _⟶_) (∀ x y → (F x ⊗₂ F y) ⟶ F (x ⊗₁ y))

-- FunctionalMonoidalCategory

AFunctorFunction²Function : ∀ {𝔬₁} → AFunctor (productCat (CategoryFunction {𝔬₁}) (CategoryFunction {𝔬₁})) (CategoryFunction {𝔬₁})
AFunctorFunction²Function .AFunctor.F₀ = uncurry _×_
AFunctorFunction²Function .AFunctor.F₁ (f₁ , f₂) (x₁ , x₂) = f₁ x₁ , f₂ x₂
AFunctorFunction²Function .AFunctor.isFunctor .IsFunctor.`IsPrefunctor .IsPrefunctor.`𝓢urjtranscommutativity = {!!}
AFunctorFunction²Function .AFunctor.isFunctor .IsFunctor.`IsPrefunctor .IsPrefunctor.`𝓢urjextensionality = {!!}
AFunctorFunction²Function .AFunctor.isFunctor .IsFunctor.`𝒮urjidentity = {!!}

record LMF {𝔬₁ 𝔬₂} (𝓕 : Ø 𝔬₁ → Ø 𝔬₂) ⦃ _ : Fmap 𝓕 ⦄ : Ø ↑̂ (↑̂ 𝔬₁ ∙̂ 𝔬₂) where
  constructor ∁
  field
    lmf-pure : Purity.type 𝓕 (Lift 𝟙) (Lift 𝟙) Function
    lmf-apply : Applicativity.type 𝓕 _×_ _×_ Function

  lmf-happly : ∀ {𝔄 𝔅} → 𝓕 (𝔄 → 𝔅) → 𝓕 𝔄 → 𝓕 𝔅
  lmf-happly f x = fmap (λ {(f , x) → f x}) (lmf-apply _ _ (f , x))

  field
    ⦃ islmf ⦄ : IsLaxMonoidalFunctor (∁ CategoryFunction (∁ (uncurry _×_) {!!} {!!}) (Lift 𝟙) {!!} {!!} {!!} {!!} {!!}) (∁ CategoryFunction (∁ (uncurry _×_) {!!} {!!}) ((Lift 𝟙)) {!!} {!!} {!!} {!!} {!!}) (record { F₀ = 𝓕 ; F₁ = fmap ; isFunctor = ∁ ⦃ {!!} ⦄ ⦃ ! ⦄ ⦃ ! ⦄ ⦃ {!!} ⦄  }) lmf-pure lmf-apply
