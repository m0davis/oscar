{-# OPTIONS --show-implicit #-}
{-# OPTIONS --postfix-projections #-}
module Oscar.Class where

open import Oscar.Prelude

open import Oscar.Data using (_≡_)

{-
prop = a "property", a function usable in programs
super = a "superclass", a set of records
type super = a "qualification", a type that is constrained by other records
type type super = type, but the constraint is itself another qual
super prop = a property that is parameterised by a set of records; i.e. a superclass that is extended to a given function
type prop = a property that is parameterised by a type

IsReflexive prop
IsSymmetric prop
IsTransitive prop
IsTransextensional super prop
IsTransassociative super prop
IsMappable type prop
IsMapextensional super prop
IsMaptranscommutative super prop
IsTransleftidentity super prop
IsTransrightidentity super prop
IsMapidentity super prop
IsCongruous prop
IsCongruous₂ prop
IsĊongruous prop

IsEquivalence super
IsPrefunctor super
IsFunctor super

HasArrowEquality type super
IsSetoid type super ==> ObjectEquality or _≋_
Setoid type type-super ==> Object
Precategory type type-super ==> ArrowEquality or ?
Category ?
Prefunctor type ?super
Functor type ?super
-}

module _ where

  module _
    {a} {A : Ø a}
    {b} (_⊸_ : A → A → Ø b)
    where
    𝓻eflexivity = ∀ {x} → x ⊸ x
    record IsReflexive : Ø a ∙̂ b where
      field reflexivity : 𝓻eflexivity

    open IsReflexive ⦃ … ⦄ public

  module _ where

    ε = reflexivity

    ε[_] : ∀
      {a} {A : Ø a}
      {b} (_⊸_ : A → A → Ø b)
      ⦃ _ : IsReflexive _⊸_ ⦄
      → ∀ {x} → x ⊸ x
    ε[ _ ] = reflexivity

module _ where

  record IsSymmetric
    {a} {A : Ø a}
    {b} (_⊸_ : A → A → Ø b)
    : Ø a ∙̂ b where
    field symmetry : ∀ {x y} → x ⊸ y → y ⊸ x

  open IsSymmetric ⦃ … ⦄ public

module _ where

  module _
    {a} {A : Ø a}
    {b} (_⊸_ : A → A → Ø b)
    where
    𝓽ransitivity = ∀ {x y z} → x ⊸ y → y ⊸ z → x ⊸ z
    record IsTransitive : Ø a ∙̂ b where
      field transitivity : 𝓽ransitivity

    open IsTransitive ⦃ … ⦄ public

  module _ where

    infixr 9 _∙_
    _∙_ : ∀
      {a} {A : Ø a}
      {b} {_⊸_ : A → A → Ø b}
      ⦃ _ : IsTransitive _⊸_ ⦄
      {x y z} → y ⊸ z → x ⊸ y → x ⊸ z
    g ∙ f = transitivity f g

module _ where

  module _
    {a} {A : Ø a}
    {m} (_⊸_ : A → A → Ø m)
    {ℓ} (_≋_ : ∀ {x y} → x ⊸ y → x ⊸ y → Ø ℓ)
    where
    module _
      (transitivity : 𝓽ransitivity _⊸_)
      where
      𝓽ransextensionality =
        ∀ {x y z} {f₁ f₂ : x ⊸ y} {g₁ g₂ : y ⊸ z} → f₁ ≋ f₂ → g₁ ≋ g₂ → transitivity f₁ g₁ ≋ transitivity f₂ g₂
    record IsTransextensional : Ø a ∙̂ m ∙̂ ℓ where
      field
        isTransitive : IsTransitive _⊸_
        transextensionality :
          asInstance isTransitive $
          𝓽ransextensionality transitivity

    open IsTransextensional ⦃ … ⦄ public using (transextensionality)

  record IsTransassociative
    {a} {A : Ø a}
    {m} (_⊸_ : A → A → Ø m)
    {ℓ} (_≋_ : ∀ {x y} → x ⊸ y → x ⊸ y → Ø ℓ)
    : Ø a ∙̂ m ∙̂ ℓ where
    field
      isTransitive : IsTransitive _⊸_
      transassociativity :
        asInstance isTransitive $
        ∀ {w x y z} (f : w ⊸ x) (g : x ⊸ y) (h : y ⊸ z) → ((h ∙ g) ∙ f) ≋ (h ∙ g ∙ f)

  open IsTransassociative ⦃ … ⦄ public using (transassociativity)

module _ where

  module _
    {a₁} {A₁ : Ø a₁}
    {m₁} (_⊸₁_ : A₁ → A₁ → Ø m₁)
    {a₂} {A₂ : Ø a₂}
    {m₂} (_⊸₂_ : A₂ → A₂ → Ø m₂)
    (μ : A₁ → A₂)
    where
    𝓶ap = ∀ {x y} → x ⊸₁ y → μ x ⊸₂ μ y

  record IsMappable
    {a₁} {A₁ : Ø a₁}
    {m₁} (_⊸₁_ : A₁ → A₁ → Ø m₁)
    {a₂} {A₂ : Ø a₂}
    {m₂} (_⊸₂_ : A₂ → A₂ → Ø m₂)
    : Ø a₁ ∙̂ m₁ ∙̂ a₂ ∙̂ m₂ where
    field
      μ : A₁ → A₂
      map : ∀ {x y} → x ⊸₁ y → μ x ⊸₂ μ y

  open IsMappable ⦃ … ⦄ public using (map)

  module _ where

    map[_] : ∀
      {a₁} {A₁ : Ø a₁}
      {m₁} {_⊸₁_ : A₁ → A₁ → Ø m₁}
      {a₂} {A₂ : Ø a₂}
      {m₂} (_⊸₂_ : A₂ → A₂ → Ø m₂)
      ⦃ isMappable : IsMappable _⊸₁_ _⊸₂_ ⦄
      → ∀ {x y} → x ⊸₁ y → IsMappable.μ isMappable x ⊸₂ IsMappable.μ isMappable y
    map[ _ ] = map

module _ where

  module _
    {a₁} {A₁ : Ø a₁}
    {m₁} (_⊸₁_ : A₁ → A₁ → Ø m₁)
    {ℓ₁} (_≋₁_ : ∀ {x y} → x ⊸₁ y → x ⊸₁ y → Ø ℓ₁)
    {a₂} {A₂ : Ø a₂}
    {m₂} (_⊸₂_ : A₂ → A₂ → Ø m₂)
    {ℓ₂} (_≋₂_ : ∀ {x y} → x ⊸₂ y → x ⊸₂ y → Ø ℓ₂)
    where
    module _
      {μ : A₁ → A₂}
      (map : 𝓶ap _⊸₁_ _⊸₂_ μ)
      where
      𝓶apextensionality = ∀ {x y} {f₁ f₂ : x ⊸₁ y} → f₁ ≋₁ f₂ → map f₁ ≋₂ map f₂

    record IsMapextensional : Ø a₁ ∙̂ m₁ ∙̂ a₂ ∙̂ m₂ ∙̂ ℓ₁ ∙̂ ℓ₂ where
      field
        isMappable : IsMappable _⊸₁_ _⊸₂_
        mapextensionality :
          asInstance isMappable $
          𝓶apextensionality map

    open IsMapextensional ⦃ … ⦄ public using (mapextensionality)

module _ where

  module _
    {a₁} {A₁ : Ø a₁}
    {m₁} (_⊸₁_ : A₁ → A₁ → Ø m₁)
    {a₂} {A₂ : Ø a₂}
    {m₂} (_⊸₂_ : A₂ → A₂ → Ø m₂)
    {ℓ₂} (_≋₂_ : ∀ {x y} → x ⊸₂ y → x ⊸₂ y → Ø ℓ₂)
    where
    module _
      {μ : A₁ → A₂}
      (map : 𝓶ap _⊸₁_ _⊸₂_ μ)
      (transitivity₁ : 𝓽ransitivity _⊸₁_)
      (transitivity₂ : 𝓽ransitivity _⊸₂_)
      where
      𝓶aptranscommutativity = ∀ {x y z} (f : x ⊸₁ y) (g : y ⊸₁ z) → map (transitivity₁ f g) ≋₂ transitivity₂ (map f) (map g)

    record IsMaptranscommutative : Ø a₁ ∙̂ a₂ ∙̂ m₁ ∙̂ m₂ ∙̂ ℓ₂ where
      field
        isMappable : IsMappable _⊸₁_ _⊸₂_
        isTransitive₁ : IsTransitive _⊸₁_
        isTransitive₂ : IsTransitive _⊸₂_
        maptranscommutativity :
          asInstance isMappable $
          asInstance isTransitive₁ $
          asInstance isTransitive₂ $
          𝓶aptranscommutativity map transitivity transitivity

    open IsMaptranscommutative ⦃ … ⦄ public using (maptranscommutativity)

module _ where

  record IsTransleftidentity
    {o} {Object : Ø o}
    {a} (Arrow : Object → Object → Ø a)
    {ℓ} (ArrowEquality : ∀ {x y} → Arrow x y → Arrow x y → Ø ℓ)
    : Ø o ∙̂ a ∙̂ ℓ where
    field
      isReflexive : IsReflexive Arrow
      isTransitive : IsTransitive Arrow
      transleftidentity :
        asInstance isReflexive $
        asInstance isTransitive $
        ∀ {x y} {f : Arrow x y} → ArrowEquality (ε ∙ f) f

  open IsTransleftidentity ⦃ … ⦄ using (transleftidentity)

module _ where

  record IsTransrightidentity
    {o} {Object : Ø o}
    {a} (Arrow : Object → Object → Ø a)
    {ℓ} (ArrowEquality : ∀ {x y} → Arrow x y → Arrow x y → Ø ℓ)
    : Ø o ∙̂ a ∙̂ ℓ where
    field
      isReflexive : IsReflexive Arrow
      isTransitive : IsTransitive Arrow
      transrightidentity :
        asInstance isReflexive $
        asInstance isTransitive $
        ∀ {x y} {f : Arrow x y} → ArrowEquality (f ∙ ε) f

  open IsTransrightidentity ⦃ … ⦄ using (transrightidentity)

module _ where

  record IsMapidentity
    {o₁} {Object₁ : Ø o₁}
    {a₁} (Arrow₁ : Object₁ → Object₁ → Ø a₁)
    {o₂} {Object₂ : Ø o₂}
    {a₂} (Arrow₂ : Object₂ → Object₂ → Ø a₂)
    {ℓ₂} (ArrowEquality₂ : ∀ {x y} → Arrow₂ x y → Arrow₂ x y → Ø ℓ₂)
    : Ø o₁ ∙̂ a₁ ∙̂ o₂ ∙̂ a₂ ∙̂ ℓ₂ where
    field
      isMappable : IsMappable Arrow₁ Arrow₂
      isReflexive₁ : IsReflexive Arrow₁
      isReflexive₂ : IsReflexive Arrow₂
      mapidentity :
        asInstance isMappable $
        asInstance isReflexive₁ $
        asInstance isReflexive₂ $
        ∀ {x} → ArrowEquality₂ (map (ε[ Arrow₁ ] {x})) ε

  open IsMapidentity ⦃ … ⦄ using (mapidentity)









module _ where

  record IsEquivalence
    {a} {A : Ø a}
    {b} (_⊸_ : A → A → Ø b)
    : Ø a ∙̂ b where
    field
      isReflexive : IsReflexive _⊸_
      isSymmetric : IsSymmetric _⊸_
      isTransitive : IsTransitive _⊸_






module _ where

  record IsEquality {o} (Object : Set o) ℓ : Ø o ∙̂ ↑̂ ℓ where
    field
      ObjectEquality : Object → Object → Ø ℓ
      isEquivalence : IsEquivalence ObjectEquality

  module _ where

    infix 4 _≋_
    _≋_ : ∀ {o} {Object : Ø o} {ℓ} ⦃ _ : IsEquality Object ℓ ⦄ → Object → Object → Ø ℓ
    _≋_ = ! .IsEquality.ObjectEquality

  module _
    {a} {A : Ø a}
    {m} (_⊸_ : A → A → Ø m)
    {ℓ} ⦃ _ : ∀ {x y} → IsEquality (x ⊸ y) ℓ ⦄
    where
    module _
      ⦃ _ : IsTransitive _⊸_ ⦄
      where
      𝓽ransextensionality! = 𝓽ransextensionality _⊸_ _≋_ transitivity
    IsTransextensional! = IsTransextensional _⊸_ _≋_

  module _
    {a₁} {A₁ : Ø a₁}
    {m₁} (_⊸₁_ : A₁ → A₁ → Ø m₁)
    {ℓ₁} ⦃ _ : ∀ {x y} → IsEquality (x ⊸₁ y) ℓ₁ ⦄
    {a₂} {A₂ : Ø a₂}
    {m₂} (_⊸₂_ : A₂ → A₂ → Ø m₂)
    {ℓ₂} ⦃ _ : ∀ {x y} → IsEquality (x ⊸₂ y) ℓ₂ ⦄
    where
    module _
      ⦃ _ : IsMappable _⊸₁_ _⊸₂_ ⦄
      where
      𝓶apextensionality! = 𝓶apextensionality _⊸₁_ _≋_ _⊸₂_ _≋_ map
    IsMapextensional! = IsMapextensional _⊸₁_ _≋_ _⊸₂_ _≋_

  module _
    {a₁} {A₁ : Ø a₁}
    {m₁} (_⊸₁_ : A₁ → A₁ → Ø m₁)
    {a₂} {A₂ : Ø a₂}
    {m₂} (_⊸₂_ : A₂ → A₂ → Ø m₂)
    {ℓ₂} ⦃ _ : ∀ {x y} → IsEquality (x ⊸₂ y) ℓ₂ ⦄
    where
    module _
      ⦃ isMappable : IsMappable _⊸₁_ _⊸₂_ ⦄
      ⦃ isTransitive₁ : IsTransitive _⊸₁_ ⦄
      ⦃ isTransitive₂ : IsTransitive _⊸₂_ ⦄
      where
      𝓶aptranscommutativity! = 𝓶aptranscommutativity _⊸₁_ _⊸₂_ _≋_ map transitivity transitivity
    IsMaptranscommutative! = IsMaptranscommutative _⊸₁_ _⊸₂_ _≋_









module _ where

  record IsPrecategory
    {o} {Object : Ø o}
    {a} (Arrow : Object → Object → Ø a)
    {ℓ} (ArrowEquality : ∀ {x y} → Arrow x y → Arrow x y → Ø ℓ)
    : Ø o ∙̂ a ∙̂ ℓ where
    field
      isTransitive : IsTransitive Arrow
      isEquivalence : ∀ {x y} → IsEquivalence (ArrowEquality {x} {y})
      isTransassociative : IsTransassociative Arrow ArrowEquality
      isTransextensional : IsTransextensional Arrow ArrowEquality
      isTransitive∈isTransassociative : isTransitive ≡ IsTransassociative.isTransitive isTransassociative
      isTransitive∈isTransextensional : isTransitive ≡ IsTransextensional.isTransitive isTransextensional

  record IsPrefunctor
    {o₁} {Object₁ : Ø o₁}
    {a₁} (Arrow₁ : Object₁ → Object₁ → Ø a₁)
    {ℓ₁} (ArrowEquality₁ : ∀ {x y} → Arrow₁ x y → Arrow₁ x y → Ø ℓ₁)
    {o₂} {Object₂ : Ø o₂}
    {a₂} (Arrow₂ : Object₂ → Object₂ → Ø a₂)
    {ℓ₂} (ArrowEquality₂ : ∀ {x y} → Arrow₂ x y → Arrow₂ x y → Ø ℓ₂)
    : Ø o₁ ∙̂ a₁ ∙̂ ℓ₁ ∙̂ o₂ ∙̂ a₂ ∙̂ ℓ₂ where
    field
      isPrecategory₁ : IsPrecategory Arrow₁ ArrowEquality₁
      isPrecategory₂ : IsPrecategory Arrow₂ ArrowEquality₂
      isMappable
        : IsMappable Arrow₁ Arrow₂
      isMapextensional
        : IsMapextensional Arrow₁ ArrowEquality₁ Arrow₂ ArrowEquality₂
      isMaptranscommutative
        : IsMaptranscommutative Arrow₁ Arrow₂ ArrowEquality₂
      isMappable∈isMapextensional
        : isMappable ≡ IsMapextensional.isMappable isMapextensional
      isMappable∈isMaptranscommutative
        : isMappable ≡ IsMaptranscommutative.isMappable isMaptranscommutative
      isTransitive₁∈isMaptranscommutative
        : isPrecategory₁ .IsPrecategory.isTransitive ≡ IsMaptranscommutative.isTransitive₁ isMaptranscommutative
      isTransitive₂∈isMaptranscommutative
        : isPrecategory₂ .IsPrecategory.isTransitive ≡ IsMaptranscommutative.isTransitive₂ isMaptranscommutative

  record IsCategory
    {o} {Object : Ø o}
    {a} (Arrow : Object → Object → Ø a)
    {ℓ} (ArrowEquality : ∀ {x y} → Arrow x y → Arrow x y → Ø ℓ)
    : Ø o ∙̂ a ∙̂ ℓ where
    field
      isPrecategory : IsPrecategory Arrow ArrowEquality
    open IsPrecategory isPrecategory public
    field
      isTransleftidentity
        : IsTransleftidentity Arrow ArrowEquality
    open IsTransleftidentity isTransleftidentity using (isReflexive) public
    field
      isTransrightidentity
        : IsTransrightidentity Arrow ArrowEquality
      isTransitive∈isTransleftidentity
        : isTransitive ≡ isTransleftidentity .IsTransleftidentity.isTransitive
      isTransitive∈isTransrightidentity
        : isTransitive ≡ isTransrightidentity .IsTransrightidentity.isTransitive
      isReflexive∈Transleftidentity≡isReflexiveTransrightidentity
        : isReflexive ≡ isTransrightidentity .IsTransrightidentity.isReflexive

  record IsFunctor
    {o₁} {Object₁ : Ø o₁}
    {a₁} (Arrow₁ : Object₁ → Object₁ → Ø a₁)
    {ℓ₁} (ArrowEquality₁ : ∀ {x y} → Arrow₁ x y → Arrow₁ x y → Ø ℓ₁)
    {o₂} {Object₂ : Ø o₂}
    {a₂} (Arrow₂ : Object₂ → Object₂ → Ø a₂)
    {ℓ₂} (ArrowEquality₂ : ∀ {x y} → Arrow₂ x y → Arrow₂ x y → Ø ℓ₂)
    : Ø o₁ ∙̂ a₁ ∙̂ ℓ₁ ∙̂ o₂ ∙̂ a₂ ∙̂ ℓ₂ where
    field
      isCategory₁ : IsCategory Arrow₁ ArrowEquality₁
      isCategory₂ : IsCategory Arrow₂ ArrowEquality₂
      isPrefunctor : IsPrefunctor Arrow₁ ArrowEquality₁ Arrow₂ ArrowEquality₂
      isPrecategory₁≡ : isPrefunctor .IsPrefunctor.isPrecategory₁ ≡ isCategory₁ .IsCategory.isPrecategory
      isPrecategory₂≡ : isPrefunctor .IsPrefunctor.isPrecategory₂ ≡ isCategory₂ .IsCategory.isPrecategory
      isMapidentity
        : IsMapidentity Arrow₁ Arrow₂ ArrowEquality₂
      isMappable/isMapidentity∈isPrefunctor
        : isMapidentity .IsMapidentity.isMappable ≡ isPrefunctor .IsPrefunctor.isMappable
      isReflexive₁/isMapidentity∈category₁
        : isMapidentity .IsMapidentity.isReflexive₁ ≡ isCategory₁ .IsCategory.isReflexive
      isReflexive₂/isMapidentity∈category₂
        : isMapidentity .IsMapidentity.isReflexive₂ ≡ isCategory₂ .IsCategory.isReflexive

module _ where

  record Setoid o ℓ : Ø ↑̂ (o ∙̂ ℓ) where
    field
      Object : Ø o
      ObjectEquality : Object → Object → Ø ℓ
      isEquivalence : IsEquivalence ObjectEquality

  record Precategory o a ℓ : Ø ↑̂ (o ∙̂ a ∙̂ ℓ) where
    field
      Object : Ø o
      Arrow : Object → Object → Ø a
      ArrowEquality : ∀ {x y} → Arrow x y → Arrow x y → Ø ℓ
      isPrecategory : IsPrecategory Arrow ArrowEquality

  record Prefunctor o₁ a₁ ℓ₁ o₂ a₂ ℓ₂ : Ø ↑̂ (o₁ ∙̂ a₁ ∙̂ ℓ₁ ∙̂ o₂ ∙̂ a₂ ∙̂ ℓ₂) where
    field
      Object₁ : Ø o₁
      Arrow₁ : Object₁ → Object₁ → Ø a₁
      ArrowEquality₁ : ∀ {x y} → Arrow₁ x y → Arrow₁ x y → Ø ℓ₁
      Object₂ : Ø o₂
      Arrow₂ : Object₂ → Object₂ → Ø a₂
      ArrowEquality₂ : ∀ {x y} → Arrow₂ x y → Arrow₂ x y → Ø ℓ₂
      isPrefunctor : IsPrefunctor Arrow₁ ArrowEquality₁ Arrow₂ ArrowEquality₂

  record Category o a ℓ : Ø ↑̂ (o ∙̂ a ∙̂ ℓ) where
    field
      Object : Ø o
      Arrow : Object → Object → Ø a
      ArrowEquality : ∀ {x y} → Arrow x y → Arrow x y → Ø ℓ
      isCategory : IsCategory Arrow ArrowEquality

  record Functor o₁ a₁ ℓ₁ o₂ a₂ ℓ₂ : Ø ↑̂ (o₁ ∙̂ a₁ ∙̂ ℓ₁ ∙̂ o₂ ∙̂ a₂ ∙̂ ℓ₂) where
    field
      Object₁ : Ø o₁
      Arrow₁ : Object₁ → Object₁ → Ø a₁
      ArrowEquality₁ : ∀ {x y} → Arrow₁ x y → Arrow₁ x y → Ø ℓ₁
      Object₂ : Ø o₂
      Arrow₂ : Object₂ → Object₂ → Ø a₂
      ArrowEquality₂ : ∀ {x y} → Arrow₂ x y → Arrow₂ x y → Ø ℓ₂
      isFunctor : IsFunctor Arrow₁ ArrowEquality₁ Arrow₂ ArrowEquality₂

module _ where

  record IsCongruous
    a b {c} (C : ∀ {x} {X : Ø x} → X → X → Ø c)
    : Ø ↑̂ (a ∙̂ b ∙̂ c) where
    field congruity : ∀ {A : Ø a} {B : Ø b} {x y} (f : A → B) → C x y → C (f x) (f y)

  open IsCongruous ⦃ … ⦄ public

module _ where

  record IsCongruous₂
    a b c {ℓ} (EQ : ∀ {x} {X : Ø x} → X → X → Ø ℓ)
    : Ø ↑̂ (a ∙̂ b ∙̂ c) ∙̂ ℓ where
    field congruity₂ : ∀ {A : Ø a} {B : Ø b} {C : Ø c} {x y} {x' y'} (f : A → B → C) → EQ x y → EQ x' y' → EQ (f x x') (f y y')

  open IsCongruous₂ ⦃ … ⦄ public

module _ where

  record IsĊongruous
    𝔬 𝔭 {c}
    (C : ∀ {𝔒 : Ø 𝔬} {𝔓 : 𝔒 → Ø 𝔭} → ((𝓞 : 𝔒) → 𝔓 𝓞) → ((𝓞 : 𝔒) → 𝔓 𝓞) → Ø c)
    : Ø ↑̂ (𝔬 ∙̂ 𝔭) ∙̂ c where
    field ċongruity : ∀ {𝔒 : Ø 𝔬} {𝔓 : 𝔒 → Ø 𝔭} {f g : (𝓞 : 𝔒) → 𝔓 𝓞} (F : ∀ {𝓞 : 𝔒} → 𝔓 𝓞 → 𝔓 𝓞) → C f g → C (F ∘ f) (F ∘ g)

  open IsĊongruous ⦃ … ⦄ public

-- module _ where

--   record Successor₀ {x} (X : Ø x) : Ø x where
--     field
--       ⇑₀ : X → X
--   open Successor₀ ⦃ … ⦄ public

--   record Principal₁ {x} {X : Ø x} {a} (A : X → Ø a) : Ø₀ where no-eta-equality
--   record Principal₁₊₁ {x} {X : Ø x} {a} (A : X → Ø a) {b} (B : X → Ø b) : Ø₀ where no-eta-equality

--   record Successor₁ {x} {X : Ø x} {a} (A : X → Ø a)
--     ⦃ _ : Successor₀ X ⦄
--     ⦃ _ : Principal₁ A ⦄
--     : Ø x ∙̂ a where
--     field
--       ⇑₁ : ∀ {m} → A m → A (⇑₀ m)
--   open Successor₁ ⦃ … ⦄ public

--   record Thin {x} {X : Ø x} {a} (A : X → Ø a) {b} (B : X → Ø b)
--     ⦃ _ : Successor₀ X ⦄
--     ⦃ _ : Principal₁ A ⦄
--     ⦃ _ : Principal₁ B ⦄
--     : Ø x ∙̂ a ∙̂ b where
--     field
--       thin : ∀ {m : X} → A (⇑₀ m) → B m → B (⇑₀ m)
--   open Thin ⦃ … ⦄ public

--   thin[_] : ∀
--     {x} {X : Ø x} {a} {A : X → Ø a} {b} (B : X → Ø b)
--     ⦃ _ : Successor₀ X ⦄
--     ⦃ _ : Principal₁ A ⦄
--     ⦃ _ : Principal₁ B ⦄
--     ⦃ _ : Thin A B ⦄
--     → ∀ {m : X} → A (⇑₀ m) → B m → B (⇑₀ m)
--   thin[ _ ] = thin

--   record Injectivity₀
--     {a} {A : Ø a}
--     {b} {B : Ø b}
--     (f : A → B)
--     ℓa
--     ℓb
--     ⦃ _ : Equivalence B ℓb ⦄
--     ⦃ _ : Equivalence A ℓa ⦄
--     : Ø a ∙̂ b ∙̂ ℓa ∙̂ ℓb where
--     field injectivity₀ : ∀ {x y} → f x ≋ f y → x ≋ y
--   open Injectivity₀ ⦃ … ⦄ public

--   injectivity₀[_] : ∀
--     {a} {A : Ø a}
--     {b} {B : Ø b}
--     (f : A → B)
--     {ℓa}
--     {ℓb}
--     ⦃ _ : Equivalence A ℓa ⦄
--     ⦃ _ : Equivalence B ℓb ⦄
--     ⦃ _ : Injectivity₀ f ℓa ℓb ⦄
--     → ∀ {x y} → f x ≋ f y → x ≋ y
--   injectivity₀[ f ] = injectivity₀ { f = f }

--   record Injectivity!
--     {a} {A : Ø a}
--     {b} {B : A → Ø b}
--     {c} (C : ∀ x → B x → B x → Ø c)
--     {d} (D : ∀ x → B x → B x → Ø d)
--     : Ø a ∙̂ b ∙̂ c ∙̂ d where
--     field injectivity! : ∀ w {x y : B w} → C w x y → D w x y
--   open Injectivity! ⦃ … ⦄ public

--   module _
--     {a} {A : Ø a}
--     {b} {B : A → Ø b}
--     {c} {C : A → Ø c}
--     (f : (x : A) → B x → C x)
--     ℓb
--     ℓc
--     ⦃ _ : ∀ {x} → Equivalence (B x) ℓb ⦄
--     ⦃ _ : ∀ {x} → Equivalence (C x) ℓc ⦄
--     where
--     Injectivity? = Injectivity! (λ w x y → f w x ≋ f w y) (λ w x y → x ≋ y)

--   injectivity?[_] : ∀
--     {a} {A : Ø a}
--     {b} {B : A → Ø b}
--     {c} {C : A → Ø c}
--     (f : (x : A) → B x → C x)
--     {ℓb}
--     {ℓc}
--     ⦃ _ : ∀ {x} → Equivalence (B x) ℓb ⦄
--     ⦃ _ : ∀ {x} → Equivalence (C x) ℓc ⦄
--     ⦃ _ : Injectivity? f ℓb ℓc ⦄
--     → ∀ w {x y} → f w x ≋ f w y → x ≋ y
--   injectivity?[ _ ] = injectivity!

--   record Injectivity₁
--     {a} {A : Ø a}
--     {b} {B : A → Ø b}
--     {c} {C : A → Ø c}
--     (f : (x : A) → B x → C x)
--     ℓb
--     ℓc
--     ⦃ _ : ∀ {x} → Equivalence (B x) ℓb ⦄
--     ⦃ _ : ∀ {x} → Equivalence (C x) ℓc ⦄
--     : Ø a ∙̂ b ∙̂ ℓb ∙̂ ℓc where
--     field injectivity₁ : ∀ w {x y} → f w x ≋ f w y → x ≋ y
--   open Injectivity₁ ⦃ … ⦄ public

--   injectivity₁[_] : ∀
--     {a} {A : Ø a}
--     {b} {B : A → Ø b}
--     {c} {C : A → Ø c}
--     (f : (x : A) → B x → C x)
--     {ℓb}
--     {ℓc}
--     ⦃ _ : ∀ {x} → Equivalence (B x) ℓb ⦄
--     ⦃ _ : ∀ {x} → Equivalence (C x) ℓc ⦄
--     ⦃ _ : Injectivity₁ f ℓb ℓc ⦄
--     → ∀ w {x y} → f w x ≋ f w y → x ≋ y
--   injectivity₁[ f ] = injectivity₁ {f = f}

--   record Injectivity₂
--     {a} {A : Ø a}
--     {b} {B : Ø b}
--     {c} {C : Ø c}
--     (f : A → B → C)
--     ℓb
--     ℓc
--     ⦃ _ : Equivalence B ℓb ⦄
--     ⦃ _ : Equivalence C ℓc ⦄
--     : Ø a ∙̂ b ∙̂ ℓb ∙̂ ℓc where
--     field injectivity₂ : ∀ w {x y} → f w x ≋ f w y → x ≋ y
--   open Injectivity₂ ⦃ … ⦄ public

--   injectivity₂[_] : ∀
--     {a} {A : Ø a}
--     {b} {B : Ø b}
--     {c} {C : Ø c}
--     (f : A → B → C)
--     {ℓb}
--     {ℓc}
--     ⦃ _ : Equivalence B ℓb ⦄
--     ⦃ _ : Equivalence C ℓc ⦄
--     ⦃ _ : Injectivity₂ f ℓb ℓc ⦄
--     → ∀ w {x y} → f w x ≋ f w y → x ≋ y
--   injectivity₂[ f ] = injectivity₂ {f = f}

--   record ThinInjective {x} {X : Ø x} {a} (A : X → Ø a) {b} (B : X → Ø b) c
--     ⦃ _ : Successor₀ X ⦄
--     ⦃ _ : ∀ {x} → Equivalence (B x) c ⦄
--     ⦃ _ : Principal₁ A ⦄
--     ⦃ _ : Principal₁ B ⦄
--     ⦃ _ : Thin A B ⦄
--     : Ø x ∙̂ a ∙̂ b ∙̂ ↑̂ c where
--     field
--       ⦃ ⌶Injectivity₁ ⦄ : ∀ {m : X} → Injectivity₁ {A = A (⇑₀ m)} {B = λ _ → B _} (λ w x → thin w x) c c
--       ⦃ ⌶Injectivity₂ ⦄ : ∀ {m : X} → Injectivity₂ (λ (w : A (⇑₀ m)) x → thin[ B ] w x) c c
--       -- (thin[ B ] {m = m})
--     thin-injective : ∀ {m : X} (x : A (⇑₀ m)) {y₁ y₂ : B m} → thin x y₁ ≋ thin x y₂ → y₁ ≋ y₂
--     thin-injective = injectivity₁[ thin ]
--     -- injectivity₂[ thin[ B ] ]
--     -- injectivity₁[ thin ]
--   open ThinInjective ⦃ … ⦄ public

--   record Thick {x} {X : Ø x} {a} (A : X → Ø a) {b} (B : X → Ø b)
--     ⦃ _ : Successor₀ X ⦄
--     ⦃ _ : Principal₁ B ⦄
--     : Ø x ∙̂ a ∙̂ b where
--     field
--       thick : ∀ {m} → B (⇑₀ m) → A m → B m
--   open Thick ⦃ … ⦄ public

--   record ThickThinId {x} {X : Ø x} {a} (A : X → Ø a) {b} (B : X → Ø b) c
--     ⦃ _ : Successor₀ X ⦄
--     ⦃ _ : Principal₁ A ⦄
--     ⦃ _ : Principal₁ B ⦄
--     ⦃ _ : Successor₁ A ⦄
--     ⦃ _ : ∀ {x} → Equivalence (B x) c ⦄
--     ⦃ _ : Thin A B ⦄
--     ⦃ _ : Thick A B ⦄
--     : Ø x ∙̂ a ∙̂ b ∙̂ ↑̂ c where
--     field
--       thick∘thin=id : ∀ {m} (x : A m) (y : B m) → thick (thin (⇑₁ x) y) x ≋ y
--   open ThickThinId ⦃ … ⦄ public

--   record Maybe* a : Ø ↑̂ a where
--     field
--       Maybe : Ø a → Ø a
--       just : ∀ {A} → A → Maybe A
--       nothing : ∀ {A} → Maybe A
--   open Maybe* ⦃ … ⦄ -- public

--   record Check {x} {X : Ø x} {a} (A : X → Ø a) {b} (B : X → Ø b)
--     ⦃ _ : Successor₀ X ⦄
--     ⦃ _ : Principal₁ A ⦄
--     ⦃ _ : Principal₁ B ⦄
--     ⦃ _ : Maybe* b ⦄
--     : Ø x ∙̂ a ∙̂ ↑̂ b where
--     field
--       check : ∀ {m} → A (⇑₀ m) → B (⇑₀ m) → Maybe (B m)
--   open Check ⦃ … ⦄ public

--   record ThinCheckId {x} {X : Ø x} {a} (A : X → Ø a) {b} (B : X → Ø b) ℓb ℓc
--     ⦃ _ : Successor₀ X ⦄
--     ⦃ _ : Maybe* b ⦄
--     ⦃ _ : ∀ {x} → Equivalence (B x) ℓb ⦄
--     ⦃ _ : ∀ {x} → Equivalence (Maybe (B x)) ℓc ⦄
--     ⦃ _ : Principal₁ A ⦄
--     ⦃ _ : Principal₁ B ⦄
--     ⦃ _ : Thin A B ⦄
--     ⦃ _ : Check A B ⦄
--     : Ø x ∙̂ a ∙̂ b ∙̂ ℓb ∙̂ ℓc where
--     field
--       thin-check-id : ∀ {m} (x : A (⇑₀ m)) y → ∀ (y' : B m) → thin x y' ≋ y → check x y ≋ just y'
--   open ThinCheckId ⦃ … ⦄ public

--   test-thin-check-id : ∀ {x} {X : Ø x} {a} (A : X → Ø a) {b} (B : X → Ø b) ℓb ℓc
--                          ⦃ _ : Successor₀ X ⦄
--                          ⦃ _ : ∀ {x} → Equivalence (B x) ℓb ⦄
--                          ⦃ _ : Maybe* b ⦄
--                          ⦃ _ : ∀ {x} → Equivalence (Maybe (B x)) ℓc ⦄
--                          ⦃ _ : Principal₁ A ⦄
--                          ⦃ _ : Principal₁ B ⦄
--                          ⦃ _ : Thin A B ⦄
--                          ⦃ _ : Check A B ⦄
--                          ⦃ _ : ThinCheckId A B ℓb ℓc ⦄
--                          → ∀ {m} (x : A (⇑₀ m)) y → ∀ (y' : B m) → thin x y' ≋ y → check x y ≋ just y'
--   test-thin-check-id A B ℓb ℓc = thin-check-id

--   record ThickAndThin {x} {X : Ø x} {a} (A : X → Ø a) {b} (B : X → Ø b) c ℓc
--     ⦃ _ : Successor₀ X ⦄
--     ⦃ _ : Principal₁ A ⦄
--     ⦃ _ : Principal₁ B ⦄
--     ⦃ _ : Successor₁ A ⦄
--     ⦃ _ : Maybe* b ⦄
--     ⦃ _ : ∀ {x} → Equivalence (B x) c ⦄
--     ⦃ _ : ∀ {x} → Equivalence (Maybe (B x)) ℓc ⦄
--     : Ø x ∙̂ a ∙̂ ↑̂ b ∙̂ ↑̂ c ∙̂ ↑̂ ℓc where
--     field
--       ⦃ iThin ⦄ : Thin A B
--       ⦃ iThinInjective ⦄ : ThinInjective A B c
--       ⦃ iThick ⦄ : Thick A B
--       ⦃ iThickThinId ⦄ : ThickThinId A B c
--       ⦃ iCheck ⦄ : Check A B
--       ⦃ iThinCheckId ⦄ : ThinCheckId A B c ℓc
--   open ThickAndThin ⦃ … ⦄

-- module _ where

--   record FMap {x} {y} (F : Ø x → Ø y) : Ø (↑̂ x) ∙̂ y where
--     field fmap : ∀ {A B : Ø x} → (A → B) → F A → F B
