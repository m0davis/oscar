{-# OPTIONS --show-implicit #-}
{-# OPTIONS --postfix-projections #-}
module Oscar.Class where

open import Oscar.Prelude

open import Oscar.Data using (_≡_; ∅)

transport : ∀ {a b} {A : Set a} (B : A → Set b) {x y} → x ≡ y → B x → B y
transport _ ∅ = ¡

{-
transport₂ : ∀ {a b c} {A : Set a} {B : Set b} (C : A → B → Set c) {x₁ x₂ y₁ y₂} → x₁ ≡ x₂ → y₁ ≡ y₂ → C x₁ y₁ → C x₂ y₂
transport₂ C refl refl cxy = cxy
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

  test-reflexivity : ∀
    {a} {A : Ø a}
    {b} {_⊸1_ : A → A → Ø b}
        {_⊸2_ : A → A → Ø b}
    ⦃ _ : IsReflexive _⊸1_ ⦄
    ⦃ _ : IsReflexive _⊸2_ ⦄
    → ∀ {x} → x ⊸1 x
  test-reflexivity = reflexivity

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
    where
    module _
      (μ : A₁ → A₂)
      where
      𝓶ap = ∀ {x y} → x ⊸₁ y → μ x ⊸₂ μ y
    record IsMappable : Ø a₁ ∙̂ m₁ ∙̂ a₂ ∙̂ m₂ where
      field
        μ : A₁ → A₂
        map : 𝓶ap μ
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
    module _
      (isMappable : IsMappable _⊸₁_ _⊸₂_)
      where
      𝓶apextensionality' =
        let instance _ = isMappable
        in
        𝓶apextensionality map

    record IsMapextensional : Ø a₁ ∙̂ m₁ ∙̂ a₂ ∙̂ m₂ ∙̂ ℓ₁ ∙̂ ℓ₂ where
      field
        ⦃ isMappable ⦄ : IsMappable _⊸₁_ _⊸₂_
        mapextensionality : 𝓶apextensionality' !

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
    {ℓ} (ArrowEquivalent : ∀ {x y} → Arrow x y → Arrow x y → Ø ℓ)
    : Ø o ∙̂ a ∙̂ ℓ where
    field
      isReflexive : IsReflexive Arrow
      isTransitive : IsTransitive Arrow
      transleftidentity :
        let instance
              _ = isReflexive
              _ = isTransitive
        in
--        asInstance isReflexive $
--        asInstance isTransitive $
        ∀ {x y} {f : Arrow x y} → ArrowEquivalent (ε ∙ f) f

  open IsTransleftidentity ⦃ … ⦄ using (transleftidentity)

module _ where

  record IsTransrightidentity
    {o} {Object : Ø o}
    {a} (Arrow : Object → Object → Ø a)
    {ℓ} (ArrowEquivalent : ∀ {x y} → Arrow x y → Arrow x y → Ø ℓ)
    : Ø o ∙̂ a ∙̂ ℓ where
    field
      isReflexive : IsReflexive Arrow
      isTransitive : IsTransitive Arrow
      transrightidentity :
        asInstance isReflexive $
        asInstance isTransitive $
        ∀ {x y} {f : Arrow x y} → ArrowEquivalent (f ∙ ε) f

  open IsTransrightidentity ⦃ … ⦄ using (transrightidentity)

module _ where

  record IsMapidentity
    {o₁} {Object₁ : Ø o₁}
    {a₁} (Arrow₁ : Object₁ → Object₁ → Ø a₁)
    {o₂} {Object₂ : Ø o₂}
    {a₂} (Arrow₂ : Object₂ → Object₂ → Ø a₂)
    {ℓ₂} (ArrowEquivalent₂ : ∀ {x y} → Arrow₂ x y → Arrow₂ x y → Ø ℓ₂)
    : Ø o₁ ∙̂ a₁ ∙̂ o₂ ∙̂ a₂ ∙̂ ℓ₂ where
    field
      isMappable : IsMappable Arrow₁ Arrow₂
      isReflexive₁ : IsReflexive Arrow₁
      isReflexive₂ : IsReflexive Arrow₂
      mapidentity :
        asInstance isMappable $
        asInstance isReflexive₁ $
        asInstance isReflexive₂ $
        ∀ {x} → ArrowEquivalent₂ (map (ε[ Arrow₁ ] {x})) ε

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

  record HasEquivalence {o} (Object : Ø o) ℓ : Ø o ∙̂ ↑̂ ℓ where
    field
      Equivalent : Object → Object → Ø ℓ
      isEquivalence : IsEquivalence Equivalent

  record Setoid o ℓ : Ø ↑̂ (o ∙̂ ℓ) where
    field
      Object : Ø o
      hasEquivalence : HasEquivalence Object ℓ
    open HasEquivalence hasEquivalence public

module _ where

  module _ where

    infix 4 _≈_
    _≈_ : ∀ {o} {Object : Ø o} {ℓ} ⦃ _ : HasEquivalence Object ℓ ⦄ → Object → Object → Ø ℓ
    _≈_ = HasEquivalence.Equivalent !

module _ where

  record IsPrecategory
    {o} {Object : Ø o}
    {a} (Arrow : Object → Object → Ø a)
    {ℓ} (ArrowEquivalent : ∀ {x y} → Arrow x y → Arrow x y → Ø ℓ)
    : Ø o ∙̂ a ∙̂ ℓ where
    field
      isEquivalence : ∀ {x y} → IsEquivalence (ArrowEquivalent {x} {y})
      isTransextensional : IsTransextensional Arrow ArrowEquivalent
      isTransassociative : IsTransassociative Arrow ArrowEquivalent
      isTransitive/isTransassociative≡isTransextensional : isTransassociative .IsTransassociative.isTransitive ≡ isTransextensional .IsTransextensional.isTransitive
    open IsTransextensional isTransextensional using (isTransitive) public

  record IsPrefunctor
    {o₁} {Object₁ : Ø o₁}
    {a₁} (Arrow₁ : Object₁ → Object₁ → Ø a₁)
    {ℓ₁} (ArrowEquivalent₁ : ∀ {x y} → Arrow₁ x y → Arrow₁ x y → Ø ℓ₁)
    {o₂} {Object₂ : Ø o₂}
    {a₂} (Arrow₂ : Object₂ → Object₂ → Ø a₂)
    {ℓ₂} (ArrowEquivalent₂ : ∀ {x y} → Arrow₂ x y → Arrow₂ x y → Ø ℓ₂)
    : Ø o₁ ∙̂ a₁ ∙̂ ℓ₁ ∙̂ o₂ ∙̂ a₂ ∙̂ ℓ₂ where
    field
      isPrecategory₁ : IsPrecategory Arrow₁ ArrowEquivalent₁
      isPrecategory₂ : IsPrecategory Arrow₂ ArrowEquivalent₂
      isMapextensional      : IsMapextensional Arrow₁ ArrowEquivalent₁ Arrow₂ ArrowEquivalent₂
      isMaptranscommutative : IsMaptranscommutative Arrow₁ Arrow₂ ArrowEquivalent₂
      isMappable/isMapextensional≡isMaptranscommutative : isMapextensional .IsMapextensional.isMappable ≡ isMaptranscommutative .IsMaptranscommutative.isMappable
      isTransitive₁/isMaptranscommutative≡isPrecategory₁ : isMaptranscommutative .IsMaptranscommutative.isTransitive₁ ≡ isPrecategory₁ .IsPrecategory.isTransitive
      isTransitive₂/isMaptranscommutative≡isPrecategory₂ : isMaptranscommutative .IsMaptranscommutative.isTransitive₂ ≡ isPrecategory₂ .IsPrecategory.isTransitive
    open IsMapextensional isMapextensional using (isMappable) public

  record IsCategory
    {o} {Object : Ø o}
    {a} (Arrow : Object → Object → Ø a)
    {ℓ} (ArrowEquivalent : ∀ {x y} → Arrow x y → Arrow x y → Ø ℓ)
    : Ø o ∙̂ a ∙̂ ℓ where
    field
      isPrecategory        : IsPrecategory Arrow ArrowEquivalent
      isTransleftidentity  : IsTransleftidentity Arrow ArrowEquivalent
      isTransrightidentity : IsTransrightidentity Arrow ArrowEquivalent
      isTransitive/isTransleftidentity≡isPrecategory  : isTransleftidentity  .IsTransleftidentity.isTransitive  ≡ isPrecategory .IsPrecategory.isTransitive
      isTransitive/isTransrightidentity≡isPrecategory : isTransrightidentity .IsTransrightidentity.isTransitive ≡ isPrecategory .IsPrecategory.isTransitive
      isReflexive/isTransrightidentity≡isTransleftidentity : isTransrightidentity .IsTransrightidentity.isReflexive ≡ isTransleftidentity .IsTransleftidentity.isReflexive
    open IsPrecategory isPrecategory public
    open IsTransleftidentity isTransleftidentity using (isReflexive) public

  record IsFunctor
    {o₁} {Object₁ : Ø o₁}
    {a₁} (Arrow₁ : Object₁ → Object₁ → Ø a₁)
    {ℓ₁} (ArrowEquivalent₁ : ∀ {x y} → Arrow₁ x y → Arrow₁ x y → Ø ℓ₁)
    {o₂} {Object₂ : Ø o₂}
    {a₂} (Arrow₂ : Object₂ → Object₂ → Ø a₂)
    {ℓ₂} (ArrowEquivalent₂ : ∀ {x y} → Arrow₂ x y → Arrow₂ x y → Ø ℓ₂)
    : Ø o₁ ∙̂ a₁ ∙̂ ℓ₁ ∙̂ o₂ ∙̂ a₂ ∙̂ ℓ₂ where
    field
      isCategory₁   : IsCategory Arrow₁ ArrowEquivalent₁
      isCategory₂   : IsCategory Arrow₂ ArrowEquivalent₂
      isPrefunctor  : IsPrefunctor Arrow₁ ArrowEquivalent₁ Arrow₂ ArrowEquivalent₂
      isMapidentity : IsMapidentity Arrow₁ Arrow₂ ArrowEquivalent₂
      isPrecategory₁/isPrefunctor≡isCategory₁ : isPrefunctor .IsPrefunctor.isPrecategory₁ ≡ isCategory₁ .IsCategory.isPrecategory
      isPrecategory₂/isPrefunctor≡isCategory₂ : isPrefunctor .IsPrefunctor.isPrecategory₂ ≡ isCategory₂ .IsCategory.isPrecategory
      isMappable/isMapidentity≡isPrefunctor  : isMapidentity .IsMapidentity.isMappable ≡ isPrefunctor .IsPrefunctor.isMappable
      isReflexive₁/isMapidentity≡isCategory₁ : isMapidentity .IsMapidentity.isReflexive₁ ≡ isCategory₁ .IsCategory.isReflexive
      isReflexive₂/isMapidentity≡isCategory₂ : isMapidentity .IsMapidentity.isReflexive₂ ≡ isCategory₂ .IsCategory.isReflexive

module _ where

  record Precategory o a ℓ : Ø ↑̂ (o ∙̂ a ∙̂ ℓ) where
    field
      Object : Ø o
      Arrow : Object → Object → Ø a
      ArrowEquivalent : ∀ {x y} → Arrow x y → Arrow x y → Ø ℓ
      isPrecategory : IsPrecategory Arrow ArrowEquivalent

  record Prefunctor o₁ a₁ ℓ₁ o₂ a₂ ℓ₂ : Ø ↑̂ (o₁ ∙̂ a₁ ∙̂ ℓ₁ ∙̂ o₂ ∙̂ a₂ ∙̂ ℓ₂) where
    field
      Object₁ : Ø o₁
      Arrow₁ : Object₁ → Object₁ → Ø a₁
      ArrowEquivalent₁ : ∀ {x y} → Arrow₁ x y → Arrow₁ x y → Ø ℓ₁
      Object₂ : Ø o₂
      Arrow₂ : Object₂ → Object₂ → Ø a₂
      ArrowEquivalent₂ : ∀ {x y} → Arrow₂ x y → Arrow₂ x y → Ø ℓ₂
      isPrefunctor : IsPrefunctor Arrow₁ ArrowEquivalent₁ Arrow₂ ArrowEquivalent₂

  record Category o a ℓ : Ø ↑̂ (o ∙̂ a ∙̂ ℓ) where
    field
      Object : Ø o
      Arrow : Object → Object → Ø a
      ArrowEquivalent : ∀ {x y} → Arrow x y → Arrow x y → Ø ℓ
      isCategory : IsCategory Arrow ArrowEquivalent

  record Functor o₁ a₁ ℓ₁ o₂ a₂ ℓ₂ : Ø ↑̂ (o₁ ∙̂ a₁ ∙̂ ℓ₁ ∙̂ o₂ ∙̂ a₂ ∙̂ ℓ₂) where
    field
      Object₁ : Ø o₁
      Arrow₁ : Object₁ → Object₁ → Ø a₁
      ArrowEquivalent₁ : ∀ {x y} → Arrow₁ x y → Arrow₁ x y → Ø ℓ₁
      Object₂ : Ø o₂
      Arrow₂ : Object₂ → Object₂ → Ø a₂
      ArrowEquivalent₂ : ∀ {x y} → Arrow₂ x y → Arrow₂ x y → Ø ℓ₂
      isFunctor : IsFunctor Arrow₁ ArrowEquivalent₁ Arrow₂ ArrowEquivalent₂


module _ where

  module _
    {a} {A : Ø a}
    {m} (_⊸_ : A → A → Ø m)
    {ℓ} ⦃ _ : ∀ {x y} → HasEquivalence (x ⊸ y) ℓ ⦄
    where
    module _
      ⦃ _ : IsTransitive _⊸_ ⦄
      where
      𝓽ransextensionality! = 𝓽ransextensionality _⊸_ _≈_ transitivity
    IsTransextensional! = IsTransextensional _⊸_ _≈_

  module _
    {a₁} {A₁ : Ø a₁}
    {m₁} (_⊸₁_ : A₁ → A₁ → Ø m₁)
    {ℓ₁} ⦃ _ : ∀ {x y} → HasEquivalence (x ⊸₁ y) ℓ₁ ⦄
    {a₂} {A₂ : Ø a₂}
    {m₂} (_⊸₂_ : A₂ → A₂ → Ø m₂)
    {ℓ₂} ⦃ _ : ∀ {x y} → HasEquivalence (x ⊸₂ y) ℓ₂ ⦄
    where
    module _
      ⦃ _ : IsMappable _⊸₁_ _⊸₂_ ⦄
      where
      𝓶apextensionality! = 𝓶apextensionality _⊸₁_ _≈_ _⊸₂_ _≈_ map
    IsMapextensional! = IsMapextensional _⊸₁_ _≈_ _⊸₂_ _≈_

  module _
    {a₁} {A₁ : Ø a₁}
    {m₁} (_⊸₁_ : A₁ → A₁ → Ø m₁)
    {a₂} {A₂ : Ø a₂}
    {m₂} (_⊸₂_ : A₂ → A₂ → Ø m₂)
    {ℓ₂} ⦃ _ : ∀ {x y} → HasEquivalence (x ⊸₂ y) ℓ₂ ⦄
    where
    module _
      ⦃ isMappable : IsMappable _⊸₁_ _⊸₂_ ⦄
      ⦃ isTransitive₁ : IsTransitive _⊸₁_ ⦄
      ⦃ isTransitive₂ : IsTransitive _⊸₂_ ⦄
      where
      𝓶aptranscommutativity! = 𝓶aptranscommutativity _⊸₁_ _⊸₂_ _≈_ map transitivity transitivity
    IsMaptranscommutative! = IsMaptranscommutative _⊸₁_ _⊸₂_ _≈_











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

open import Oscar.Data

module _ where

  module _ {𝔬} {𝔒 : Ø 𝔬} where

    instance

      IsReflexiveProposequality : IsReflexive Proposequality⟦ 𝔒 ⟧
      IsReflexiveProposequality .IsReflexive.reflexivity = !

      IsSymmetricProposequality : IsSymmetric Proposequality⟦ 𝔒 ⟧
      IsSymmetricProposequality .IsSymmetric.symmetry ∅ = !

      IsTransitiveProposequality : IsTransitive Proposequality⟦ 𝔒 ⟧
      IsTransitiveProposequality .IsTransitive.transitivity ∅ = ¡

      IsEquivalenceProposequality : IsEquivalence Proposequality⟦ 𝔒 ⟧
      IsEquivalenceProposequality .IsEquivalence.isReflexive = !
      IsEquivalenceProposequality .IsEquivalence.isSymmetric = !
      IsEquivalenceProposequality .IsEquivalence.isTransitive = !



module _ where

  module _
    {x} (X : Ø x)
    where
    𝓼uccessor₀ = X → X
    record Successor₀ : Ø x where
      field
        successor₀ : 𝓼uccessor₀
    open Successor₀ ⦃ … ⦄ public

  ⇑₀ = successor₀

  module _
    {x} {X : Ø x} {a} (A : X → Ø a)
    where
    module _ (successor₀ : 𝓼uccessor₀ X) where
      𝓼uccessor₁ = ∀ {m} → A m → A (successor₀ m)
    module _ (⌶Successor₀ : Successor₀ X) where
      𝓼uccessor₁' =
        let instance _ = ⌶Successor₀
        in
        𝓼uccessor₁ successor₀
    record Successor₁ : Ø x ∙̂ a where
      field
        --successor₀ : 𝓼uccessor₀ X
        ⦃ isSuccessor₀ ⦄ : Successor₀ X
        successor₁ :
          -- asInstance isSuccessor₀ $
          -- 𝓼uccessor₁ successor₀
          𝓼uccessor₁' !
    open Successor₁ ⦃ … ⦄ public using (successor₁)

  module _
    {a} (A : Ø a)
    {b} (B : Ø b)
    {ℓa} (_≈A_ : A → A → Ø ℓa)
    {ℓb} (_≈B_ : B → B → Ø ℓb)
    where
    module _
      (f : A → B)
      where
      𝓲njectivity = ∀ {x y} → f x ≈B f y → x ≈A y
    record Injectivity : Ø a ∙̂ b ∙̂ ℓa ∙̂ ℓb where
      field
        f : A → B
        injectivity : 𝓲njectivity f
    open Injectivity ⦃ … ⦄ public using (injectivity)

  module _
    {x} {X : Ø x} {a} (A : X → Ø a) {b} (B : X → Ø b)
    where
    module _ (⇑₀ : 𝓼uccessor₀ X) where
      𝓉hin = ∀ {m : X} → A (⇑₀ m) → B m → B (⇑₀ m)
    module _ (isSuccessor₀ : Successor₀ X) where
      𝓽hin =
        let instance _ = isSuccessor₀
        in
        ∀ {m : X} → A (⇑₀ m) → B m → B (⇑₀ m)
--        𝓉hin successor₀
    module _ ⦃ isSuccessor₀ : Successor₀ X ⦄ where
      𝓽hin! = 𝓉hin successor₀
    record Thin! ⦃ _ : Successor₀ X ⦄ : Ø x ∙̂ a ∙̂ b where
      field
        𝓣hin : 𝓽hin!
    record Thin : Ø x ∙̂ a ∙̂ b where
      field
        ⦃ isSuccessor₀ ⦄ : Successor₀ X
        ⦃ ⌶Thin! ⦄ : Thin!
--      thin : 𝓽hin !
      open Thin! ⌶Thin! public renaming (𝓣hin to thin)
      -- thin = Thin!.𝓣hin ⌶Thin!


--  open Thin! ⦃ … ⦄
  open Thin ⦃ … ⦄ public using (thin)

  !Thin : ∀ {x} {X : Ø x} {a} {A : X → Ø a} {b} {B : X → Ø b} ⦃ _ : Successor₀ X ⦄ ⦃ _ : Thin! A B ⦄ → Thin A B
  !Thin = record {}

  module Test where
    postulate
      X : Set
      A : X → Set
      B : X → Set
      instance _ : Successor₀ X
      instance _ : Thin! A B
    instance _ : Thin A B
    _ = !Thin
    test-thin : ∀ {m : X} → A (⇑₀ m) → B m → B (⇑₀ m)
    test-thin = thin

--  thin! : ∀ {x} {X : Ø x} {a} {A : X → Ø a} {b} {B : X → Ø b} ⦃ _ : Successor₀ X ⦄ ⦃ _ : Thin! A B ⦄
--    → ∀ {m : X} → A (⇑₀ m) → B m → B (⇑₀ m)
--  thin! ⦃ x ⦄ ⦃ y ⦄ = let instance ⌶ = Thin!.⌶Thin y in thin




  module _
    {x} {X : Ø x} {a} (A : X → Ø a) {b} (B : X → Ø b)
    where

    module _ (⇑₀ : 𝓼uccessor₀ X) where
      𝓉hick = ∀ {m} → B (⇑₀ m) → A m → B m

    module _ (isSuccessor₀ : Successor₀ X) where
      𝓽hick =
        let instance _ = isSuccessor₀
        in
        𝓉hick successor₀

    record Thick : Ø x ∙̂ a ∙̂ b where
      field
        ⦃ isSuccessor₀ ⦄ : Successor₀ X
        thick : 𝓽hick !

    open Thick ⦃ … ⦄ public using (thick)

  module _
    {x} {X : Ø x} {a} (A : X → Ø a) {b} (B : X → Ø b) {ℓ} (_≈_ : ∀ {x} → B x → B x → Ø ℓ)
    where
    module _
      {successor₀ : 𝓼uccessor₀ X}
      (successor₁ : 𝓼uccessor₁ A successor₀)
      (thin : 𝓉hin A B successor₀)
      (thick : 𝓉hick A B successor₀)
      where
      𝓉hick∘thin=id = ∀ {m} (x : A m) (y : B m) → thick (thin (successor₁ x) y) x ≈ y
    module _
      (isSuccessor₁ : Successor₁ A)
      (isThin : Thin A B)
      (isThick : Thick A B)
      (=2 : isThin .Thin.isSuccessor₀ ≡ isSuccessor₁ .Successor₁.isSuccessor₀)
      (=3 : isThick .Thick.isSuccessor₀ ≡ isSuccessor₁ .Successor₁.isSuccessor₀)
      where
      𝓽hick∘thin=id =
        let instance _ = isSuccessor₁
                     _ = isThin
                     _ = isThick
        in
        𝓉hick∘thin=id
          successor₁
          (transport (𝓽hin A B) =2 thin)
          (transport (𝓽hick A B) =3 thick)
    module _
      ⦃ isSuccessor₁ : Successor₁ A ⦄
      ⦃ isThin : Thin A B ⦄
      ⦃ isThick : Thick A B ⦄
      ⦃ =2 : isThin .Thin.isSuccessor₀ ≡ isSuccessor₁ .Successor₁.isSuccessor₀ ⦄
      ⦃ =3 : isThick .Thick.isSuccessor₀ ≡ isSuccessor₁ .Successor₁.isSuccessor₀ ⦄
      where
      𝓽hick∘thin=id! =
        𝓉hick∘thin=id
          successor₁
          (transport (𝓽hin A B) =2 thin)
          (transport (𝓽hick A B) =3 thick)
--     record ThickThinId!
--       ⦃ isSuccessor₁ : Successor₁ A ⦄
--       ⦃ isThin : Thin! A B ⦄
--       ⦃ _ : Thick A B ⦄
--       ⦃ _ : isThin .Thin.isSuccessor₀ ≡ isSuccessor₁ .Successor₁.isSuccessor₀ ⦄
--       ⦃ _ : isThick .Thick.isSuccessor₀ ≡ isSuccessor₁ .Successor₁.isSuccessor₀ ⦄
--       : Ø x ∙̂ a ∙̂ b ∙̂ ℓ where
--       field

--         thick∘thin=id : 𝓽hick∘thin=id!
--     record ThickThinId  : Ø x ∙̂ a ∙̂ b ∙̂ ℓ where
--       field
--         ⦃ isSuccessor₁ ⦄ : Successor₁ A
--         ⦃ isThin! ⦄ : Thin! A B
--         ⦃ isThin       ⦄ : Thin A B
--         ⦃ isThick      ⦄ : Thick A B
--         ⦃ =2           ⦄ : isThin .Thin.isSuccessor₀ ≡ isSuccessor₁ .Successor₁.isSuccessor₀
--         ⦃ =3           ⦄ : isThick .Thick.isSuccessor₀ ≡ isSuccessor₁ .Successor₁.isSuccessor₀
--         thick∘thin=id : 𝓽hick∘thin=id!
--         --𝓽hick∘thin=id ! ! ! ! !

--   module _
--     {x} {X : Ø x} {a} (A : X → Ø a) {b} (B : X → Ø b)
--     where
--     module _
--       (successor₀ : 𝓼uccessor₀ X)
--       {e}
--       (∃? : Ø b → Ø e)
--       where
--       𝓬heck = ∀ {m} → A (successor₀ m) → B (successor₀ m) → ∃? (B m)
--     record Check : Ø x ∙̂ a ∙̂ ↑̂ b where
--       field
--         successor₀ : 𝓼uccessor₀ X
--         ∃? : Ø b → Ø b
--         check : 𝓬heck successor₀ Maybe

--   module _
--     {x} {X : Ø x} {a} (A : X → Ø a) {b} (B : X → Ø b) {ℓb} (_≈B_ : ∀ {x} → B x → B x → Ø ℓb) {e} (∃? : Ø b → Ø e) {ℓ∃} (_≈E_ : ∀ {A : Ø b} → ∃? A → ∃? A → Ø ℓ∃)
--     where
--     module _
--       (successor₀ : 𝓼uccessor₀ X)
--       (thin : 𝓉hin A B successor₀)
--       (check : 𝓬heck A B successor₀ ∃?)
--       (just : ∀ {x} → B x → ∃? (B x))
--       where
--       𝓽hin-check-id = ∀ {m} (x : A (successor₀ m)) y → ∀ (y' : B m) → thin x y' ≈B y → check x y ≈E just y'
--     record ThinCheckId : Ø x ∙̂ a ∙̂ e ∙̂ ℓb ∙̂ b ∙̂ ℓ∃ where
--       field
--         successor₀ : 𝓼uccessor₀ X
--         thin : 𝓉hin A B successor₀
--         check : 𝓬heck A B successor₀ ∃?
--         just : ∀ {x} → B x → ∃? (B x)
--         thin-check-id : 𝓽hin-check-id successor₀ thin check just

--   record ThickAndThin x a b ℓb e ℓE : Ø ↑̂ (x ∙̂ a ∙̂ b ∙̂ ℓb ∙̂ e ∙̂ ℓE) where
--     field
--       X : Ø x
--       A : X → Ø a
--       B : X → Ø b
--       _≈B_ : ∀ {x} → B x → B x → Ø ℓb
--       ∃? : Ø b → Ø e
--       _≈E_ : ∀ {A : Ø b} → ∃? A → ∃? A → Ø ℓE
--       successor₀ : 𝓼uccessor₀ X
--       thin : 𝓉hin A B successor₀
--       check : 𝓬heck A B successor₀ ∃?
--       just : ∀ {x} → B x → ∃? (B x)
--       thick : 𝓉hick A B successor₀
--       successor₁ : 𝓼uccessor₁ A successor₀
--       injectivity : ∀ {m : X} {x : A (successor₀ m)} → 𝓲njectivity (B m) (B (successor₀ m)) _≈B_ _≈B_ (thin x)
--       thick∘thin=id : 𝓉hick∘thin=id A B _≈B_ successor₁ thin thick
--       thin-check-id : 𝓽hin-check-id A B _≈B_ ∃? _≈E_ successor₀ thin check just

-- --   open Successor₀ ⦃ … ⦄ using () renaming (successor₀ to ⇑₀)
-- --   open Thin ⦃ … ⦄ using (thin)

-- --   postulate
-- --     X : Set
-- --     A : X → Set
-- --     A' : X → Set
-- --     B : X → Set
-- --     ∃? : Set → Set
-- --     _≈B_ : ∀ {x} → B x → B x → Set
-- --     _≈E_ : ∀ {A : Set} → ∃? A → ∃? A → Set
-- --     _≈E'_ : ∀ {A : Set} → ∃? A → ∃? A → Set

-- --   instance
-- --     ⌶ThickAndThin : ThickAndThin _ _ _ _ _ _
-- --     ⌶ThickAndThin .ThickAndThin.X = X
-- --     ⌶ThickAndThin .ThickAndThin.A = A
-- --     ⌶ThickAndThin .ThickAndThin.B = B
-- --     ⌶ThickAndThin .ThickAndThin._≈B_ = _≈B_
-- --     ⌶ThickAndThin .ThickAndThin.∃? = ∃?
-- --     ⌶ThickAndThin .ThickAndThin._≈E_ = _≈E_
-- --     ⌶ThickAndThin .ThickAndThin.successor₀ = magic
-- --     ⌶ThickAndThin .ThickAndThin.thin = magic
-- --     ⌶ThickAndThin .ThickAndThin.check = magic
-- --     ⌶ThickAndThin .ThickAndThin.just = magic
-- --     ⌶ThickAndThin .ThickAndThin.thick = magic
-- --     ⌶ThickAndThin .ThickAndThin.successor₁ = magic
-- --     ⌶ThickAndThin .ThickAndThin.injectivity = magic
-- --     ⌶ThickAndThin .ThickAndThin.thick∘thin=id = magic
-- --     ⌶ThickAndThin .ThickAndThin.thin-check-id = magic

-- --     ⌶ThickAndThin' : ThickAndThin _ _ _ _ _ _
-- --     ⌶ThickAndThin' .ThickAndThin.X = X
-- --     ⌶ThickAndThin' .ThickAndThin.A = A'
-- --     ⌶ThickAndThin' .ThickAndThin.B = B
-- --     ⌶ThickAndThin' .ThickAndThin._≈B_ = _≈B_
-- --     ⌶ThickAndThin' .ThickAndThin.∃? = ∃?
-- --     ⌶ThickAndThin' .ThickAndThin._≈E_ = _≈E'_
-- --     ⌶ThickAndThin' .ThickAndThin.successor₀ = magic
-- --     ⌶ThickAndThin' .ThickAndThin.thin = magic
-- --     ⌶ThickAndThin' .ThickAndThin.check = magic
-- --     ⌶ThickAndThin' .ThickAndThin.just = magic
-- --     ⌶ThickAndThin' .ThickAndThin.thick = magic
-- --     ⌶ThickAndThin' .ThickAndThin.successor₁ = magic
-- --     ⌶ThickAndThin' .ThickAndThin.injectivity = magic
-- --     ⌶ThickAndThin' .ThickAndThin.thick∘thin=id = magic
-- --     ⌶ThickAndThin' .ThickAndThin.thin-check-id = magic

-- -- -- -- --   record FMap {x} {y} (F : Ø x → Ø y) : Ø (↑̂ x) ∙̂ y where
-- -- -- -- --     field fmap : ∀ {A B : Ø x} → (A → B) → F A → F B
