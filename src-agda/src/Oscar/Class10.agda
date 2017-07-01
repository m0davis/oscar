{-# OPTIONS --show-implicit #-}
{-# OPTIONS --postfix-projections #-}
module Oscar.Class where

open import Oscar.Prelude

open import Oscar.Data using (_≡_; ∅; _≡̇_)

module _ where

  record Reflexivity
    {a} {A : Ø a}
    {b} (_⊸_ : A → A → Ø b)
    : Ø a ∙̂ b where
    field reflexivity : ∀ {x} → x ⊸ x

  open Reflexivity ⦃ … ⦄ public

module _ where

  record Symmetry
    {a} {A : Ø a}
    {b} (_⊸_ : A → A → Ø b)
    : Ø a ∙̂ b where
    field symmetry : ∀ {x y} → x ⊸ y → y ⊸ x

  open Symmetry ⦃ … ⦄ public

module _ where

  record Transitivity
    {a} {A : Ø a}
    {b} (_⊸_ : A → A → Ø b)
    : Ø a ∙̂ b where
    field transitivity : ∀ {x y z} → x ⊸ y → y ⊸ z → x ⊸ z

  open Transitivity ⦃ … ⦄ public

  record _≋Transitivity_
    {a} {A : Ø a}
    {b} {_⊸_ : A → A → Ø b}
    (T1 T2 : Transitivity _⊸_)
    : Ø a ∙̂ b where
    module M1 = Transitivity T1
    module M2 = Transitivity T2
    field
      ≋transitivity : ∀ {x y z} (f : x ⊸ y) (g : y ⊸ z) → M1.transitivity f g ≡ M2.transitivity f g


{-
  module _ where

    record Compositionality
      {a} {A : Ø a}
      {b} (_⊸_ : A → A → Ø b)
      : Ø a ∙̂ b where
      infixr 9 _∙_
      field _∙_ : ∀ {x y z} → y ⊸ z → x ⊸ y → x ⊸ z

    open Compositionality ⦃ … ⦄ public

    instance

      ⌶Transitivity→Compositionality : ∀ {a} {A : Ø a} {b} {⊸ : A → A → Ø b} ⦃ _ : Transitivity ⊸ ⦄ → Compositionality ⊸
      ⌶Transitivity→Compositionality .Compositionality._∙_ g f = transitivity f g
-}

  module _ where

    infixr 9 _∙_
    _∙_ : ∀
      {a} {A : Ø a}
      {b} {_⊸_ : A → A → Ø b}
      ⦃ _ : Transitivity _⊸_ ⦄
      {x y z} → y ⊸ z → x ⊸ y → x ⊸ z
    g ∙ f = transitivity f g

{-
--     record Compositionality
--       {a} {A : Ø a}
--       {b} (_⊸_ : A → A → Ø b)
--       ⦃ _ : Transitivity _⊸_ ⦄
--       : Ø a ∙̂ b where
-- --      no-eta-equality
-- --      field
-- --        ⦃ ⌶Transitivity ⦄ : Transitivity _⊸_
--       infixr 9 _∙_
--       _∙_ : ∀ {x y z} → y ⊸ z → x ⊸ y → x ⊸ z
--       _∙_ g f = transitivity f g

--     open Compositionality ⦃ … ⦄ public
-}

module _ where

  record IsEquality
    {a} {A : Ø a}
    {b} (⊸ : A → A → Ø b)
    : Ø a ∙̂ b where
    field
      instance ⦃ ⌶Reflexivity ⦄ : Reflexivity ⊸
      instance ⦃ ⌶Symmetry ⦄ : Symmetry ⊸
      instance ⦃ ⌶Transitivity ⦄ : Transitivity ⊸

  instance
    IsEquality≋Transitivity : ∀
      {a} {A : Ø a}
      {b} {_⊸_ : A → A → Ø b}
      → IsEquality (_≋Transitivity_ {_⊸_ = _⊸_})
    IsEquality≋Transitivity {a} {A} {b} {_⊸_} .IsEquality.⌶Reflexivity .Reflexivity.reflexivity {x} ._≋Transitivity_.≋transitivity = {!!}
    IsEquality≋Transitivity {a} {A} {b} {_⊸_} .IsEquality.⌶Symmetry .Symmetry.symmetry {x} {y} x₁ ._≋Transitivity_.≋transitivity f g = {!!}
    IsEquality≋Transitivity {a} {A} {b} {_⊸_} .IsEquality.⌶Transitivity = {!!}

module _ where

  record Setoid a ℓ : Ø ↑̂ (a ∙̂ ℓ) where
    field
      Ob : Ø a
      Eq : Ob → Ob → Ø ℓ
      instance ⦃ ⌶IsEquality ⦄ : IsEquality Eq

module _ where

  record Equality {a} (A : Set a) ℓ : Ø a ∙̂ ↑̂ ℓ where
    infix 4 _≋_
    field
      _≋_ : A → A → Ø ℓ
      ⦃ ⌶IsEquality ⦄ : IsEquality _≋_

  open Equality ⦃ … ⦄ public using (_≋_)

  instance EqualityTransitivity : ∀ {o} {Obj : Ø o} {m} {Hom : Obj → Obj → Ø m} → Equality (Transitivity Hom) _
  EqualityTransitivity {o} {Obj} {m} {Hom} .Equality._≋_ = _≋Transitivity_
  EqualityTransitivity {o} {Obj} {m} {Hom} .Equality.⌶IsEquality = it

  instance EqualityEq2 : ∀ {o} {Obj : Ø o} {m} {Hom : Obj → Obj → Ø m} {ℓ} → Equality (∀ {x y} → Hom x y → Hom x y → Ø ℓ) m
  EqualityEq2 = {!!}

module _ where

  record Transextensionality
    {a} {A : Ø a}
    {m} (_⊸_ : A → A → Ø m)
    {ℓ} (_≋_ : ∀ {x y} → x ⊸ y → x ⊸ y → Ø ℓ)
    : Ø a ∙̂ m ∙̂ ℓ where
    no-eta-equality
    field
      ⦃ ⌶Transitivity ⦄ : Transitivity _⊸_
      transextensionality : ∀ {x y z} {f₁ f₂ : x ⊸ y} {g₁ g₂ : y ⊸ z} → f₁ ≋ f₂ → g₁ ≋ g₂ → (g₁ ∙ f₁) ≋ (g₂ ∙ f₂)

  open Transextensionality ⦃ … ⦄ public using (transextensionality)

  record Transassociativity
    {a} {A : Ø a}
    {m} (_⊸_ : A → A → Ø m)
    {ℓ} (_≋_ : ∀ {x y} → x ⊸ y → x ⊸ y → Ø ℓ)
    : Ø a ∙̂ m ∙̂ ↑̂ ℓ where
    no-eta-equality
    field
      ⦃ ⌶Transitivity ⦄ : Transitivity _⊸_
      -- ⦃ _ : ∀ {x y} → IsEquality (_≋_ {x} {y}) ⦄
      transassociativity : ∀ {w x y z} (f : w ⊸ x) (g : x ⊸ y) (h : y ⊸ z) → ((h ∙ g) ∙ f) ≋ (h ∙ g ∙ f)

  open Transassociativity ⦃ … ⦄ public using (transassociativity)

  test-transassociativity : ∀
    {a} {A : Ø a}
    {m} {_⊸_ : A → A → Ø m}
    {ℓ} {_≋_ : ∀ {x y} → x ⊸ y → x ⊸ y → Ø ℓ}
    ⦃ TA : Transassociativity _⊸_ _≋_ ⦄
    ⦃ TA' : Transassociativity _⊸_ _≋_ ⦄
    (let instance _ = Transassociativity.⌶Transitivity TA)
    → ∀ {w x y z} (f : w ⊸ x) (g : x ⊸ y) (h : y ⊸ z) → ((h ∙ g) ∙ f) ≋ (h ∙ g ∙ f)
  test-transassociativity = transassociativity

  record Semigroupoid o m ℓ : Ø ↑̂ (o ∙̂ m ∙̂ ℓ) where
    field
      Obj : Ø o
      Hom : Obj → Obj → Ø m
      instance ⦃ ⌶TransitivityHom ⦄ : Transitivity Hom
      Eq : ∀ {x y} → Hom x y → Hom x y → Ø ℓ
      instance ⦃ ⌶IsEqualityEq ⦄ : ∀ {x y} → IsEquality (Eq {x} {y})
      instance ⦃ ⌶Transassociativity ⦄ : Transassociativity Hom Eq
      ⌶Transassociativity-≋-⌶Transitivity : Transassociativity.⌶Transitivity ⌶Transassociativity ≡ ⌶TransitivityHom
      instance ⦃ ⌶Transextensionality ⦄ : Transextensionality Hom Eq
      ⌶Transextensionality-≋-⌶Transitivity : Transextensionality.⌶Transitivity ⌶Transextensionality ≡ ⌶TransitivityHom

  record Map
    {a₁} {A₁ : Ø a₁}
    {m₁} (_⊸₁_ : A₁ → A₁ → Ø m₁)
    {a₂} {A₂ : Ø a₂}
    {m₂} (_⊸₂_ : A₂ → A₂ → Ø m₂)
    : Ø a₁ ∙̂ m₁ ∙̂ a₂ ∙̂ m₂ where
    -- no-eta-equality
    field
      μ : A₁ → A₂
      map : ∀ {x y} → x ⊸₁ y → μ x ⊸₂ μ y

  open Map ⦃ … ⦄ public

  map[_] : ∀
    {a₁} {A₁ : Ø a₁}
    {m₁} {_⊸₁_ : A₁ → A₁ → Ø m₁}
    {a₂} {A₂ : Ø a₂}
    {m₂} (_⊸₂_ : A₂ → A₂ → Ø m₂)
    ⦃ ⌶Map : Map _⊸₁_ _⊸₂_ ⦄
    → ∀ {x y} → x ⊸₁ y → Map.μ ⌶Map x ⊸₂ Map.μ ⌶Map y
  map[ _ ] = map

  record Mapextensionality
    {a₁} {A₁ : Ø a₁}
    {m₁} (_⊸₁_ : A₁ → A₁ → Ø m₁)
    {ℓ₁} (_≋₁_ : ∀ {x y} → x ⊸₁ y → x ⊸₁ y → Ø ℓ₁)
    {a₂} {A₂ : Ø a₂}
    {m₂} (_⊸₂_ : A₂ → A₂ → Ø m₂)
    {ℓ₂} (_≋₂_ : ∀ {x y} → x ⊸₂ y → x ⊸₂ y → Ø ℓ₂)
    : Ø a₁ ∙̂ m₁ ∙̂ a₂ ∙̂ m₂ ∙̂ ℓ₁ ∙̂ ℓ₂
    where
    field
    -- ⦃ _ : ∀ {x y} → IsEquality (_≋₁_ {x} {y}) ⦄
    -- ⦃ _ : ∀ {x y} → IsEquality (_≋₂_ {x} {y}) ⦄
      ⦃ ⌶Map ⦄ : Map _⊸₁_ _⊸₂_
      mapextensionality : ∀ {x y} {f₁ f₂ : x ⊸₁ y} → f₁ ≋₁ f₂ → map f₁ ≋₂ map f₂

  open Mapextensionality ⦃ … ⦄ public using (mapextensionality)

  test-mapextensionality : ∀
    {a₁} {A₁ : Ø a₁}
    {m₁} {_⊸₁_ : A₁ → A₁ → Ø m₁}
    {ℓ₁} {_≋₁_ : ∀ {x y} → x ⊸₁ y → x ⊸₁ y → Ø ℓ₁}
    {a₂} {A₂ : Ø a₂}
    {m₂} {_⊸₂_ : A₂ → A₂ → Ø m₂}
    {ℓ₂} {_≋₂_ : ∀ {x y} → x ⊸₂ y → x ⊸₂ y → Ø ℓ₂}
    ⦃ ⌶ME : Mapextensionality _⊸₁_ _≋₁_ _⊸₂_ _≋₂_ ⦄
    ⦃ ⌶ME' : Mapextensionality _⊸₁_ _≋₁_ _⊸₂_ _≋₂_ ⦄
--    (open MapExtensionality ⦃ … ⦄)
    → ∀ {x y} {f₁ f₂ : x ⊸₁ y} → f₁ ≋₁ f₂ → (Map.map (Mapextensionality.⌶Map ⌶ME)) f₁ ≋₂ (Map.map (Mapextensionality.⌶Map ⌶ME)) f₂
  test-mapextensionality = mapextensionality

  record Maptranscommutativity
    {a₁} {A₁ : Ø a₁}
    {m₁} (_⊸₁_ : A₁ → A₁ → Ø m₁)
    {a₂} {A₂ : Ø a₂}
    {m₂} (_⊸₂_ : A₂ → A₂ → Ø m₂)
    {ℓ₂} (_≋₂_ : ∀ {x y} → x ⊸₂ y → x ⊸₂ y → Ø ℓ₂)
    : Ø a₁ ∙̂ a₂ ∙̂ m₁ ∙̂ m₂ ∙̂ ℓ₂
    where
    field
      ⦃ ⌶Transitivity₁ ⦄ : Transitivity _⊸₁_
      ⦃ ⌶Transitivity₂ ⦄ : Transitivity _⊸₂_
      ⦃ ⌶Map ⦄ : Map _⊸₁_ _⊸₂_
      maptranscommutativity : ∀ {x y z} (f : x ⊸₁ y) (g : y ⊸₁ z) → map (g ∙ f) ≋₂ (map g ∙ map f)

  open Maptranscommutativity ⦃ … ⦄ public using (maptranscommutativity)

  test-maptranscommutativity' : ∀
    {a₁} {A₁ : Ø a₁}
    {m₁} {_⊸₁_ : A₁ → A₁ → Ø m₁}
    {a₂} {A₂ : Ø a₂}
    {m₂} {_⊸₂_ : A₂ → A₂ → Ø m₂}
    {ℓ₂} {_≋₂_ : ∀ {x y} → x ⊸₂ y → x ⊸₂ y → Ø ℓ₂}
    ⦃ ⌶MT : Maptranscommutativity _⊸₁_ _⊸₂_ _≋₂_ ⦄
    ⦃ ⌶MT' : Maptranscommutativity _⊸₁_ _⊸₂_ _≋₂_ ⦄
    → ∀ {x y z} (f : x ⊸₁ y) (g : y ⊸₁ z) → Map.map (Maptranscommutativity.⌶Map ⌶MT) (g ∙ f) ≋₂ (map g ∙ map f)
  test-maptranscommutativity' = maptranscommutativity

  record Semifunctor o₁ m₁ ℓ₁ o₂ m₂ ℓ₂ : Ø ↑̂ (o₁ ∙̂ m₁ ∙̂ ℓ₁ ∙̂ o₂ ∙̂ m₂ ∙̂ ℓ₂) where
    field
      instance ⌶Semigroupoid₁ : Semigroupoid o₁ m₁ ℓ₁
      instance ⌶Semigroupoid₂ : Semigroupoid o₂ m₂ ℓ₂
    module ⒈ = Semigroupoid ⌶Semigroupoid₁
    module ⒉ = Semigroupoid ⌶Semigroupoid₂
    field
      μ : ⒈.Obj → ⒉.Obj
      instance ⦃ ⌶Map ⦄ : Map ⒈.Hom ⒉.Hom
      instance ⦃ ⌶Mapextensionality ⦄ : Mapextensionality ⒈.Hom ⒈.Eq ⒉.Hom ⒉.Eq
      ⌶Map∈⌶Mapextensionality : ⌶Map ≡ Mapextensionality.⌶Map ⌶Mapextensionality
      instance ⦃ ⌶Maptranscommutativity ⦄ : Maptranscommutativity ⒈.Hom ⒉.Hom ⒉.Eq
      ⌶Transitivity₁∈⌶Maptranscommutativity : ⒈.⌶TransitivityHom ≡ Maptranscommutativity.⌶Transitivity₁ ⌶Maptranscommutativity
      ⌶Transitivity₂∈⌶Maptranscommutativity : ⒉.⌶TransitivityHom ≡ Maptranscommutativity.⌶Transitivity₂ ⌶Maptranscommutativity
      ⌶Map∈⌶Maptranscommutativity : ⌶Map ≡ Maptranscommutativity.⌶Map ⌶Maptranscommutativity

module Test where

  postulate
    A : Set
    B : Set
    F : A → A → Set
    _≋F_ : ∀ {x y} → F x y → F x y → Set
    G : B → B → Set
    _≋G_ : ∀ {x y} → G x y → G x y → Set
    μAB : A → B
    mapFG : ∀ {x y} → F x y → G (μAB x) (μAB y)

  instance
    SemigroupoidF : Semigroupoid _ _ _
    SemigroupoidF .Semigroupoid.Obj = A
    SemigroupoidF .Semigroupoid.Hom = F
    SemigroupoidF .Semigroupoid.⌶TransitivityHom .Transitivity.transitivity = magic
    SemigroupoidF .Semigroupoid.Eq = _≋F_
    SemigroupoidF .Semigroupoid.⌶IsEqualityEq = magic
    SemigroupoidF .Semigroupoid.⌶Transassociativity .Transassociativity.⌶Transitivity = it
    SemigroupoidF .Semigroupoid.⌶Transassociativity .Transassociativity.transassociativity = magic
    SemigroupoidF .Semigroupoid.⌶Transassociativity-≋-⌶Transitivity = ∅
    SemigroupoidF .Semigroupoid.⌶Transextensionality .Transextensionality.⌶Transitivity = it
    SemigroupoidF .Semigroupoid.⌶Transextensionality .Transextensionality.transextensionality = magic
    SemigroupoidF .Semigroupoid.⌶Transextensionality-≋-⌶Transitivity = ∅

    MapFG : Map F G
    MapFG .Map.μ = μAB
    MapFG .Map.map = mapFG

  SemifunctorFG : Semifunctor _ _ _ _ _ _
  SemifunctorFG .Semifunctor.⌶Semigroupoid₁ = SemigroupoidF
  SemifunctorFG .Semifunctor.⌶Semigroupoid₂ .Semigroupoid.Obj = B
  SemifunctorFG .Semifunctor.⌶Semigroupoid₂ .Semigroupoid.Hom = G
  SemifunctorFG .Semifunctor.⌶Semigroupoid₂ .Semigroupoid.⌶TransitivityHom = magic
  SemifunctorFG .Semifunctor.⌶Semigroupoid₂ .Semigroupoid.Eq = _≋G_
  SemifunctorFG .Semifunctor.⌶Semigroupoid₂ .Semigroupoid.⌶IsEqualityEq = magic
  SemifunctorFG .Semifunctor.⌶Semigroupoid₂ .Semigroupoid.⌶Transassociativity .Transassociativity.⌶Transitivity = magic
  SemifunctorFG .Semifunctor.⌶Semigroupoid₂ .Semigroupoid.⌶Transassociativity .Transassociativity.transassociativity = magic
  SemifunctorFG .Semifunctor.⌶Semigroupoid₂ .Semigroupoid.⌶Transassociativity-≋-⌶Transitivity = ∅
  SemifunctorFG .Semifunctor.⌶Semigroupoid₂ .Semigroupoid.⌶Transextensionality .Transextensionality.⌶Transitivity = magic
  SemifunctorFG .Semifunctor.⌶Semigroupoid₂ .Semigroupoid.⌶Transextensionality .Transextensionality.transextensionality = magic
  SemifunctorFG .Semifunctor.⌶Semigroupoid₂ .Semigroupoid.⌶Transextensionality-≋-⌶Transitivity = ∅
  SemifunctorFG .Semifunctor.μ = μAB
  SemifunctorFG .Semifunctor.⌶Map = it
  SemifunctorFG .Semifunctor.⌶Mapextensionality .Mapextensionality.⌶Map = it
  SemifunctorFG .Semifunctor.⌶Mapextensionality .Mapextensionality.mapextensionality = magic
  SemifunctorFG .Semifunctor.⌶Map∈⌶Mapextensionality = ∅
  SemifunctorFG .Semifunctor.⌶Maptranscommutativity .Maptranscommutativity.⌶Transitivity₁ = it
  SemifunctorFG .Semifunctor.⌶Maptranscommutativity .Maptranscommutativity.⌶Transitivity₂ = magic
  SemifunctorFG .Semifunctor.⌶Maptranscommutativity .Maptranscommutativity.⌶Map = it
  SemifunctorFG .Semifunctor.⌶Maptranscommutativity .Maptranscommutativity.maptranscommutativity = magic
  SemifunctorFG .Semifunctor.⌶Transitivity₁∈⌶Maptranscommutativity = ∅
  SemifunctorFG .Semifunctor.⌶Transitivity₂∈⌶Maptranscommutativity = ∅
  SemifunctorFG .Semifunctor.⌶Map∈⌶Maptranscommutativity = ∅

  instance ⌶SemifunctorFG = SemifunctorFG

  postulate
    instance SemifunctorXY : Semifunctor ∅̂ ∅̂ ∅̂ ∅̂ ∅̂ ∅̂

  test- : ∀ {x y z} (f : F x y) (g : F y z) → map (g ∙ f) ≋G (map g ∙ map f)
  test- = maptranscommutativity

--       instance ⦃ ⌶ExtensionalityMap ⦄ : Extensionality₁ ⒈.Hom ⒈.Eq (⒉.Eq on map)
--       instance ⦃ ⌶CommuteMap ⦄ : Commute ⒈.Hom (λ f g → ⒉.Eq (map (g ∙ f)) (map g ∙ map f))

-- --       instance ⦃ ⌶Map ⦄ : Map ⒈.Hom (⒉.Hom on μ)
-- --       instance ⦃ ⌶ExtensionalityMap ⦄ : Extensionality₁ ⒈.Hom ⒈.Eq (⒉.Eq on map)
-- --       instance ⦃ ⌶CommuteMap ⦄ : Commute ⒈.Hom (λ f g → ⒉.Eq (map (g ∙ f)) (map g ∙ map f))

-- -- --   record Map
-- -- --     {a} {A : Ø a}
-- -- --     {m₁} (_⊸₁_ : A → A → Ø m₁)
-- -- --     {m₂} (_⊸₂_ : A → A → Ø m₂)
-- -- --     : Ø a ∙̂ m₁ ∙̂ m₂ where
-- -- --     field
-- -- --       map : ∀ {x y} → x ⊸₁ y → x ⊸₂ y

-- -- --   open Map ⦃ … ⦄ public

-- -- --   map[_] : ∀
-- -- --     {a} {A : Ø a}
-- -- --     {m₁} {_⊸₁_ : A → A → Ø m₁}
-- -- --     {m₂} (_⊸₂_ : A → A → Ø m₂)
-- -- --     ⦃ _ : Map _⊸₁_ _⊸₂_ ⦄
-- -- --     → ∀ {x y} → x ⊸₁ y → x ⊸₂ y
-- -- --   map[ _ ] = map

-- -- --   record Extensionality₁
-- -- --     {a} {A : Ø a}
-- -- --     {m₁} (_⊸_ : A → A → Ø m₁)
-- -- --     {ℓ₁} (_≋₁_ : ∀ {x y} → x ⊸ y → x ⊸ y → Ø ℓ₁)
-- -- --     {ℓ₂} (_≋₂_ : ∀ {x y} → x ⊸ y → x ⊸ y → Ø ℓ₂)
-- -- --     -- ⦃ _ : ∀ {x y} → IsEquality (_≋₁_ {x} {y}) ⦄
-- -- --     -- ⦃ _ : ∀ {x y} → IsEquality (_≋₂_ {x} {y}) ⦄
-- -- --     : Ø a ∙̂ m₁ ∙̂ ℓ₁ ∙̂ ℓ₂
-- -- --     where
-- -- --     field
-- -- --       extensionality₁ : ∀ {x y} {f₁ f₂ : x ⊸ y} → f₁ ≋₁ f₂ → f₁ ≋₂ f₂

-- -- --   open Extensionality₁ ⦃ … ⦄ public

-- -- --   record MapExtensionality
-- -- --     {a} {A : Ø a}
-- -- --     {m₁} (_⊸_ : A → A → Ø m₁)
-- -- --     {ℓ₁} (_≋₁_ : ∀ {x y} → x ⊸ y → x ⊸ y → Ø ℓ₁)
-- -- --     ℓ₂
-- -- --     -- ⦃ _ : ∀ {x y} → IsEquality (_≋₁_ {x} {y}) ⦄
-- -- --     -- ⦃ _ : ∀ {x y} → IsEquality (_≋₂_ {x} {y}) ⦄
-- -- --     : Ø a ∙̂ m₁ ∙̂ ℓ₁ ∙̂ ℓ₂
-- -- --     where
-- -- --     field
-- -- --       _⊸₂_ : A → A → Ø m₂
-- -- --       ⦃ ⌶Map ⦄ : Map _⊸_ _⊸₂_
-- -- --       _≋₂_ : ∀ {x y} → x ⊸ y → x ⊸ y → Ø ℓ₂
-- -- --       mapextensionality : ∀ {x y} {f₁ f₂ : x ⊸ y} → f₁ ≋₁ f₂ → map f₁ ≋₂ map f₂

-- -- --   open Extensionality₁ ⦃ … ⦄ public

-- -- --   record Commute
-- -- --     {a} {A : Ø a}
-- -- --     {m} (_⊸_ : A → A → Ø m)
-- -- --     {ℓ} (_↦_ : ∀ {x y z} → x ⊸ y → y ⊸ z → Ø ℓ)
-- -- --     : Ø a ∙̂ m ∙̂ ℓ
-- -- --     where
-- -- --     field
-- -- --       commute : ∀ {x y z} (f : x ⊸ y) (g : y ⊸ z) → f ↦ g

-- -- --   open Commute ⦃ … ⦄ public

-- -- --   record Maptranscommutativity
-- -- --     {a} {A : Ø a}
-- -- --     {m₁} (_⊸₁_ : A → A → Ø m₁)
-- -- --     ⦃ _ : Transitivity _⊸₁_ ⦄
-- -- --     {m₂} (_⊸₂_ : A → A → Ø m₂)
-- -- --     ⦃ _ : Transitivity _⊸₂_ ⦄
-- -- --     ⦃ _ : Map _⊸₁_ _⊸₂_ ⦄
-- -- --     {ℓ₂} (_≋₂_ : ∀ {x y} → x ⊸₂ y → x ⊸₂ y → Ø ℓ₂)
-- -- --     ⦃ _ : ∀ {x y} → IsEquality (_≋₂_ {x} {y}) ⦄
-- -- --     : Ø a ∙̂ m₁ ∙̂ m₂ ∙̂ ℓ₂
-- -- --     where
-- -- --     field
-- -- --       maptranscommutativity : ∀ {x y z} (f : x ⊸₁ y) (g : y ⊸₁ z) → map (g ∙ f) ≋₂ (map g ∙ map f)

-- -- --   open Maptranscommutativity ⦃ … ⦄ public

-- -- --   record Semifunctor o₁ m₁ ℓ₁ o₂ m₂ ℓ₂ : Ø ↑̂ (o₁ ∙̂ m₁ ∙̂ ℓ₁ ∙̂ o₂ ∙̂ m₂ ∙̂ ℓ₂) where
-- -- --     field
-- -- --       instance ⦃ ⌶Semigroupoid₁ ⦄ : Semigroupoid o₁ m₁ ℓ₁
-- -- --       instance ⦃ ⌶Semigroupoid₂ ⦄ : Semigroupoid o₂ m₂ ℓ₂
-- -- --     module ⒈ = Semigroupoid ⌶Semigroupoid₁
-- -- --     module ⒉ = Semigroupoid ⌶Semigroupoid₂
-- -- --     field
-- -- --       μ : ⒈.Obj → ⒉.Obj
-- -- --       instance ⦃ ⌶Map ⦄ : Map ⒈.Hom (⒉.Hom on μ)
-- -- --       instance ⦃ ⌶ExtensionalityMap ⦄ : Extensionality₁ ⒈.Hom ⒈.Eq (⒉.Eq on map)
-- -- --       instance ⦃ ⌶CommuteMap ⦄ : Commute ⒈.Hom (λ f g → ⒉.Eq (map (g ∙ f)) (map g ∙ map f))

-- -- -- module Test where

-- -- --   module T where

-- -- --     test-maptranscommutativity : ∀
-- -- --       {a} {A : Ø a}
-- -- --       {m₁} {_⊸₁_ : A → A → Ø m₁}
-- -- --       ⦃ _ : Transitivity _⊸₁_ ⦄
-- -- --       {m₂} {_⊸₂_ : A → A → Ø m₂}
-- -- --       ⦃ _ : Transitivity _⊸₂_ ⦄
-- -- --       ⦃ _ : Map _⊸₁_ _⊸₂_ ⦄
-- -- --       {ℓ₂} {_≋₂_ : ∀ {x y} → x ⊸₂ y → x ⊸₂ y → Ø ℓ₂}
-- -- --       ⦃ _ : ∀ {x y} → IsEquality (_≋₂_ {x} {y}) ⦄
-- -- --       ⦃ _ : Maptranscommutativity _⊸₁_ _⊸₂_ _≋₂_ ⦄
-- -- --       → ∀ {x y z} (f : x ⊸₁ y) (g : y ⊸₁ z) → map (g ∙ f) ≋₂ (map g ∙ map f)
-- -- --     test-maptranscommutativity = maptranscommutativity

-- -- --   module T0
-- -- --     {o₁ m₁ ℓ₁ o₂ m₂ ℓ₂}
-- -- --     ⦃ SF : Semifunctor o₁ m₁ ℓ₁ o₂ m₂ ℓ₂ ⦄
-- -- --     where
-- -- --     open Semifunctor ⦃ … ⦄

-- -- --     _⊸₁_ = ⒈.Hom
-- -- --     _⊸₂_ = ⒉.Hom
-- -- --     _≋₁_ = ⒈.Eq
-- -- --     _≋₂_ = ⒉.Eq
-- -- --     μ₁₂ = μ

-- -- --     instance ⌶Equality₁ : ∀ {x y} → Equality (x ⊸₁ y) ℓ₁
-- -- --     ⌶Equality₁ {x} {y} .Equality._≋_ = ⒈.Eq
-- -- --     ⌶Equality₁ {x} {y} .Equality.⌶IsEquality = it

-- -- --     instance ⌶Equality₂ : ∀ {x y} → Equality (x ⊸₂ y) ℓ₂
-- -- --     ⌶Equality₂ {x} {y} .Equality._≋_ = ⒉.Eq
-- -- --     ⌶Equality₂ {x} {y} .Equality.⌶IsEquality = it

-- -- --     test-sf-extensionality : ∀ {x y} {f₁ f₂ : x ⊸₁ y} → f₁ ≋ f₂ → map[ _⊸₂_ on μ ] f₁ ≋ map f₂
-- -- --     test-sf-extensionality = extensionality₁

-- -- --     test-sf-transcommutativity' : ∀ {x y z} (f : x ⊸₁ y) (g : y ⊸₁ z) → map[ _⊸₂_ on μ ] (g ∙ f) ≋ (map g ∙ map f)
-- -- --     test-sf-transcommutativity' = commute

-- -- --     test-sf-transcommutativity : ∀ {x y z} (f : x ⊸₁ y) (g : y ⊸₁ z) → map (g ∙ f) ≋₂ (map g ∙ map f)
-- -- --     test-sf-transcommutativity = commute

-- -- --     test-sf-transext2 : ∀ {x y z} {f₁ f₂ : x ⊸₁ y} {g₁ g₂ : y ⊸₁ z} → f₁ ≋ f₂ → g₁ ≋ g₂ → (map g₁ ∙ map f₁) ≋₂ (map g₂ ∙ map f₂)
-- -- --     test-sf-transext2 eqf eqg = transextensionality {_≋_ = _≋₂_} (extensionality₁ eqf) (extensionality₁ eqg)
-- -- --     -- ⦃ r = ⒉.⌶Transextensionality ⦄

-- -- --     test-sf-transext2' : ∀ {x y z} {f₁ f₂ : x ⊸₁ y} {g₁ g₂ : y ⊸₁ z} → f₁ ≋ f₂ → g₁ ≋ g₂ → (map[ _⊸₂_ on μ ] g₁ ∙ map f₁) ≋ (map g₂ ∙ map f₂)
-- -- --     test-sf-transext2' eqf eqg = transextensionality {_≋_ = _≋₂_} (extensionality₁ eqf) (extensionality₁ eqg)

-- -- --     test-sf-transext2'' : ∀ {x y z} {f₁ f₂ : x ⊸₁ y} {g₁ g₂ : y ⊸₁ z} → f₁ ≋ f₂ → g₁ ≋ g₂ → (map[ _⊸₂_ on μ ] g₁ ∙ map f₁) ≋ (map g₂ ∙ map f₂)
-- -- --     test-sf-transext2'' eqf eqg = contiguextension {_≋₁_ = _≋₂_} {_≋₂_ = _≋₂_} (extensionality₁ eqf) (extensionality₁ eqg)
-- -- --     -- ⦃ r = ⒉.⌶Contiguextension ⦄

-- -- --     test-sf-transext4 : ∀ {x y z} {f₁ f₂ : x ⊸₁ y} {g₁ g₂ : y ⊸₁ z} → f₁ ≋ f₂ → g₁ ≋ g₂ → (map[ _⊸₂_ on μ ] g₁ ∙ map f₁) ≋ (map g₂ ∙ map f₂)
-- -- --     test-sf-transext4 eqf eqg = transextensionality {_≋_ = _≋₂_} (_≋₂_ _ _ ∋ extensionality₁ eqf) (_≋₂_ _ _ ∋ extensionality₁ eqg)

-- -- --     test-sf-transext4' : ∀ {x y z} {f₁ f₂ : x ⊸₁ y} {g₁ g₂ : y ⊸₁ z} → f₁ ≋ f₂ → g₁ ≋ g₂ → (map[ _⊸₂_ on μ ] g₁ ∙ map f₁) ≋ (map g₂ ∙ map f₂)
-- -- --     test-sf-transext4' eqf eqg = contiguextension {_≋₁_ = _} (_≋₂_ _ _ ∋ extensionality₁ eqf) (_≋₂_ _ _ ∋ extensionality₁ eqg)

-- -- --     test-sf-transext3 : ∀ {x y z} {f₁ f₂ : x ⊸₁ y} {g₁ g₂ : y ⊸₁ z} → f₁ ≋ f₂ → g₁ ≋ g₂ → (g₁ ∙ f₁) ≋ (g₂ ∙ f₂)
-- -- --     test-sf-transext3 eqf eqg = contiguextension eqf eqg


-- -- -- --   module T0' where

-- -- -- --     postulate
-- -- -- --       A : Set
-- -- -- --       _⊸_ : A → A → Set
-- -- -- --       instance T⊸ : Transitivity _⊸_
-- -- -- --       _≋A_ : ∀ {x y} → x ⊸ y → x ⊸ y → Set
-- -- -- --       instance isEA : ∀ {x y} → IsEquality (_≋A_ {x} {y})
-- -- -- --       instance TexA : Transextensionality _⊸_ _≋A_
-- -- -- --       -- _≋B_ : ∀ {x y} → x ⊸ y → x ⊸ y → Set
-- -- -- --       -- instance isEB : ∀ {x y} → IsEquality (_≋B_ {x} {y})
-- -- -- --       -- instance TexB : Transextensionality _⊸_ _≋B_

-- -- -- --     --open Transextensionality ⦃ … ⦄
-- -- -- --     --open Transassociativity ⦃ … ⦄

-- -- -- --     test-transext : ∀ {x y z} {f₁ f₂ : x ⊸ y} {g₁ g₂ : y ⊸ z} → f₁ ≋A f₂ → g₁ ≋A g₂ → (g₁ ∙ f₁) ≋A (g₂ ∙ f₂)
-- -- -- --     test-transext = transextensionality

-- -- -- --     postulate
-- -- -- --       instance TAssA : Transassociativity _⊸_ _≋A_

-- -- -- --     test-transAss : ∀ {w x y z} (f : w ⊸ x) (g : x ⊸ y) (h : y ⊸ z) → ((h ∙ g) ∙ f) ≋A (h ∙ g ∙ f)
-- -- -- --     test-transAss = transassociativity

-- -- -- --   module T1 where

-- -- -- --     test-Setoid :
-- -- -- --       ∀ {a ℓ} ⦃ s : Setoid a ℓ ⦄ {x y : s .Setoid.Ob} → s .Setoid.Eq x y → s .Setoid.Eq y x
-- -- -- --     test-Setoid = symmetry

-- -- -- --   module T2 where

-- -- -- --     postulate
-- -- -- --       A : Set
-- -- -- --       EqA : A → A → Set
-- -- -- -- {-
-- -- -- --     instance

-- -- -- --       ⌶ReflexivityA : Reflexivity EqA
-- -- -- --       ⌶ReflexivityA .Reflexivity.reflexivity = magic
-- -- -- -- -}
-- -- -- --     instance

-- -- -- --       ⌶SymmetryA : Symmetry EqA
-- -- -- --       ⌶SymmetryA .Symmetry.symmetry = magic

-- -- -- --     instance

-- -- -- --       ⌶TransitivityA : Transitivity EqA
-- -- -- --       ⌶TransitivityA .Transitivity.transitivity = magic

-- -- -- --     IsEqualityA : IsEquality EqA
-- -- -- --     IsEqualityA .IsEquality.⌶Reflexivity = magic

-- -- -- --     instance

-- -- -- --       ⌶IsEqualityA = IsEqualityA

-- -- -- -- {-
-- -- -- --       ⌶IsEqualityA : IsEquality EqA
-- -- -- --       ⌶IsEqualityA .IsEquality.⌶Reflexivity = ⌶ReflexivityA
-- -- -- --       ⌶IsEqualityA .IsEquality.⌶Symmetry = ⌶SymmetryA
-- -- -- --       ⌶IsEqualityA .IsEquality.⌶Transitivity = ⌶TransitivityA
-- -- -- -- -}
-- -- -- -- {-
-- -- -- --       ⌶IsEqualityA .IsEquality.⌶Reflexivity = magic
-- -- -- -- --      ⌶IsEqualityA .IsEquality.⌶Symmetry = it -- ⌶SymmetryA -- it -- ⌶SymmetryA
-- -- -- --       -- it -- .Symmetry.symmetry = magic
-- -- -- --       ⌶IsEqualityA .IsEquality.⌶Transitivity = magic
-- -- -- -- -}
-- -- -- --     instance

-- -- -- --       SetoidA : Setoid _ _
-- -- -- --       SetoidA .Setoid.Ob = A
-- -- -- --       SetoidA .Setoid.Eq = EqA
-- -- -- --       SetoidA .Setoid.⌶IsEquality = ⌶IsEqualityA

-- -- -- --     test-SetoidA-sym : ∀ {x y} → EqA x y → EqA y x
-- -- -- --     test-SetoidA-sym = symmetry

-- -- -- --     test-SetoidA-ref : ∀ {x} → EqA x x
-- -- -- --     test-SetoidA-ref = reflexivity -- doesn't work b/c no defined instance

-- -- -- -- --   module T3 where

-- -- -- -- --     open Semigroupoid ⦃ … ⦄

-- -- -- -- --     test-transextensionality-semigroupoid : ∀
-- -- -- -- --       {o m ℓ} ⦃ _ : Semigroupoid o m ℓ ⦄
-- -- -- -- --       → ∀ {x y z} {f₁ f₂ : x ⊸ y} {g₁ g₂ : y ⊸ z} → f₁ ≋ f₂ → g₁ ≋ g₂ → g₁ ∙ f₁ ≋ g₂ ∙ f₂
-- -- -- -- --     test-transextensionality-semigroupoid = transextensionality

-- -- -- -- --     test-transassociativity-semigroupoid : ∀
-- -- -- -- --       {o m ℓ} ⦃ _ : Semigroupoid o m ℓ ⦄
-- -- -- -- --       → ∀ {w x y z} (f : w ⊸ x) (g : x ⊸ y) (h : y ⊸ z) → (h ∙ g) ∙ f ≋ h ∙ g ∙ f
-- -- -- -- --     test-transassociativity-semigroupoid = transassociativity

-- -- -- -- --   module T4 where

-- -- -- -- --     open Semigroupoid ⦃ … ⦄
-- -- -- -- --     open Semifunctor ⦃ … ⦄


-- -- -- -- --     postulate
-- -- -- -- --       A : Set
-- -- -- -- --       B : Set
-- -- -- -- --       C : Set
-- -- -- -- --       _⊸A_ : A → A → Set
-- -- -- -- --       _⊸B_ : B → B → Set
-- -- -- -- --       _⊸C_ : C → C → Set
-- -- -- -- --       _≋A_ : ∀ {x y} → x ⊸A y → x ⊸A y → Set
-- -- -- -- --       _≋B_ : ∀ {x y} → x ⊸B y → x ⊸B y → Set
-- -- -- -- --       _≋C_ : ∀ {x y} → x ⊸C y → x ⊸C y → Set
-- -- -- -- --       μAB : A → B
-- -- -- -- --       μAB' : A → B
-- -- -- -- --       μBC : B → C

-- -- -- -- --     instance ⌶TransitivityA : Transitivity _⊸A_
-- -- -- -- --     ⌶TransitivityA .Transitivity.transitivity = magic

-- -- -- -- --     instance ⌶TransitivityB : Transitivity _⊸B_
-- -- -- -- --     ⌶TransitivityB .Transitivity.transitivity = magic

-- -- -- -- --     instance ⌶TransitivityC : Transitivity _⊸C_
-- -- -- -- --     ⌶TransitivityC .Transitivity.transitivity = magic

-- -- -- -- --     instance ⌶EqualityA : ∀ {x y} → Equality (x ⊸A y) _
-- -- -- -- --     ⌶EqualityA {x} {y} .Equality._≋_ = _≋A_
-- -- -- -- --     ⌶EqualityA {x} {y} .Equality.⌶IsEquality = magic

-- -- -- -- --     instance ⌶EqualityB : ∀ {x y} → Equality (x ⊸B y) _
-- -- -- -- --     ⌶EqualityB {x} {y} .Equality._≋_ = _≋B_
-- -- -- -- --     ⌶EqualityB {x} {y} .Equality.⌶IsEquality = magic

-- -- -- -- --     instance ⌶EqualityC : ∀ {x y} → Equality (x ⊸C y) _
-- -- -- -- --     ⌶EqualityC {x} {y} .Equality._≋_ = _≋C_
-- -- -- -- --     ⌶EqualityC {x} {y} .Equality.⌶IsEquality = magic

-- -- -- -- --     instance SemigroupoidA : Semigroupoid _ _ _
-- -- -- -- --     SemigroupoidA .Semigroupoid.⋆ = A
-- -- -- -- --     SemigroupoidA .Semigroupoid._⊸_ = _⊸A_
-- -- -- -- --     SemigroupoidA .Semigroupoid.⌶Transitivity = it
-- -- -- -- --     SemigroupoidA .Semigroupoid.⌶Equality = ⌶EqualityA
-- -- -- -- --     SemigroupoidA .Semigroupoid.transextensionality = magic
-- -- -- -- --     SemigroupoidA .Semigroupoid.transassociativity = magic

-- -- -- -- --     instance SemigroupoidB : Semigroupoid _ _ _
-- -- -- -- --     SemigroupoidB .Semigroupoid.⋆ = B
-- -- -- -- --     SemigroupoidB .Semigroupoid._⊸_ = _⊸B_
-- -- -- -- --     SemigroupoidB .Semigroupoid.⌶Transitivity = it
-- -- -- -- --     SemigroupoidB .Semigroupoid.⌶Equality = ⌶EqualityB
-- -- -- -- --     SemigroupoidB .Semigroupoid.transextensionality = magic
-- -- -- -- --     SemigroupoidB .Semigroupoid.transassociativity = magic

-- -- -- -- --     instance SemigroupoidC : Semigroupoid _ _ _
-- -- -- -- --     SemigroupoidC .Semigroupoid.⋆ = C
-- -- -- -- --     SemigroupoidC .Semigroupoid._⊸_ = _⊸C_
-- -- -- -- --     SemigroupoidC .Semigroupoid.⌶Transitivity = it
-- -- -- -- --     SemigroupoidC .Semigroupoid.⌶Equality = ⌶EqualityC
-- -- -- -- --     SemigroupoidC .Semigroupoid.transextensionality = magic
-- -- -- -- --     SemigroupoidC .Semigroupoid.transassociativity = magic

-- -- -- -- --     instance SemifunctorAB : Semifunctor _ _ _ _ _ _
-- -- -- -- --     SemifunctorAB .Semifunctor.⌶Semigroupoid₁ = SemigroupoidA
-- -- -- -- --     SemifunctorAB .Semifunctor.⌶Semigroupoid₂ = SemigroupoidB
-- -- -- -- --     SemifunctorAB .Semifunctor.μ = μAB
-- -- -- -- --     SemifunctorAB .Semifunctor.map = magic
-- -- -- -- --     SemifunctorAB .Semifunctor.map-extensionality = magic
-- -- -- -- --     SemifunctorAB .Semifunctor.map-transcommutativity = magic

-- -- -- -- --     instance SemifunctorBC : Semifunctor _ _ _ _ _ _
-- -- -- -- --     SemifunctorBC .Semifunctor.⌶Semigroupoid₁ = SemigroupoidB
-- -- -- -- --     SemifunctorBC .Semifunctor.⌶Semigroupoid₂ = SemigroupoidC
-- -- -- -- --     SemifunctorBC .Semifunctor.μ = μBC
-- -- -- -- --     SemifunctorBC .Semifunctor.map = magic
-- -- -- -- --     SemifunctorBC .Semifunctor.map-extensionality = magic
-- -- -- -- --     SemifunctorBC .Semifunctor.map-transcommutativity = magic

-- -- -- -- --     instance Map'AC : Map' _⊸A_ (_⊸C_ on (μBC ∘ μAB))
-- -- -- -- --     Map'AC .Map'.map' = map' ∘ map'[ _⊸B_ on μAB ]

-- -- -- -- --     instance SemifunctorAC : Semifunctor _ _ _ _ _ _
-- -- -- -- --     SemifunctorAC .Semifunctor.⌶Semigroupoid₁ = SemigroupoidA
-- -- -- -- --     SemifunctorAC .Semifunctor.⌶Semigroupoid₂ = SemigroupoidC
-- -- -- -- --     SemifunctorAC .Semifunctor.μ = μBC ∘ μAB
-- -- -- -- --     SemifunctorAC .Semifunctor.map = map ∘ map'[ _⊸B_ on μAB ]
-- -- -- -- --     SemifunctorAC .Semifunctor.map-extensionality eq = map-extensionality (map-extensionality ⦃ SemifunctorAB ⦄ eq)
-- -- -- -- --     -- map-extensionality (map-extensionality ⦃ SemifunctorAB ⦄ eq)
-- -- -- -- --     -- map-extensionality ⦃ SemifunctorBC ⦄ (map-extensionality ⦃ SemifunctorAB ⦄ eq)
-- -- -- -- --     -- map-extensionality ⦃ SemifunctorBC ⦄ (map-extensionality eq)
-- -- -- -- --     -- map-extensionality (map-extensionality eq)
-- -- -- -- --     SemifunctorAC .Semifunctor.map-transcommutativity = magic

-- -- -- -- --     test-transextensionality-A : ∀ {x y z} {f₁ f₂ : x ⊸A y} {g₁ g₂ : y ⊸A z} → f₁ ≋ f₂ → g₁ ≋ g₂ → g₁ ∙ f₁ ≋ g₂ ∙ f₂
-- -- -- -- --     test-transextensionality-A = transextensionality

-- -- -- -- -- {-
-- -- -- -- --     instance SemifunctorAB' : Semifunctor _ _ _ _ _ _
-- -- -- -- --     SemifunctorAB' .Semifunctor.⌶Semigroupoid₁ = SemigroupoidA
-- -- -- -- --     SemifunctorAB' .Semifunctor.⌶Semigroupoid₂ = SemigroupoidB
-- -- -- -- --     SemifunctorAB' .Semifunctor.μ = μAB'
-- -- -- -- --     SemifunctorAB' .Semifunctor.map = magic
-- -- -- -- --     SemifunctorAB' .Semifunctor.map-extensionality = magic
-- -- -- -- --     SemifunctorAB' .Semifunctor.map-transcommutativity = magic
-- -- -- -- -- -}

-- -- -- -- --     test-map-AB : ∀ {x y} → x ⊸A y → μAB x ⊸B μAB y
-- -- -- -- --     test-map-AB = map'

-- -- -- -- --     test-map-AC : ∀ {x y} → x ⊸A y → (μBC ∘ μAB) x ⊸C (μBC ∘ μAB) y
-- -- -- -- --     test-map-AC = map

-- -- -- -- --     test-map-extensionality : ∀ {x y} {f₁ f₂ : x ⊸A y} → f₁ ≋A f₂ → map f₁ ≋B map f₂
-- -- -- -- --     test-map-extensionality = map-extensionality

-- -- -- -- --     test-map-extensionalityB : ∀ {x y} {f₁ f₂ : x ⊸B y} → f₁ ≋ f₂ → map f₁ ≋C map f₂
-- -- -- -- --     test-map-extensionalityB = map-extensionality

-- -- -- -- --     test-map-extensionalityA2 : ∀ {x y} {f₁ f₂ : x ⊸A y} → f₁ ≋A f₂ → map' (map'[ _⊸B_ on μAB ] f₁) ≋ map (map'[ _⊸B_ on μAB ] f₂)
-- -- -- -- --     test-map-extensionalityA2 = map-extensionality ∘ map-extensionality ⦃ SemifunctorAB ⦄

-- -- -- -- --     test-map-transcommutativity : ∀ {x y z} (f : x ⊸A y) (g : y ⊸A z) → map ((_⊸A_ x z) ∋ (g ∙ f)) ≋B (map g ∙ map f)
-- -- -- -- --     test-map-transcommutativity = map-transcommutativity

-- -- -- -- -- record Congruity
-- -- -- -- --   a b {c} (C : ∀ {x} {X : Ø x} → X → X → Ø c)
-- -- -- -- --   : Ø ↑̂ (a ∙̂ b ∙̂ c) where
-- -- -- -- --   field congruity : ∀ {A : Ø a} {B : Ø b} {x y} (f : A → B) → C x y → C (f x) (f y)

-- -- -- -- -- open Congruity ⦃ … ⦄ public

-- -- -- -- -- record Congruity₂
-- -- -- -- --   a b c {ℓ} (EQ : ∀ {x} {X : Ø x} → X → X → Ø ℓ)
-- -- -- -- --   : Ø ↑̂ (a ∙̂ b ∙̂ c) ∙̂ ℓ where
-- -- -- -- --   field congruity₂ : ∀ {A : Ø a} {B : Ø b} {C : Ø c} {x y} {x' y'} (f : A → B → C) → EQ x y → EQ x' y' → EQ (f x x') (f y y')

-- -- -- -- -- open Congruity₂ ⦃ … ⦄ public

-- -- -- -- -- record Ċongruity
-- -- -- -- --   𝔬 𝔭 {c}
-- -- -- -- --   (C : ∀ {𝔒 : Ø 𝔬} {𝔓 : 𝔒 → Ø 𝔭} → ((𝓞 : 𝔒) → 𝔓 𝓞) → ((𝓞 : 𝔒) → 𝔓 𝓞) → Ø c)
-- -- -- -- --   : Ø ↑̂ (𝔬 ∙̂ 𝔭) ∙̂ c where
-- -- -- -- --   field ċongruity : ∀ {𝔒 : Ø 𝔬} {𝔓 : 𝔒 → Ø 𝔭} {f g : (𝓞 : 𝔒) → 𝔓 𝓞} (F : ∀ {𝓞 : 𝔒} → 𝔓 𝓞 → 𝔓 𝓞) → C f g → C (F ∘ f) (F ∘ g)

-- -- -- -- -- open Ċongruity ⦃ … ⦄ public

-- -- -- -- -- module _
-- -- -- -- --   {a₁} {A₁ : Ø a₁} {b₁} (B₁ : A₁ → A₁ → Ø b₁)
-- -- -- -- --   {a₂} {A₂ : Ø a₂} {b₂} (B₂ : A₂ → A₂ → Ø b₂)
-- -- -- -- --   c₂ ⦃ _ : MorphismEquivalence B₂ c₂ ⦄
-- -- -- -- --   (μ : A₁ → A₂)
-- -- -- -- --   ⦃ _ : Transitivity B₁ ⦄
-- -- -- -- --   ⦃ _ : Transitivity B₂ ⦄
-- -- -- -- --   ⦃ _ : Map B₁ (B₂ on μ) ⦄
-- -- -- -- --   where
-- -- -- -- --   𝓒ommutativity : ∀ {x y z} → B₁ x y → B₁ y z → Ø c₂
-- -- -- -- --   𝓒ommutativity = λ f g → map[ B₂ on μ ] (g ∙ f) ≋ map g ∙ map f
-- -- -- -- --   𝓬ommutativity = 𝓬ontiguity B₁ 𝓒ommutativity
-- -- -- -- --   Commutativity = Contiguity B₁ 𝓒ommutativity

-- -- -- -- -- commutativity : ∀
-- -- -- -- --   {a} {A : Ø a}
-- -- -- -- --   {b} {B : A → A → Ø b}
-- -- -- -- --   {c} {C : ∀ {x y z} → B x y → B y z → Ø c}
-- -- -- -- --   ⦃ _ : Contiguity B C ⦄
-- -- -- -- --   → 𝓬ontiguity B C
-- -- -- -- -- commutativity = contiguity

-- -- -- -- -- commutativity[_] : ∀
-- -- -- -- --   {a₁} {A₁ : Ø a₁} {b₁} {B₁ : A₁ → A₁ → Ø b₁}
-- -- -- -- --   {a₂} {A₂ : Ø a₂} {b₂} (B₂ : A₂ → A₂ → Ø b₂)
-- -- -- -- --   {c₂} ⦃ _ : MorphismEquivalence B₂ c₂ ⦄
-- -- -- -- --   {μ : A₁ → A₂}
-- -- -- -- --   ⦃ _ : Transitivity B₁ ⦄
-- -- -- -- --   ⦃ _ : Transitivity B₂ ⦄
-- -- -- -- --   ⦃ _ : Map B₁ (B₂ on μ) ⦄
-- -- -- -- --   ⦃ _ : Commutativity B₁ B₂ c₂ μ ⦄
-- -- -- -- --   → 𝓬ommutativity B₁ B₂ c₂ μ
-- -- -- -- -- commutativity[ _ ] = contiguity

-- -- -- -- -- module _
-- -- -- -- --   {a} {A : Ø a}
-- -- -- -- --   {b} (B : A → Ø b)
-- -- -- -- --   where
-- -- -- -- --   𝓲dentity′ = ∀ {x} → B x
-- -- -- -- --   record Identity′ : Ø a ∙̂ b where field identity : 𝓲dentity′

-- -- -- -- -- open Identity′ ⦃ … ⦄ public

-- -- -- -- -- module _
-- -- -- -- --   {a₁} {A₁ : Ø a₁} {b₁} (B₁ : A₁ → A₁ → Ø b₁)
-- -- -- -- --   {a₂} {A₂ : Ø a₂} {b₂} (B₂ : A₂ → A₂ → Ø b₂) c₂ ⦃ _ : MorphismEquivalence B₂ c₂ ⦄
-- -- -- -- --   (μ : A₁ → A₂)
-- -- -- -- --   ⦃ _ : Reflexivity B₁ ⦄
-- -- -- -- --   ⦃ _ : Reflexivity B₂ ⦄
-- -- -- -- --   ⦃ _ : Map B₁ (B₂ on μ) ⦄
-- -- -- -- --   where
-- -- -- -- --   𝓘dentity : A₁ → Ø c₂
-- -- -- -- --   𝓘dentity = λ x → map (ε[ B₁ ] {x = x}) ≋ ε[ B₂ ] {x = μ x}
-- -- -- -- --   𝓲dentity = 𝓲dentity′ 𝓘dentity
-- -- -- -- --   Identity = Identity′ 𝓘dentity

-- -- -- -- -- record LeftIdentity
-- -- -- -- --   {a} {A : Ø a} {b}
-- -- -- -- --     (B : A → A → Ø b)
-- -- -- -- --     c
-- -- -- -- --     ⦃ _ : MorphismEquivalence B c ⦄
-- -- -- -- --     ⦃ _ : Reflexivity B ⦄
-- -- -- -- --     ⦃ _ : Transitivity B ⦄
-- -- -- -- --   : Ø a ∙̂ b ∙̂ c where
-- -- -- -- --   field left-identity : ∀ {x y} (f : B x y) → ε ∙ f ≋ f

-- -- -- -- -- open LeftIdentity ⦃ … ⦄ public

-- -- -- -- -- record RightIdentity
-- -- -- -- --   {a} {A : Ø a} {b}
-- -- -- -- --     (B : A → A → Ø b)
-- -- -- -- --     c
-- -- -- -- --     ⦃ _ : MorphismEquivalence B c ⦄
-- -- -- -- --     ⦃ _ : Reflexivity B ⦄
-- -- -- -- --     ⦃ _ : Transitivity B ⦄
-- -- -- -- --   : Ø a ∙̂ b ∙̂ c where
-- -- -- -- --   field right-identity : ∀ {x y} (f : B x y) → f ∙ ε ≋ f
-- -- -- -- -- open RightIdentity ⦃ … ⦄ public


-- -- -- -- -- module _
-- -- -- -- --   {a} {A : Ø a}
-- -- -- -- --   {b} (B : A → A → Ø b)
-- -- -- -- --   {c} (C : ∀ {x y} → B x y → B x y → Ø c)
-- -- -- -- --   {d} (D : ∀ {x y} → B x y → B x y → Ø d)
-- -- -- -- --   where

-- -- -- -- --   𝓮xtensionality₁′ : Ø a ∙̂ b ∙̂ c ∙̂ d
-- -- -- -- --   𝓮xtensionality₁′ = ∀ {x y} {f₁ f₂ : B x y} → C f₁ f₂ → D f₁ f₂

-- -- -- -- --   record Extensionality₁′ : Ø a ∙̂ b ∙̂ c ∙̂ d where field extensionality₁ : 𝓮xtensionality₁′

-- -- -- -- -- open Extensionality₁′ ⦃ … ⦄ public

-- -- -- -- -- module _
-- -- -- -- --   {a₁} {A₁ : Ø a₁} {b₁} (B₁ : A₁ → A₁ → Ø b₁) c₁ ⦃ _ : MorphismEquivalence B₁ c₁ ⦄
-- -- -- -- --   {a₂} {A₂ : Ø a₂} {b₂} (B₂ : A₂ → A₂ → Ø b₂) c₂ ⦃ _ : MorphismEquivalence B₂ c₂ ⦄
-- -- -- -- --   (μ : A₁ → A₂)
-- -- -- -- --   ⦃ _ : Map B₁ (B₂ on μ) ⦄
-- -- -- -- --   where
-- -- -- -- --   Extensionality₁ = Extensionality₁′ B₁ _≋_ (λ f₁ f₂ → map[ B₂ on μ ] f₁ ≋ map f₂)
-- -- -- -- --   𝓮xtensionality₁ = 𝓮xtensionality₁′ B₁ _≋_ (λ f₁ f₂ → map[ B₂ on μ ] f₁ ≋ map f₂)

-- -- -- -- -- module _
-- -- -- -- --   {a} {A : Ø a}
-- -- -- -- --   {b} (B : A → A → Ø b)
-- -- -- -- --   {c} (C : ∀ {x y} → B x y → B x y → Ø c)
-- -- -- -- --   {d} (D : ∀ {x y} → B x y → B x y → ∀ {z} → B y z → B y z → Ø d)
-- -- -- -- --   where

-- -- -- -- --   𝓮xtensionality₂′ = ∀ {x y} {f₁ f₂ : B x y} {z} {g₁ g₂ : B y z} → C f₁ f₂ → C g₁ g₂ → D f₁ f₂ g₁ g₂
-- -- -- -- --   record Extensionality₂′ : Ø a ∙̂ b ∙̂ c ∙̂ d where field extensionality₂ : 𝓮xtensionality₂′

-- -- -- -- -- open Extensionality₂′ ⦃ … ⦄ public

-- -- -- -- -- module _
-- -- -- -- --   {a} {A : Ø a} {b} (B : A → A → Ø b) c ⦃ _ : MorphismEquivalence B c ⦄
-- -- -- -- --   ⦃ _ : Transitivity B ⦄
-- -- -- -- --   where
-- -- -- -- --   𝓮xtensionality₂ = 𝓮xtensionality₂′ B equivalence (λ f₁ f₂ g₁ g₂ → g₁ ∙ f₁ ≋ g₂ ∙ f₂)
-- -- -- -- --   Extensionality₂ = Extensionality₂′ B equivalence (λ f₁ f₂ g₁ g₂ → g₁ ∙ f₁ ≋ g₂ ∙ f₂)

-- -- -- -- -- record IsCategory
-- -- -- -- --   {a} {A : Ø a} {b}
-- -- -- -- --     (B : A → A → Ø b)
-- -- -- -- --     c
-- -- -- -- --     ⦃ _ : MorphismEquivalence B c ⦄
-- -- -- -- --   : Ø a ∙̂ b ∙̂ c where
-- -- -- -- --   field
-- -- -- -- --     ⦃ ⌶IsSemigroupoid ⦄ : IsSemigroupoid B c
-- -- -- -- --     ⦃ ⌶Reflexivity ⦄ : Reflexivity B
-- -- -- -- --     ⦃ ⌶LeftIdentity ⦄ : LeftIdentity B c
-- -- -- -- --     ⦃ ⌶RightIdentity ⦄ : RightIdentity B c

-- -- -- -- -- record IsSemifunctor
-- -- -- -- --   {a₁} {A₁ : Ø a₁} {b₁} (B₁ : A₁ → A₁ → Ø b₁) c₁ ⦃ _ : MorphismEquivalence B₁ c₁ ⦄
-- -- -- -- --   {a₂} {A₂ : Ø a₂} {b₂} (B₂ : A₂ → A₂ → Ø b₂) c₂ ⦃ _ : MorphismEquivalence B₂ c₂ ⦄
-- -- -- -- --   (μ : A₁ → A₂)
-- -- -- -- --   : Ø a₁ ∙̂ b₁ ∙̂ c₁ ∙̂ a₂ ∙̂ b₂ ∙̂ c₂
-- -- -- -- --   where
-- -- -- -- --   field
-- -- -- -- --     ⦃ ⌶IsSemigroupoid₁ ⦄ : IsSemigroupoid B₁ c₁
-- -- -- -- --     ⦃ ⌶IsSemigroupoid₂ ⦄ : IsSemigroupoid B₂ c₂
-- -- -- -- --     ⦃ ⌶Map ⦄ : Map B₁ (B₂ on μ)
-- -- -- -- --     ⦃ ⌶Extensionality₁ ⦄ : Extensionality₁ B₁ c₁ B₂ c₂ μ
-- -- -- -- --     ⦃ ⌶Commutativity ⦄ : Commutativity B₁ B₂ c₂ μ

-- -- -- -- -- record IsFunctor
-- -- -- -- --   {a₁} {A₁ : Ø a₁} {b₁} (B₁ : A₁ → A₁ → Ø b₁) c₁ ⦃ _ : MorphismEquivalence B₁ c₁ ⦄
-- -- -- -- --   {a₂} {A₂ : Ø a₂} {b₂} (B₂ : A₂ → A₂ → Ø b₂) c₂ ⦃ _ : MorphismEquivalence B₂ c₂ ⦄
-- -- -- -- --   (μ : A₁ → A₂)
-- -- -- -- --   : Ø a₁ ∙̂ b₁ ∙̂ c₁ ∙̂ a₂ ∙̂ b₂ ∙̂ c₂
-- -- -- -- --   where
-- -- -- -- --   field
-- -- -- -- --     ⦃ ⌶IsCategory₁ ⦄ : IsCategory B₁ c₁
-- -- -- -- --     ⦃ ⌶IsCategory₂ ⦄ : IsCategory B₂ c₂
-- -- -- -- --     ⦃ ⌶IsSemifunctor ⦄ : IsSemifunctor B₁ c₁ B₂ c₂ μ
-- -- -- -- --     ⦃ ⌶Identity ⦄ : Identity B₁ B₂ c₂ μ

-- -- -- -- -- record Category a b c : Ø ↑̂ (a ∙̂ b ∙̂ c) where
-- -- -- -- --   field
-- -- -- -- --     Object : Ø a
-- -- -- -- --     Morphism : Object → Object → Ø b
-- -- -- -- --     ⦃ ⌶MorophismEquivalence ⦄ : MorphismEquivalence Morphism c
-- -- -- -- --     ⦃ ⌶IsCategory ⦄ : IsCategory Morphism c

-- -- -- -- -- record Semifunctor a b c d e f : Ø ↑̂ (a ∙̂ b ∙̂ c ∙̂ d ∙̂ e ∙̂ f) where
-- -- -- -- --   field
-- -- -- -- --     Object₁ : Ø a
-- -- -- -- --     Morphism₁ : Object₁ → Object₁ → Ø b
-- -- -- -- --     ⦃ ⌶MorophismEquivalence₁ ⦄ : MorphismEquivalence Morphism₁ c
-- -- -- -- --     Object₂ : Ø d
-- -- -- -- --     Morphism₂ : Object₂ → Object₂ → Ø e
-- -- -- -- --     ⦃ ⌶MorophismEquivalence₂ ⦄ : MorphismEquivalence Morphism₂ f
-- -- -- -- --     μ : Object₁ → Object₂
-- -- -- -- --     ⦃ ⌶IsSemifunctor ⦄ : IsSemifunctor Morphism₁ c Morphism₂ f μ

-- -- -- -- -- record Functor a b c d e f : Ø ↑̂ (a ∙̂ b ∙̂ c ∙̂ d ∙̂ e ∙̂ f) where
-- -- -- -- --   field
-- -- -- -- --     Object₁ : Ø a
-- -- -- -- --     Morphism₁ : Object₁ → Object₁ → Ø b
-- -- -- -- --     ⦃ ⌶MorophismEquivalence₁ ⦄ : MorphismEquivalence Morphism₁ c
-- -- -- -- --     Object₂ : Ø d
-- -- -- -- --     Morphism₂ : Object₂ → Object₂ → Ø e
-- -- -- -- --     ⦃ ⌶MorophismEquivalence₂ ⦄ : MorphismEquivalence Morphism₂ f
-- -- -- -- --     μ : Object₁ → Object₂
-- -- -- -- --     ⦃ ⌶IsFunctor ⦄ : IsFunctor Morphism₁ c Morphism₂ f μ

-- -- -- -- -- module _ where

-- -- -- -- --   record Successor₀ {x} (X : Ø x) : Ø x where
-- -- -- -- --     field
-- -- -- -- --       ⇑₀ : X → X
-- -- -- -- --   open Successor₀ ⦃ … ⦄ public

-- -- -- -- --   record Principal₁ {x} {X : Ø x} {a} (A : X → Ø a) : Ø₀ where no-eta-equality
-- -- -- -- --   record Principal₁₊₁ {x} {X : Ø x} {a} (A : X → Ø a) {b} (B : X → Ø b) : Ø₀ where no-eta-equality

-- -- -- -- --   record Successor₁ {x} {X : Ø x} {a} (A : X → Ø a)
-- -- -- -- --     ⦃ _ : Successor₀ X ⦄
-- -- -- -- --     ⦃ _ : Principal₁ A ⦄
-- -- -- -- --     : Ø x ∙̂ a where
-- -- -- -- --     field
-- -- -- -- --       ⇑₁ : ∀ {m} → A m → A (⇑₀ m)
-- -- -- -- --   open Successor₁ ⦃ … ⦄ public

-- -- -- -- --   record Thin {x} {X : Ø x} {a} (A : X → Ø a) {b} (B : X → Ø b)
-- -- -- -- --     ⦃ _ : Successor₀ X ⦄
-- -- -- -- --     ⦃ _ : Principal₁ A ⦄
-- -- -- -- --     ⦃ _ : Principal₁ B ⦄
-- -- -- -- --     : Ø x ∙̂ a ∙̂ b where
-- -- -- -- --     field
-- -- -- -- --       thin : ∀ {m : X} → A (⇑₀ m) → B m → B (⇑₀ m)
-- -- -- -- --   open Thin ⦃ … ⦄ public

-- -- -- -- --   thin[_] : ∀
-- -- -- -- --     {x} {X : Ø x} {a} {A : X → Ø a} {b} (B : X → Ø b)
-- -- -- -- --     ⦃ _ : Successor₀ X ⦄
-- -- -- -- --     ⦃ _ : Principal₁ A ⦄
-- -- -- -- --     ⦃ _ : Principal₁ B ⦄
-- -- -- -- --     ⦃ _ : Thin A B ⦄
-- -- -- -- --     → ∀ {m : X} → A (⇑₀ m) → B m → B (⇑₀ m)
-- -- -- -- --   thin[ _ ] = thin

-- -- -- -- --   record Injectivity₀
-- -- -- -- --     {a} {A : Ø a}
-- -- -- -- --     {b} {B : Ø b}
-- -- -- -- --     (f : A → B)
-- -- -- -- --     ℓa
-- -- -- -- --     ℓb
-- -- -- -- --     ⦃ _ : Equivalence B ℓb ⦄
-- -- -- -- --     ⦃ _ : Equivalence A ℓa ⦄
-- -- -- -- --     : Ø a ∙̂ b ∙̂ ℓa ∙̂ ℓb where
-- -- -- -- --     field injectivity₀ : ∀ {x y} → f x ≋ f y → x ≋ y
-- -- -- -- --   open Injectivity₀ ⦃ … ⦄ public

-- -- -- -- --   injectivity₀[_] : ∀
-- -- -- -- --     {a} {A : Ø a}
-- -- -- -- --     {b} {B : Ø b}
-- -- -- -- --     (f : A → B)
-- -- -- -- --     {ℓa}
-- -- -- -- --     {ℓb}
-- -- -- -- --     ⦃ _ : Equivalence A ℓa ⦄
-- -- -- -- --     ⦃ _ : Equivalence B ℓb ⦄
-- -- -- -- --     ⦃ _ : Injectivity₀ f ℓa ℓb ⦄
-- -- -- -- --     → ∀ {x y} → f x ≋ f y → x ≋ y
-- -- -- -- --   injectivity₀[ f ] = injectivity₀ { f = f }

-- -- -- -- --   record Injectivity!
-- -- -- -- --     {a} {A : Ø a}
-- -- -- -- --     {b} {B : A → Ø b}
-- -- -- -- --     {c} (C : ∀ x → B x → B x → Ø c)
-- -- -- -- --     {d} (D : ∀ x → B x → B x → Ø d)
-- -- -- -- --     : Ø a ∙̂ b ∙̂ c ∙̂ d where
-- -- -- -- --     field injectivity! : ∀ w {x y : B w} → C w x y → D w x y
-- -- -- -- --   open Injectivity! ⦃ … ⦄ public

-- -- -- -- --   module _
-- -- -- -- --     {a} {A : Ø a}
-- -- -- -- --     {b} {B : A → Ø b}
-- -- -- -- --     {c} {C : A → Ø c}
-- -- -- -- --     (f : (x : A) → B x → C x)
-- -- -- -- --     ℓb
-- -- -- -- --     ℓc
-- -- -- -- --     ⦃ _ : ∀ {x} → Equivalence (B x) ℓb ⦄
-- -- -- -- --     ⦃ _ : ∀ {x} → Equivalence (C x) ℓc ⦄
-- -- -- -- --     where
-- -- -- -- --     Injectivity? = Injectivity! (λ w x y → f w x ≋ f w y) (λ w x y → x ≋ y)

-- -- -- -- --   injectivity?[_] : ∀
-- -- -- -- --     {a} {A : Ø a}
-- -- -- -- --     {b} {B : A → Ø b}
-- -- -- -- --     {c} {C : A → Ø c}
-- -- -- -- --     (f : (x : A) → B x → C x)
-- -- -- -- --     {ℓb}
-- -- -- -- --     {ℓc}
-- -- -- -- --     ⦃ _ : ∀ {x} → Equivalence (B x) ℓb ⦄
-- -- -- -- --     ⦃ _ : ∀ {x} → Equivalence (C x) ℓc ⦄
-- -- -- -- --     ⦃ _ : Injectivity? f ℓb ℓc ⦄
-- -- -- -- --     → ∀ w {x y} → f w x ≋ f w y → x ≋ y
-- -- -- -- --   injectivity?[ _ ] = injectivity!

-- -- -- -- --   record Injectivity₁
-- -- -- -- --     {a} {A : Ø a}
-- -- -- -- --     {b} {B : A → Ø b}
-- -- -- -- --     {c} {C : A → Ø c}
-- -- -- -- --     (f : (x : A) → B x → C x)
-- -- -- -- --     ℓb
-- -- -- -- --     ℓc
-- -- -- -- --     ⦃ _ : ∀ {x} → Equivalence (B x) ℓb ⦄
-- -- -- -- --     ⦃ _ : ∀ {x} → Equivalence (C x) ℓc ⦄
-- -- -- -- --     : Ø a ∙̂ b ∙̂ ℓb ∙̂ ℓc where
-- -- -- -- --     field injectivity₁ : ∀ w {x y} → f w x ≋ f w y → x ≋ y
-- -- -- -- --   open Injectivity₁ ⦃ … ⦄ public

-- -- -- -- --   injectivity₁[_] : ∀
-- -- -- -- --     {a} {A : Ø a}
-- -- -- -- --     {b} {B : A → Ø b}
-- -- -- -- --     {c} {C : A → Ø c}
-- -- -- -- --     (f : (x : A) → B x → C x)
-- -- -- -- --     {ℓb}
-- -- -- -- --     {ℓc}
-- -- -- -- --     ⦃ _ : ∀ {x} → Equivalence (B x) ℓb ⦄
-- -- -- -- --     ⦃ _ : ∀ {x} → Equivalence (C x) ℓc ⦄
-- -- -- -- --     ⦃ _ : Injectivity₁ f ℓb ℓc ⦄
-- -- -- -- --     → ∀ w {x y} → f w x ≋ f w y → x ≋ y
-- -- -- -- --   injectivity₁[ f ] = injectivity₁ {f = f}

-- -- -- -- --   record Injectivity₂
-- -- -- -- --     {a} {A : Ø a}
-- -- -- -- --     {b} {B : Ø b}
-- -- -- -- --     {c} {C : Ø c}
-- -- -- -- --     (f : A → B → C)
-- -- -- -- --     ℓb
-- -- -- -- --     ℓc
-- -- -- -- --     ⦃ _ : Equivalence B ℓb ⦄
-- -- -- -- --     ⦃ _ : Equivalence C ℓc ⦄
-- -- -- -- --     : Ø a ∙̂ b ∙̂ ℓb ∙̂ ℓc where
-- -- -- -- --     field injectivity₂ : ∀ w {x y} → f w x ≋ f w y → x ≋ y
-- -- -- -- --   open Injectivity₂ ⦃ … ⦄ public

-- -- -- -- --   injectivity₂[_] : ∀
-- -- -- -- --     {a} {A : Ø a}
-- -- -- -- --     {b} {B : Ø b}
-- -- -- -- --     {c} {C : Ø c}
-- -- -- -- --     (f : A → B → C)
-- -- -- -- --     {ℓb}
-- -- -- -- --     {ℓc}
-- -- -- -- --     ⦃ _ : Equivalence B ℓb ⦄
-- -- -- -- --     ⦃ _ : Equivalence C ℓc ⦄
-- -- -- -- --     ⦃ _ : Injectivity₂ f ℓb ℓc ⦄
-- -- -- -- --     → ∀ w {x y} → f w x ≋ f w y → x ≋ y
-- -- -- -- --   injectivity₂[ f ] = injectivity₂ {f = f}

-- -- -- -- --   record ThinInjective {x} {X : Ø x} {a} (A : X → Ø a) {b} (B : X → Ø b) c
-- -- -- -- --     ⦃ _ : Successor₀ X ⦄
-- -- -- -- --     ⦃ _ : ∀ {x} → Equivalence (B x) c ⦄
-- -- -- -- --     ⦃ _ : Principal₁ A ⦄
-- -- -- -- --     ⦃ _ : Principal₁ B ⦄
-- -- -- -- --     ⦃ _ : Thin A B ⦄
-- -- -- -- --     : Ø x ∙̂ a ∙̂ b ∙̂ ↑̂ c where
-- -- -- -- --     field
-- -- -- -- --       ⦃ ⌶Injectivity₁ ⦄ : ∀ {m : X} → Injectivity₁ {A = A (⇑₀ m)} {B = λ _ → B _} (λ w x → thin w x) c c
-- -- -- -- --       ⦃ ⌶Injectivity₂ ⦄ : ∀ {m : X} → Injectivity₂ (λ (w : A (⇑₀ m)) x → thin[ B ] w x) c c
-- -- -- -- --       -- (thin[ B ] {m = m})
-- -- -- -- --     thin-injective : ∀ {m : X} (x : A (⇑₀ m)) {y₁ y₂ : B m} → thin x y₁ ≋ thin x y₂ → y₁ ≋ y₂
-- -- -- -- --     thin-injective = injectivity₁[ thin ]
-- -- -- -- --     -- injectivity₂[ thin[ B ] ]
-- -- -- -- --     -- injectivity₁[ thin ]
-- -- -- -- --   open ThinInjective ⦃ … ⦄ public

-- -- -- -- --   record Thick {x} {X : Ø x} {a} (A : X → Ø a) {b} (B : X → Ø b)
-- -- -- -- --     ⦃ _ : Successor₀ X ⦄
-- -- -- -- --     ⦃ _ : Principal₁ B ⦄
-- -- -- -- --     : Ø x ∙̂ a ∙̂ b where
-- -- -- -- --     field
-- -- -- -- --       thick : ∀ {m} → B (⇑₀ m) → A m → B m
-- -- -- -- --   open Thick ⦃ … ⦄ public

-- -- -- -- --   record ThickThinId {x} {X : Ø x} {a} (A : X → Ø a) {b} (B : X → Ø b) c
-- -- -- -- --     ⦃ _ : Successor₀ X ⦄
-- -- -- -- --     ⦃ _ : Principal₁ A ⦄
-- -- -- -- --     ⦃ _ : Principal₁ B ⦄
-- -- -- -- --     ⦃ _ : Successor₁ A ⦄
-- -- -- -- --     ⦃ _ : ∀ {x} → Equivalence (B x) c ⦄
-- -- -- -- --     ⦃ _ : Thin A B ⦄
-- -- -- -- --     ⦃ _ : Thick A B ⦄
-- -- -- -- --     : Ø x ∙̂ a ∙̂ b ∙̂ ↑̂ c where
-- -- -- -- --     field
-- -- -- -- --       thick∘thin=id : ∀ {m} (x : A m) (y : B m) → thick (thin (⇑₁ x) y) x ≋ y
-- -- -- -- --   open ThickThinId ⦃ … ⦄ public

-- -- -- -- --   record Maybe* a : Ø ↑̂ a where
-- -- -- -- --     field
-- -- -- -- --       Maybe : Ø a → Ø a
-- -- -- -- --       just : ∀ {A} → A → Maybe A
-- -- -- -- --       nothing : ∀ {A} → Maybe A
-- -- -- -- --   open Maybe* ⦃ … ⦄ -- public

-- -- -- -- --   record Check {x} {X : Ø x} {a} (A : X → Ø a) {b} (B : X → Ø b)
-- -- -- -- --     ⦃ _ : Successor₀ X ⦄
-- -- -- -- --     ⦃ _ : Principal₁ A ⦄
-- -- -- -- --     ⦃ _ : Principal₁ B ⦄
-- -- -- -- --     ⦃ _ : Maybe* b ⦄
-- -- -- -- --     : Ø x ∙̂ a ∙̂ ↑̂ b where
-- -- -- -- --     field
-- -- -- -- --       check : ∀ {m} → A (⇑₀ m) → B (⇑₀ m) → Maybe (B m)
-- -- -- -- --   open Check ⦃ … ⦄ public

-- -- -- -- --   record ThinCheckId {x} {X : Ø x} {a} (A : X → Ø a) {b} (B : X → Ø b) ℓb ℓc
-- -- -- -- --     ⦃ _ : Successor₀ X ⦄
-- -- -- -- --     ⦃ _ : Maybe* b ⦄
-- -- -- -- --     ⦃ _ : ∀ {x} → Equivalence (B x) ℓb ⦄
-- -- -- -- --     ⦃ _ : ∀ {x} → Equivalence (Maybe (B x)) ℓc ⦄
-- -- -- -- --     ⦃ _ : Principal₁ A ⦄
-- -- -- -- --     ⦃ _ : Principal₁ B ⦄
-- -- -- -- --     ⦃ _ : Thin A B ⦄
-- -- -- -- --     ⦃ _ : Check A B ⦄
-- -- -- -- --     : Ø x ∙̂ a ∙̂ b ∙̂ ℓb ∙̂ ℓc where
-- -- -- -- --     field
-- -- -- -- --       thin-check-id : ∀ {m} (x : A (⇑₀ m)) y → ∀ (y' : B m) → thin x y' ≋ y → check x y ≋ just y'
-- -- -- -- --   open ThinCheckId ⦃ … ⦄ public

-- -- -- -- --   test-thin-check-id : ∀ {x} {X : Ø x} {a} (A : X → Ø a) {b} (B : X → Ø b) ℓb ℓc
-- -- -- -- --                          ⦃ _ : Successor₀ X ⦄
-- -- -- -- --                          ⦃ _ : ∀ {x} → Equivalence (B x) ℓb ⦄
-- -- -- -- --                          ⦃ _ : Maybe* b ⦄
-- -- -- -- --                          ⦃ _ : ∀ {x} → Equivalence (Maybe (B x)) ℓc ⦄
-- -- -- -- --                          ⦃ _ : Principal₁ A ⦄
-- -- -- -- --                          ⦃ _ : Principal₁ B ⦄
-- -- -- -- --                          ⦃ _ : Thin A B ⦄
-- -- -- -- --                          ⦃ _ : Check A B ⦄
-- -- -- -- --                          ⦃ _ : ThinCheckId A B ℓb ℓc ⦄
-- -- -- -- --                          → ∀ {m} (x : A (⇑₀ m)) y → ∀ (y' : B m) → thin x y' ≋ y → check x y ≋ just y'
-- -- -- -- --   test-thin-check-id A B ℓb ℓc = thin-check-id

-- -- -- -- --   record ThickAndThin {x} {X : Ø x} {a} (A : X → Ø a) {b} (B : X → Ø b) c ℓc
-- -- -- -- --     ⦃ _ : Successor₀ X ⦄
-- -- -- -- --     ⦃ _ : Principal₁ A ⦄
-- -- -- -- --     ⦃ _ : Principal₁ B ⦄
-- -- -- -- --     ⦃ _ : Successor₁ A ⦄
-- -- -- -- --     ⦃ _ : Maybe* b ⦄
-- -- -- -- --     ⦃ _ : ∀ {x} → Equivalence (B x) c ⦄
-- -- -- -- --     ⦃ _ : ∀ {x} → Equivalence (Maybe (B x)) ℓc ⦄
-- -- -- -- --     : Ø x ∙̂ a ∙̂ ↑̂ b ∙̂ ↑̂ c ∙̂ ↑̂ ℓc where
-- -- -- -- --     field
-- -- -- -- --       ⦃ iThin ⦄ : Thin A B
-- -- -- -- --       ⦃ iThinInjective ⦄ : ThinInjective A B c
-- -- -- -- --       ⦃ iThick ⦄ : Thick A B
-- -- -- -- --       ⦃ iThickThinId ⦄ : ThickThinId A B c
-- -- -- -- --       ⦃ iCheck ⦄ : Check A B
-- -- -- -- --       ⦃ iThinCheckId ⦄ : ThinCheckId A B c ℓc
-- -- -- -- --   open ThickAndThin ⦃ … ⦄

-- -- -- -- -- module _ where

-- -- -- -- --   record FMap {x} {y} (F : Ø x → Ø y) : Ø (↑̂ x) ∙̂ y where
-- -- -- -- --     field fmap : ∀ {A B : Ø x} → (A → B) → F A → F B
