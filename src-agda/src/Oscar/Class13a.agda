{-# OPTIONS --show-implicit #-}
{-# OPTIONS --postfix-projections #-}
module Oscar.Class where

open import Oscar.Prelude

module _ where

  module _
    {a} {A : Ø a}
    {b} (_⊸_ : A → A → Ø b)
    where
    𝓻eflexivity∁ = ∀ {x} → x ⊸ x
    record 𝓡eflexivity∁ : Ø a ∙̂ b where field reflexivity : 𝓻eflexivity∁
  open 𝓡eflexivity∁ ⦃ … ⦄ public

  module _ where

    ε = reflexivity

    ε[_] : ∀
      {a} {A : Ø a}
      {b} (_⊸_ : A → A → Ø b)
      ⦃ _ : 𝓡eflexivity∁ _⊸_ ⦄
      → ∀ {x} → x ⊸ x
    ε[ _ ] = reflexivity

module _ where

  module _
    {a} {A : Ø a}
    {b} (_⊸_ : A → A → Ø b)
    where
    𝓼ymmetry∁ = ∀ {x y} → x ⊸ y → y ⊸ x
    record 𝓢ymmetry∁ : Ø a ∙̂ b where field symmetry : 𝓼ymmetry∁
  open 𝓢ymmetry∁ ⦃ … ⦄ public

module _ where

  module _
    {a} {A : Ø a}
    {b} (_⊸_ : A → A → Ø b)
    where
    𝓽ransitivity∁ = ∀ {x y z} → x ⊸ y → y ⊸ z → x ⊸ z
    record 𝓣ransitivity∁ : Ø a ∙̂ b where field transitivity : 𝓽ransitivity∁
  open 𝓣ransitivity∁ ⦃ … ⦄ public

  module _
    {a} {A : Ø a}
    {b} (_⊸_ : A → A → Ø b)
    where
    𝓬ompositionality∁ = ∀ {x y z} → y ⊸ z → x ⊸ y → x ⊸ z
    record 𝓒ompositionality∁ : Ø a ∙̂ b where
      infixr 9 _∙_
      field _∙_ : ∀ {x y z} → y ⊸ z → x ⊸ y → x ⊸ z
  open 𝓒ompositionality∁ ⦃ … ⦄ public

  instance
    T→C : ∀
      {a} {A : Ø a}
      {b} {_⊸_ : A → A → Ø b}
      ⦃ _ : 𝓣ransitivity∁ _⊸_ ⦄ → 𝓒ompositionality∁ _⊸_
    T→C {a} {A₁} {b} {_⊸₁_} {{x}} .𝓒ompositionality∁._∙_ g f = transitivity f g

module _ where

  module _
    {a} {A : Ø a}
    {m} (_⊸_ : A → A → Ø m)
    {ℓ} (_≋_ : ∀ {x y} → x ⊸ y → x ⊸ y → Ø ℓ)
    where
    module _
      (_∙_ : 𝓬ompositionality∁ _⊸_)
      -- ⦃ _ : 𝓣ransitivity∁ _⊸_ ⦄
      where
      𝓽ransextensionality/ = ∀ {x y z} {f₁ f₂ : x ⊸ y} {g₁ g₂ : y ⊸ z} → f₁ ≋ f₂ → g₁ ≋ g₂ → (g₁ ∙ f₁) ≋ (g₂ ∙ f₂)
    record 𝓣ransextensionality∁ : Ø a ∙̂ m ∙̂ ℓ where
      field
        ⦃ ⌶𝓣ransitivity∁ ⦄ : 𝓣ransitivity∁ _⊸_
        transextensionality : 𝓽ransextensionality/ _∙_
  open 𝓣ransextensionality∁ ⦃ … ⦄ public using (transextensionality)

  module _
    {a} {A : Ø a}
    {m} (_⊸_ : A → A → Ø m)
    {ℓ} (_≋_ : ∀ {x y} → x ⊸ y → x ⊸ y → Ø ℓ)
    where
    module _
      (_∙_ : 𝓬ompositionality∁ _⊸_)
      where
      𝓽ransassociativity/ = ∀ {w x y z} (f : w ⊸ x) (g : x ⊸ y) (h : y ⊸ z) → ((h ∙ g) ∙ f) ≋ (h ∙ (g ∙ f))
    record 𝓣ransassociativity∁ : Ø a ∙̂ m ∙̂ ℓ where
      field
        ⦃ ⌶𝓣ransitivity∁ ⦄ : 𝓣ransitivity∁ _⊸_
        transassociativity : 𝓽ransassociativity/ _∙_
  open 𝓣ransassociativity∁ ⦃ … ⦄ public using (transassociativity)

-- module _ where

--   module _
--     {a₁} {A₁ : Ø a₁}
--     {m₁} (_⊸₁_ : A₁ → A₁ → Ø m₁)
--     {a₂} {A₂ : Ø a₂}
--     {m₂} (_⊸₂_ : A₂ → A₂ → Ø m₂)
--     where
--     module _
--       (μ : A₁ → A₂)
--       where
--       𝓶ap/ = ∀ {x y} → x ⊸₁ y → μ x ⊸₂ μ y
--     record 𝓜ap∁ : Ø a₁ ∙̂ m₁ ∙̂ a₂ ∙̂ m₂ where
--       field
--         μ : A₁ → A₂
--         map : 𝓶ap/ μ
--   open 𝓜ap∁ ⦃ … ⦄ public using (map)

--   module _ where

--     map[_] : ∀
--       {a₁} {A₁ : Ø a₁}
--       {m₁} {_⊸₁_ : A₁ → A₁ → Ø m₁}
--       {a₂} {A₂ : Ø a₂}
--       {m₂} (_⊸₂_ : A₂ → A₂ → Ø m₂)
--       ⦃ ⌶𝓜ap∁ : 𝓜ap∁ _⊸₁_ _⊸₂_ ⦄
--       → ∀ {x y} → x ⊸₁ y → 𝓜ap∁.μ ⌶𝓜ap∁ x ⊸₂ 𝓜ap∁.μ ⌶𝓜ap∁ y
--     map[ _ ] = map

-- module _ where

--   module _
--     {a₁} {A₁ : Ø a₁}
--     {m₁} (_⊸₁_ : A₁ → A₁ → Ø m₁)
--     {ℓ₁} (_≋₁_ : ∀ {x y} → x ⊸₁ y → x ⊸₁ y → Ø ℓ₁)
--     {a₂} {A₂ : Ø a₂}
--     {m₂} (_⊸₂_ : A₂ → A₂ → Ø m₂)
--     {ℓ₂} (_≋₂_ : ∀ {x y} → x ⊸₂ y → x ⊸₂ y → Ø ℓ₂)
--     where
--     module _
--       ⦃ _ : 𝓜ap∁ _⊸₁_ _⊸₂_ ⦄
--       where
--       𝓶apextensionality/ = ∀ {x y} {f₁ f₂ : x ⊸₁ y} → f₁ ≋₁ f₂ → map f₁ ≋₂ map f₂
--     record 𝓜apextensionality∁ : Ø a₁ ∙̂ m₁ ∙̂ a₂ ∙̂ m₂ ∙̂ ℓ₁ ∙̂ ℓ₂ where
--       field
--         ⦃ ⌶𝓜ap∁ ⦄ : 𝓜ap∁ _⊸₁_ _⊸₂_
--         mapextensionality : 𝓶apextensionality/
--   open 𝓜apextensionality∁ ⦃ … ⦄ public using (mapextensionality)

-- module _ where

--   module _
--     {a₁} {A₁ : Ø a₁}
--     {m₁} (_⊸₁_ : A₁ → A₁ → Ø m₁)
--     {a₂} {A₂ : Ø a₂}
--     {m₂} (_⊸₂_ : A₂ → A₂ → Ø m₂)
--     {ℓ₂} (_≋₂_ : ∀ {x y} → x ⊸₂ y → x ⊸₂ y → Ø ℓ₂)
--     where
--     module _
--       ⦃ _ : 𝓜ap∁ _⊸₁_ _⊸₂_ ⦄
--       ⦃ _ : 𝓣ransitivity∁ _⊸₁_ ⦄
--       ⦃ _ : 𝓣ransitivity∁ _⊸₂_ ⦄
--       where
--       𝓶aptranscommutativity/ = ∀ {x y z} (f : x ⊸₁ y) (g : y ⊸₁ z) → map (g ∙ f) ≋₂ (map g ∙ map f)
--     record 𝓜aptranscommutativity∁ : Ø a₁ ∙̂ a₂ ∙̂ m₁ ∙̂ m₂ ∙̂ ℓ₂ where
--       field
--         ⦃ ⌶𝓜ap∁ ⦄ : 𝓜ap∁ _⊸₁_ _⊸₂_
--         ⦃ ⌶𝓣ransitivity∁₁ ⦄ : 𝓣ransitivity∁ _⊸₁_
--         ⦃ ⌶𝓣ransitivity∁₂ ⦄ : 𝓣ransitivity∁ _⊸₂_
--         maptranscommutativity : 𝓶aptranscommutativity/
--   open 𝓜aptranscommutativity∁ ⦃ … ⦄ public using (maptranscommutativity)

-- module _ where

--   module _
--     {o} {Object : Ø o}
--     {a} (Arrow : Object → Object → Ø a)
--     {ℓ} (ArrowEquivalent : ∀ {x y} → Arrow x y → Arrow x y → Ø ℓ)
--     where
--     module _
--       ⦃ _ : 𝓡eflexivity∁ Arrow ⦄
--       ⦃ _ : 𝓣ransitivity∁ Arrow ⦄
--       where
--       𝓽ransleftidentity/ = ∀ {x y} {f : Arrow x y} → ArrowEquivalent (ε ∙ f) f
--     record 𝓣ransleftidentity∁ : Ø o ∙̂ a ∙̂ ℓ where
--       field
--         ⦃ ⌶𝓡eflexivity∁ ⦄ : 𝓡eflexivity∁ Arrow
--         ⦃ ⌶𝓣ransitivity∁ ⦄ : 𝓣ransitivity∁ Arrow
--         transleftidentity : 𝓽ransleftidentity/
--   open 𝓣ransleftidentity∁ ⦃ … ⦄ public using (transleftidentity)

--   module _
--     {o} {Object : Ø o}
--     {a} (Arrow : Object → Object → Ø a)
--     {ℓ} (ArrowEquivalent : ∀ {x y} → Arrow x y → Arrow x y → Ø ℓ)
--     where
--     module _
--       ⦃ _ : 𝓡eflexivity∁ Arrow ⦄
--       ⦃ _ : 𝓣ransitivity∁ Arrow ⦄
--       where
--       𝓽ransrightidentity/ = ∀ {x y} {f : Arrow x y} → ArrowEquivalent (f ∙ ε) f
--     record 𝓣ransrightidentity∁ : Ø o ∙̂ a ∙̂ ℓ where
--       field
--         ⦃ ⌶𝓡eflexivity∁ ⦄ : 𝓡eflexivity∁ Arrow
--         ⦃ ⌶𝓣ransitivity∁ ⦄ : 𝓣ransitivity∁ Arrow
--         transrightidentity : 𝓽ransrightidentity/
--   open 𝓣ransrightidentity∁ ⦃ … ⦄ public using (transrightidentity)

-- module _ where

--   module _
--     {o₁} {Object₁ : Ø o₁}
--     {a₁} (Arrow₁ : Object₁ → Object₁ → Ø a₁)
--     {o₂} {Object₂ : Ø o₂}
--     {a₂} (Arrow₂ : Object₂ → Object₂ → Ø a₂)
--     {ℓ₂} (ArrowEquivalent₂ : ∀ {x y} → Arrow₂ x y → Arrow₂ x y → Ø ℓ₂)
--     where
--     module _
--       ⦃ _ : 𝓜ap∁ Arrow₁ Arrow₂ ⦄
--       ⦃ _ : 𝓡eflexivity∁ Arrow₁ ⦄
--       ⦃ _ : 𝓡eflexivity∁ Arrow₂ ⦄
--       where
--       𝓶apidentity/ = ∀ {x} → ArrowEquivalent₂ (map (ε[ Arrow₁ ] {x})) ε
--     record 𝓜apidentity∁ : Ø o₁ ∙̂ a₁ ∙̂ o₂ ∙̂ a₂ ∙̂ ℓ₂ where
--       field
--         ⦃ ⌶𝓜ap∁ ⦄ : 𝓜ap∁ Arrow₁ Arrow₂
--         ⦃ ⌶𝓡eflexivity∁₁ ⦄ : 𝓡eflexivity∁ Arrow₁
--         ⦃ ⌶𝓡eflexivity∁₂ ⦄ : 𝓡eflexivity∁ Arrow₂
--         mapidentity : 𝓶apidentity/
--   open 𝓜apidentity∁ ⦃ … ⦄ public using (mapidentity)





module _ where

  record IsEquivalence∁
    {a} {A : Ø a}
    {b} (_⊸_ : A → A → Ø b)
    : Ø a ∙̂ b where
    field
      ⦃ ⌶𝓡eflexivity∁ ⦄ : 𝓡eflexivity∁ _⊸_
      ⦃ ⌶𝓢ymmetry∁ ⦄ : 𝓢ymmetry∁ _⊸_
      ⦃ ⌶𝓣ransitivity∁ ⦄ : 𝓣ransitivity∁ _⊸_

open import Oscar.Data

module _ where

  record Precategory o a ℓ : Ø ↑̂ (o ∙̂ a ∙̂ ℓ) where
    field
      Object : Ø o
      Arrow : Object → Object → Ø a
      ArrowEquivalent : ∀ {x y} → Arrow x y → Arrow x y → Ø ℓ
      ⌶IsEquivalence∁ : ∀ {x y} → IsEquivalence∁ (ArrowEquivalent {x} {y})
      compositionalityArrow : 𝓬ompositionality∁ Arrow
      ⌶𝓣ransextensionality∁ : 𝓽ransextensionality∁ Arrow ArrowEquivalent compositionalityArrow
      ⌶𝓣ransassociativity∁ : 𝓽ransassociativity∁ Arrow ArrowEquivalent compositionalityArrow

  record IsPrecategory∁
    {o} {Object : Ø o}
    {a} (Arrow : Object → Object → Ø a)
    {ℓ} (ArrowEquivalent : ∀ {x y} → Arrow x y → Arrow x y → Ø ℓ)
    ⦃ _ : ∀ {x y} → IsEquivalence∁ (ArrowEquivalent {x} {y}) ⦄
    ⦃ ⌶T : 𝓣ransitivity∁ Arrow ⦄
    ⦃ ⌶X : 𝓣ransextensionality∁ Arrow ArrowEquivalent ⦄
    ⦃ ⌶A : 𝓣ransassociativity∁ Arrow ArrowEquivalent ⦄
    ⦃ _ : ⌶T ≡ 𝓣ransextensionality∁.⌶𝓣ransitivity∁ ⌶X ⦄
    ⦃ _ : ⌶T ≡ 𝓣ransassociativity∁.⌶𝓣ransitivity∁ ⌶A ⦄
    : Ø₀ where

  postulate
    A : Set
    F : A → A → Set
    _≋F_ : ∀ {x y} → F x y → F x y → Set
    instance _ : 𝓣ransitivity∁ F
    instance _ : ∀ {x y} → IsEquivalence∁ (_≋F_ {x} {y})

  instance TX : 𝓣ransextensionality∁ F _≋F_
  TX .𝓣ransextensionality∁.⌶𝓣ransitivity∁ = !
  TX .𝓣ransextensionality∁.transextensionality = {!!}

  instance TA : 𝓣ransassociativity∁ F _≋F_
  TA .𝓣ransassociativity∁.⌶𝓣ransitivity∁ = !
  TA .𝓣ransassociativity∁.transassociativity = {!!}

  _ = IsPrecategory∁ F _≋F_ ∋ record {}



--       ⦃ ⌶IsEquivalence∁ ⦄ : ∀ {x y} → IsEquivalence∁ (ArrowEquivalent {x} {y})
--       -- ⦃ ⌶𝓣ransitivity∁ ⦄ : 𝓣ransitivity∁ Arrow
--       ⦃ ⌶𝓣ransitivity ⦄ : 𝓣ransitivity∁ Arrow
--       ⦃ ⌶𝓣ransextensionality ⦄ : 𝓣ransextensionality∁ Arrow ArrowEquivalent
--       ⦃ ⌶transassociativity : 𝓽ransassociativity/ Arrow ArrowEquivalent

--   record Precategory o a ℓ : Ø ↑̂ (o ∙̂ a ∙̂ ℓ) where
--     field
--       Object : Ø o
--       Arrow : Object → Object → Ø a
--       ArrowEquivalent : ∀ {x y} → Arrow x y → Arrow x y → Ø ℓ
--       ⦃ ⌶IsEquivalence∁ ⦄ : ∀ {x y} → IsEquivalence∁ (ArrowEquivalent {x} {y})
--       ⦃ ⌶𝓣ransitivity∁ ⦄ : 𝓣ransitivity∁ Arrow
--       ⦃ ⌶𝓣ransextensionality∁ ⦄ : 𝓣ransextensionality∁ Arrow ArrowEquivalent
--       ⦃ ⌶𝓣ransassociativity∁ ⦄ : 𝓣ransassociativity∁ Arrow ArrowEquivalent
--       =Exten : ⌶𝓣ransitivity∁ ≡

-- --   record Precategory∁
-- --     {o}
-- --     {a}
-- --     {ℓ}
-- --     : Ø o ∙̂ a ∙̂ ℓ where
-- --     field
-- --       Object : Ø o
-- --       Arrow : Object → Object → Ø a
-- --       ArrowEquivalent : ∀ {x y} → Arrow x y → Arrow x y → Ø ℓ



-- --   record IsPrecategory∁'
-- --     {o} {Object : Ø o}
-- --     {a} (Arrow : Object → Object → Ø a)
-- --     {ℓ} (ArrowEquivalent : ∀ {x y} → Arrow x y → Arrow x y → Ø ℓ)
-- --     : Ø o ∙̂ a ∙̂ ℓ where
-- --     field
-- --       ⦃ ⌶IsEquivalence∁ ⦄ : ∀ {x y} → IsEquivalence∁ (ArrowEquivalent {x} {y})
-- --       -- ⦃ ⌶𝓣ransitivity∁ ⦄ : 𝓣ransitivity∁ Arrow
-- --       ⦃ ⌶𝓣ransitivity ⦄ : 𝓣ransitivity∁ Arrow
-- --       ⦃ ⌶𝓣ransextensionality ⦄ : 𝓣ransextensionality∁ Arrow ArrowEquivalent
-- --       ⦃ ⌶transassociativity : 𝓽ransassociativity/ Arrow ArrowEquivalent

-- --   record IsPrecategory∁
-- --     {o} {Object : Ø o}
-- --     {a} (Arrow : Object → Object → Ø a)
-- --     {ℓ} (ArrowEquivalent : ∀ {x y} → Arrow x y → Arrow x y → Ø ℓ)
-- --     : Ø o ∙̂ a ∙̂ ℓ where
-- --     field
-- --       ⦃ ⌶IsEquivalence∁ ⦄ : ∀ {x y} → IsEquivalence∁ (ArrowEquivalent {x} {y})
-- --       -- ⦃ ⌶𝓣ransitivity∁ ⦄ : 𝓣ransitivity∁ Arrow
-- --       compositionality : 𝓬ompositionality∁ Arrow
-- --       transextensionality : 𝓽ransextensionality/ Arrow ArrowEquivalent compositionality
-- --       transassociativity : 𝓽ransassociativity/ Arrow ArrowEquivalent compositionality

-- -- --   record IsPrefunctor∁
-- -- --     {o₁} {Object₁ : Ø o₁}
-- -- --     {a₁} (Arrow₁ : Object₁ → Object₁ → Ø a₁)
-- -- --     {ℓ₁} (ArrowEquivalent₁ : ∀ {x y} → Arrow₁ x y → Arrow₁ x y → Ø ℓ₁)
-- -- --     {o₂} {Object₂ : Ø o₂}
-- -- --     {a₂} (Arrow₂ : Object₂ → Object₂ → Ø a₂)
-- -- --     {ℓ₂} (ArrowEquivalent₂ : ∀ {x y} → Arrow₂ x y → Arrow₂ x y → Ø ℓ₂)
-- -- --     : Ø o₁ ∙̂ a₁ ∙̂ ℓ₁ ∙̂ o₂ ∙̂ a₂ ∙̂ ℓ₂ where
-- -- --     field
-- -- --       ⦃ ⌶IsPrecategory∁₁ ⦄ : IsPrecategory∁ Arrow₁ ArrowEquivalent₁
-- -- --       ⦃ ⌶IsPrecategory∁₂ ⦄ : IsPrecategory∁ Arrow₂ ArrowEquivalent₂
-- -- --       ⦃ ⌶𝓜ap∁ ⦄ : 𝓜ap∁ Arrow₁ Arrow₂
-- -- --       ⌶𝓜apextensionality/ : 𝓶apextensionality/ Arrow₁ ArrowEquivalent₁ Arrow₂ ArrowEquivalent₂
-- -- --       ⌶𝓜aptranscommutativity/ : 𝓶aptranscommutativity/ Arrow₁ Arrow₂ ArrowEquivalent₂

-- -- --   module _
-- -- --     {o} {Object : Ø o}
-- -- --     {a} (Arrow : Object → Object → Ø a)
-- -- --     {ℓ} (ArrowEquivalent : ∀ {x y} → Arrow x y → Arrow x y → Ø ℓ)
-- -- --     where
-- -- --     module _
-- -- --       ⦃ _ : IsPrecategory∁ Arrow ArrowEquivalent ⦄
-- -- --       where
-- -- --       record IsCategory/ : Ø o ∙̂ a ∙̂ ℓ where
-- -- --         field
-- -- --           ⦃ ⌶𝓡eflexivity∁ ⦄ : 𝓡eflexivity∁ Arrow
-- -- --           ⌶𝓣ransleftidentity/ : 𝓽ransleftidentity/ Arrow ArrowEquivalent
-- -- --           ⌶𝓣ransrightidentity/ : 𝓽ransrightidentity/ Arrow ArrowEquivalent
-- -- --     record IsCategory∁ : Ø o ∙̂ a ∙̂ ℓ where
-- -- --       field
-- -- --         ⦃ ⌶IsPrecategory∁ ⦄ : IsPrecategory∁ Arrow ArrowEquivalent
-- -- --         ⦃ ⌶IsCategory/ ⦄ : IsCategory/

-- -- --   record IsFunctor∁
-- -- --     {o₁} {Object₁ : Ø o₁}
-- -- --     {a₁} (Arrow₁ : Object₁ → Object₁ → Ø a₁)
-- -- --     {ℓ₁} (ArrowEquivalent₁ : ∀ {x y} → Arrow₁ x y → Arrow₁ x y → Ø ℓ₁)
-- -- --     {o₂} {Object₂ : Ø o₂}
-- -- --     {a₂} (Arrow₂ : Object₂ → Object₂ → Ø a₂)
-- -- --     {ℓ₂} (ArrowEquivalent₂ : ∀ {x y} → Arrow₂ x y → Arrow₂ x y → Ø ℓ₂)
-- -- --     : Ø o₁ ∙̂ a₁ ∙̂ ℓ₁ ∙̂ o₂ ∙̂ a₂ ∙̂ ℓ₂ where
-- -- --     field
-- -- --       ⦃ ⌶IsPrefunctor∁ ⦄ : IsPrefunctor∁ Arrow₁ ArrowEquivalent₁ Arrow₂ ArrowEquivalent₂
-- -- --       ⦃ ⌶IsCategory/₁ ⦄ : IsCategory/ Arrow₁ ArrowEquivalent₁
-- -- --       ⦃ ⌶IsCategory/₂ ⦄ : IsCategory/ Arrow₂ ArrowEquivalent₂
-- -- --       ⌶𝓜apidentity/ : 𝓶apidentity/ Arrow₁ Arrow₂ ArrowEquivalent₂




-- -- -- module _ where

-- -- --   record Setoid o ℓ : Ø ↑̂ (o ∙̂ ℓ) where
-- -- --     field
-- -- --       Object : Ø o
-- -- --       ObjectEquality : Object → Object → Ø ℓ
-- -- --       ⦃ ⌶IsEquivalence∁ ⦄ : IsEquivalence∁ ObjectEquality

-- -- --   record Precategory o a ℓ : Ø ↑̂ (o ∙̂ a ∙̂ ℓ) where
-- -- --     field
-- -- --       Object : Ø o
-- -- --       Arrow : Object → Object → Ø a
-- -- --       ArrowEquivalent : ∀ {x y} → Arrow x y → Arrow x y → Ø ℓ
-- -- --       ⦃ ⌶IsPrecategory∁ ⦄ : IsPrecategory∁ Arrow ArrowEquivalent

-- -- --   record Prefunctor o₁ a₁ ℓ₁ o₂ a₂ ℓ₂ : Ø ↑̂ (o₁ ∙̂ a₁ ∙̂ ℓ₁ ∙̂ o₂ ∙̂ a₂ ∙̂ ℓ₂) where
-- -- --     field
-- -- --       Object₁ : Ø o₁
-- -- --       Arrow₁ : Object₁ → Object₁ → Ø a₁
-- -- --       ArrowEquivalent₁ : ∀ {x y} → Arrow₁ x y → Arrow₁ x y → Ø ℓ₁
-- -- --       Object₂ : Ø o₂
-- -- --       Arrow₂ : Object₂ → Object₂ → Ø a₂
-- -- --       ArrowEquivalent₂ : ∀ {x y} → Arrow₂ x y → Arrow₂ x y → Ø ℓ₂
-- -- --       ⦃ ⌶IsPrefunctor∁ ⦄ : IsPrefunctor∁ Arrow₁ ArrowEquivalent₁ Arrow₂ ArrowEquivalent₂

-- -- --   record Category o a ℓ : Ø ↑̂ (o ∙̂ a ∙̂ ℓ) where
-- -- --     field
-- -- --       Object : Ø o
-- -- --       Arrow : Object → Object → Ø a
-- -- --       ArrowEquivalent : ∀ {x y} → Arrow x y → Arrow x y → Ø ℓ
-- -- --       ⦃ ⌶IsCategory∁ ⦄ : IsCategory∁ Arrow ArrowEquivalent

-- -- --   record Functor o₁ a₁ ℓ₁ o₂ a₂ ℓ₂ : Ø ↑̂ (o₁ ∙̂ a₁ ∙̂ ℓ₁ ∙̂ o₂ ∙̂ a₂ ∙̂ ℓ₂) where
-- -- --     field
-- -- --       Object₁ : Ø o₁
-- -- --       Arrow₁ : Object₁ → Object₁ → Ø a₁
-- -- --       ArrowEquivalent₁ : ∀ {x y} → Arrow₁ x y → Arrow₁ x y → Ø ℓ₁
-- -- --       Object₂ : Ø o₂
-- -- --       Arrow₂ : Object₂ → Object₂ → Ø a₂
-- -- --       ArrowEquivalent₂ : ∀ {x y} → Arrow₂ x y → Arrow₂ x y → Ø ℓ₂
-- -- --       ⦃ ⌶IsFunctor∁ ⦄ : IsFunctor∁ Arrow₁ ArrowEquivalent₁ Arrow₂ ArrowEquivalent₂









-- -- -- module _ where

-- -- --   record HasEquivalence {o} (Object : Ø o) ℓ : Ø o ∙̂ ↑̂ ℓ where
-- -- --     field
-- -- --       Equivalent : Object → Object → Ø ℓ
-- -- --       ⦃ ⌶IsEquivalence∁ ⦄ : IsEquivalence∁ Equivalent

-- -- --   module _ where

-- -- --     infix 4 _≈_
-- -- --     _≈_ : ∀ {o} {Object : Ø o} {ℓ} ⦃ _ : HasEquivalence Object ℓ ⦄ → Object → Object → Ø ℓ
-- -- --     _≈_ = HasEquivalence.Equivalent !








-- -- -- module _ where

-- -- --   record 𝓒ongruity∁
-- -- --     a b {c} (C : ∀ {x} {X : Ø x} → X → X → Ø c)
-- -- --     : Ø ↑̂ (a ∙̂ b ∙̂ c) where
-- -- --     field congruity : ∀ {A : Ø a} {B : Ø b} {x y} (f : A → B) → C x y → C (f x) (f y)

-- -- --   open 𝓒ongruity∁ ⦃ … ⦄ public

-- -- -- module _ where

-- -- --   record 𝓒ongruity₂∁
-- -- --     a b c {ℓ} (EQ : ∀ {x} {X : Ø x} → X → X → Ø ℓ)
-- -- --     : Ø ↑̂ (a ∙̂ b ∙̂ c) ∙̂ ℓ where
-- -- --     field congruity₂ : ∀ {A : Ø a} {B : Ø b} {C : Ø c} {x y} {x' y'} (f : A → B → C) → EQ x y → EQ x' y' → EQ (f x x') (f y y')

-- -- --   open 𝓒ongruity₂∁ ⦃ … ⦄ public

-- -- -- module _ where

-- -- --   record 𝓒̇ongruity∁
-- -- --     𝔬 𝔭 {c}
-- -- --     (C : ∀ {𝔒 : Ø 𝔬} {𝔓 : 𝔒 → Ø 𝔭} → ((𝓞 : 𝔒) → 𝔓 𝓞) → ((𝓞 : 𝔒) → 𝔓 𝓞) → Ø c)
-- -- --     : Ø ↑̂ (𝔬 ∙̂ 𝔭) ∙̂ c where
-- -- --     field ċongruity : ∀ {𝔒 : Ø 𝔬} {𝔓 : 𝔒 → Ø 𝔭} {f g : (𝓞 : 𝔒) → 𝔓 𝓞} (F : ∀ {𝓞 : 𝔒} → 𝔓 𝓞 → 𝔓 𝓞) → C f g → C (F ∘ f) (F ∘ g)

-- -- --   open 𝓒̇ongruity∁ ⦃ … ⦄ public



-- -- -- module _ where

-- -- --   module _
-- -- --     {x} (X : Ø x)
-- -- --     where
-- -- --     𝓼uccessor₀∁ = X → X
-- -- --     record 𝓢uccessor₀∁ : Ø x where field successor₀ : 𝓼uccessor₀∁
-- -- --   open 𝓢uccessor₀∁ ⦃ … ⦄ public

-- -- --   ⇑₀ = successor₀

-- -- --   module _
-- -- --     {x} {X : Ø x} {a} (A : X → Ø a)
-- -- --     where
-- -- --     module _
-- -- --       ⦃ _ : 𝓢uccessor₀∁ X ⦄
-- -- --       where
-- -- --       𝓼uccessor₁/ = ∀ {m} → A m → A (⇑₀ m)
-- -- --       record 𝓢uccessor₁/ : Ø x ∙̂ a where field successor₁ : 𝓼uccessor₁/
-- -- --     record 𝓢uccessor₁∁ : Ø x ∙̂ a where
-- -- --       field
-- -- --         ⦃ ⌶𝓢uccessor₀∁ ⦄ : 𝓢uccessor₀∁ X
-- -- --         ⦃ ⌶𝓢uccessor₁/ ⦄ : 𝓢uccessor₁/
-- -- --       open 𝓢uccessor₁/ ⌶𝓢uccessor₁/ public
-- -- --   open 𝓢uccessor₁∁ ⦃ … ⦄ public using (successor₁)

-- -- --   ⇑₁ = successor₁

-- -- --   module _
-- -- --     {a} (A : Ø a)
-- -- --     {b} (B : Ø b)
-- -- --     {ℓa} (_≈A_ : A → A → Ø ℓa)
-- -- --     {ℓb} (_≈B_ : B → B → Ø ℓb)
-- -- --     where
-- -- --     module _
-- -- --       (f : A → B)
-- -- --       where
-- -- --       𝓲njectivity/ = ∀ {x y} → f x ≈B f y → x ≈A y
-- -- --       record 𝓘njectivity/ : Ø a ∙̂ b ∙̂ ℓa ∙̂ ℓb where field injectivity : 𝓲njectivity/
-- -- --     record 𝓘njectivity∁ : Ø a ∙̂ b ∙̂ ℓa ∙̂ ℓb where
-- -- --       field
-- -- --         f : A → B
-- -- --         ⦃ ⌶𝓘njectivity/ ⦄ : 𝓘njectivity/ f
-- -- --       open 𝓘njectivity/ ⌶𝓘njectivity/ public
-- -- --   open 𝓘njectivity∁ ⦃ … ⦄ public using (injectivity)

-- -- --   module _
-- -- --     {x} {X : Ø x} {a} (A : X → Ø a) {b} (B : X → Ø b)
-- -- --     where
-- -- --     module _
-- -- --       ⦃ _ : 𝓢uccessor₀∁ X ⦄
-- -- --       where
-- -- --       𝓽hin/ = ∀ {m : X} → A (⇑₀ m) → B m → B (⇑₀ m)
-- -- --       record 𝓣hin/ : Ø x ∙̂ a ∙̂ b where field thin : 𝓽hin/
-- -- --     record 𝓣hin∁ : Ø x ∙̂ a ∙̂ b where
-- -- --       field
-- -- --         ⦃ ⌶𝓢uccessor₀∁ ⦄ : 𝓢uccessor₀∁ X
-- -- --         ⦃ ⌶𝓣hin/ ⦄ : 𝓣hin/
-- -- --       open 𝓣hin/ ⌶𝓣hin/ public
-- -- --   open 𝓣hin∁ ⦃ … ⦄ public using (thin)

-- -- --   module _
-- -- --     {x} {X : Ø x} {a} (A : X → Ø a) {b} (B : X → Ø b)
-- -- --     where
-- -- --     module _
-- -- --       ⦃ _ : 𝓢uccessor₀∁ X ⦄
-- -- --       where
-- -- --       𝓽hick/ = ∀ {m} → B (⇑₀ m) → A m → B m
-- -- --       record 𝓣hick/ : Ø x ∙̂ a ∙̂ b where field thick : 𝓽hick/
-- -- --     record 𝓣hick∁ : Ø x ∙̂ a ∙̂ b where
-- -- --       field
-- -- --         ⦃ ⌶𝓢uccessor₀∁ ⦄ : 𝓢uccessor₀∁ X
-- -- --         ⦃ ⌶𝓣hick/ ⦄ : 𝓣hick/
-- -- --       open 𝓣hick/ ⌶𝓣hick/ public
-- -- --   open 𝓣hick∁ ⦃ … ⦄ public using (thick)

-- -- --   module _
-- -- --     {x} {X : Ø x}
-- -- --     {a} (A : X → Ø a)
-- -- --     {b} (B : X → Ø b)
-- -- --     {ℓ} (_≈_ : ∀ {x} → B x → B x → Ø ℓ)
-- -- --     where
-- -- --     module _
-- -- --       ⦃ _ : 𝓢uccessor₁∁ A ⦄
-- -- --       ⦃ _ : 𝓣hin/ A B ⦄
-- -- --       ⦃ _ : 𝓣hick/ A B ⦄
-- -- --       where
-- -- --       instance
-- -- --         _ = 𝓣hin∁ A B ∋ record {}
-- -- --         _ = 𝓣hick∁ A B ∋ record {}
-- -- --       𝓽hick∘thin=id/ = ∀ {m} (x : A m) (y : B m) → thick (thin (⇑₁ x) y) x ≈ y
-- -- --       record 𝓣hick∘thin=id/ : Ø x ∙̂ a ∙̂ b ∙̂ ℓ where field thick∘thin=id : 𝓽hick∘thin=id/
-- -- --     record 𝓣hick∘thin=id∁ : Ø x ∙̂ a ∙̂ b ∙̂ ℓ where
-- -- --       field
-- -- --         ⦃ ⌶𝓢uccessor₁∁ ⦄ : 𝓢uccessor₁∁ A
-- -- --         ⦃ ⌶𝓣hin/ ⦄ : 𝓣hin/ A B
-- -- --         ⦃ ⌶𝓣hick/ ⦄ : 𝓣hick/ A B
-- -- --         ⦃ ⌶𝓣hick∘thin=id/ ⦄ : 𝓣hick∘thin=id/
-- -- --       open 𝓣hick∘thin=id/ ⌶𝓣hick∘thin=id/ public
-- -- --   open 𝓣hick∘thin=id∁ ⦃ … ⦄ public using (thick∘thin=id)

-- -- --   module _
-- -- --     {x} {X : Ø x}
-- -- --     {a} (A : X → Ø a)
-- -- --     {b} (B : X → Ø b)
-- -- --     {e} (E? : Ø b → Ø e)
-- -- --     where
-- -- --     module _
-- -- --       ⦃ _ : 𝓢uccessor₀∁ X ⦄
-- -- --       where
-- -- --       𝓬heck/ = ∀ {m} → A (⇑₀ m) → B (⇑₀ m) → E? (B m)
-- -- --       record 𝓒heck/ : Ø x ∙̂ a ∙̂ b ∙̂ e where field check : 𝓬heck/
-- -- --     record 𝓒heck∁ : Ø x ∙̂ a ∙̂ b ∙̂ e where
-- -- --       field
-- -- --         ⦃ ⌶𝓢uccessor₀∁ ⦄ : 𝓢uccessor₀∁ X
-- -- --         ⦃ ⌶𝓒heck/ ⦄ : 𝓒heck/
-- -- --       open 𝓒heck/ ⌶𝓒heck/ public
-- -- --   open 𝓒heck∁ ⦃ … ⦄ public using (check)

-- -- --   module _
-- -- --     {x} {X : Ø x}
-- -- --     {a} (A : X → Ø a)
-- -- --     {b} (B : X → Ø b)
-- -- --     {ℓb} (_≈B_ : ∀ {x} → B x → B x → Ø ℓb)
-- -- --     {e} (E? : Ø b → Ø e)
-- -- --     {ℓe} (_≈E?_ : ∀ {A : Ø b} → E? A → E? A → Ø ℓe)
-- -- --     where
-- -- --     module _
-- -- --       ⦃ _ : 𝓢uccessor₀∁ X ⦄
-- -- --       ⦃ _ : 𝓣hin/ A B ⦄
-- -- --       ⦃ _ : 𝓒heck/ A B E? ⦄
-- -- --       (just : ∀ {x} → B x → E? (B x))
-- -- --       where
-- -- --       instance
-- -- --         _ = 𝓣hin∁ A B ∋ record {}
-- -- --         _ = 𝓒heck∁ A B E? ∋ record {}
-- -- --       𝓽hin-check-id/ = ∀ {m} (x : A (⇑₀ m)) y → ∀ (y' : B m) → thin x y' ≈B y → check x y ≈E? just y'
-- -- --       record 𝓣hin-check-id/ : Ø x ∙̂ a ∙̂ b ∙̂ ℓb ∙̂ e ∙̂ ℓe where field thin-check-id : 𝓽hin-check-id/
-- -- --     record 𝓣hin-check-id∁ : Ø x ∙̂ a ∙̂ b ∙̂ ℓb ∙̂ e ∙̂ ℓe where
-- -- --       field
-- -- --         ⦃ ⌶𝓢uccessor₀∁ ⦄ : 𝓢uccessor₀∁ X
-- -- --         ⦃ ⌶𝓣hin/ ⦄ : 𝓣hin/ A B
-- -- --         ⦃ ⌶𝓒heck/ ⦄ : 𝓒heck/ A B E?
-- -- --         just : ∀ {x} → B x → E? (B x)
-- -- --         ⦃ ⌶𝓣hin-check-id/ ⦄ : 𝓣hin-check-id/ just
-- -- --       open 𝓣hin-check-id/ ⌶𝓣hin-check-id/ public
-- -- --   open 𝓣hin-check-id∁ ⦃ … ⦄ using (thin-check-id)

-- -- --   record Thickandthin x a b ℓb e ℓe : Ø ↑̂ (x ∙̂ a ∙̂ b ∙̂ ℓb ∙̂ e ∙̂ ℓe) where
-- -- --     field
-- -- --       X : Ø x
-- -- --       A : X → Ø a
-- -- --       B : X → Ø b
-- -- --       _≈B_ : ∀ {x} → B x → B x → Ø ℓb
-- -- --       E? : Ø b → Ø e
-- -- --       _≈E?_ : ∀ {A : Ø b} → E? A → E? A → Ø ℓe
-- -- --       just : ∀ {x} → B x → E? (B x)
-- -- --       ⦃ ⌶𝓢uccessor₀∁ ⦄ : 𝓢uccessor₀∁ X
-- -- --       ⦃ ⌶𝓢uccessor₁/ ⦄ : 𝓢uccessor₁/ A
-- -- --     instance _ = 𝓢uccessor₁∁ A ∋ record {}
-- -- --     field
-- -- --       ⦃ ⌶𝓣hick/ ⦄ : 𝓣hick/ A B
-- -- --       ⦃ ⌶𝓣hin/ ⦄ : 𝓣hin/ A B
-- -- --     instance _ = 𝓣hin∁ A B ∋ record {}
-- -- --     field
-- -- --       ⦃ ⌶𝓘njectivity/ ⦄ : ∀ {m : X} {x : A (⇑₀ m)} → 𝓘njectivity/ (B m) (B (⇑₀ m)) _≈B_ _≈B_ (thin x)
-- -- --       ⦃ ⌶𝓒heck/ ⦄ : 𝓒heck/ A B E?
-- -- --       ⦃ ⌶𝓣hick∘thin=id/ ⦄ : 𝓣hick∘thin=id/ A B _≈B_
-- -- --       ⦃ ⌶𝓣hin-check-id/ ⦄ : 𝓣hin-check-id/ A B _≈B_ E? _≈E?_ just




-- -- -- open import Oscar.Data

-- -- -- module _ where

-- -- --   module _ {𝔬} {𝔒 : Ø 𝔬} where

-- -- --     instance

-- -- --       𝓡eflexivity∁Proposequality : 𝓡eflexivity∁ Proposequality⟦ 𝔒 ⟧
-- -- --       𝓡eflexivity∁Proposequality .𝓡eflexivity∁.reflexivity = !

-- -- --       𝓢ymmetry∁Proposequality : 𝓢ymmetry∁ Proposequality⟦ 𝔒 ⟧
-- -- --       𝓢ymmetry∁Proposequality .𝓢ymmetry∁.symmetry ∅ = !

-- -- --       𝓣ransitivity∁Proposequality : 𝓣ransitivity∁ Proposequality⟦ 𝔒 ⟧
-- -- --       𝓣ransitivity∁Proposequality .𝓣ransitivity∁.transitivity ∅ = ¡

-- -- --       IsEquivalence∁Proposequality : IsEquivalence∁ Proposequality⟦ 𝔒 ⟧
-- -- --       IsEquivalence∁Proposequality .IsEquivalence∁.⌶𝓡eflexivity∁ = !
-- -- --       IsEquivalence∁Proposequality .IsEquivalence∁.⌶𝓢ymmetry∁ = !
-- -- --       IsEquivalence∁Proposequality .IsEquivalence∁.⌶𝓣ransitivity∁ = !

-- -- -- module _ where

-- -- --   module _ {𝔬} (𝔒 : Ø 𝔬) where

-- -- --     SetoidProposequality : Setoid _ _
-- -- --     Setoid.Object SetoidProposequality = _
-- -- --     Setoid.ObjectEquality SetoidProposequality = Proposequality⟦ 𝔒 ⟧

-- -- --   instance

-- -- --     𝓒ongruity∁Proposequality : ∀ {a b} → 𝓒ongruity∁ a b Proposequality
-- -- --     𝓒ongruity∁Proposequality .𝓒ongruity∁.congruity _ ∅ = !

-- -- --     𝓒ongruity₂∁Proposequality : ∀ {a b c} → 𝓒ongruity₂∁ a b c Proposequality
-- -- --     𝓒ongruity₂∁Proposequality .𝓒ongruity₂∁.congruity₂ _ ∅ ∅ = !

-- -- -- --     𝓣ransextensionality∁Proposequality : ∀
-- -- -- --       {a} {A : Ø a}
-- -- -- --       {m} {_⊸_ : A → A → Ø m}
-- -- -- --       ⦃ _ : 𝓣ransitivity∁ _⊸_ ⦄
-- -- -- --       → 𝓣ransextensionality∁ _⊸_ Proposequality
-- -- -- --     𝓣ransextensionality∁Proposequality .𝓣ransextensionality∁.⌶𝓣ransitivity∁ = !
-- -- -- --     𝓣ransextensionality∁Proposequality .𝓣ransextensionality∁.⌶𝓣ransextensionality/ .𝓣ransextensionality/.transextensionality = congruity₂ _

-- -- -- -- module _ where

-- -- -- --   module _ {𝔬} {𝔒 : Ø 𝔬} {𝔭} {𝔓 : 𝔒 → Ø 𝔭} where

-- -- -- --     instance

-- -- -- --       𝓡eflexivity∁Proposextensequality : 𝓡eflexivity∁ Proposextensequality⟦ 𝔓 ⟧
-- -- -- --       𝓡eflexivity∁.reflexivity 𝓡eflexivity∁Proposextensequality _ = ∅

-- -- -- --       𝓢ymmetry∁Proposextensequality : 𝓢ymmetry∁ Proposextensequality⟦ 𝔓 ⟧
-- -- -- --       𝓢ymmetry∁.symmetry 𝓢ymmetry∁Proposextensequality f₁≡̇f₂ x rewrite f₁≡̇f₂ x = ∅

-- -- -- --       𝓣ransitivity∁Proposextensequality : 𝓣ransitivity∁ Proposextensequality⟦ 𝔓 ⟧
-- -- -- --       𝓣ransitivity∁.transitivity 𝓣ransitivity∁Proposextensequality f₁≡̇f₂ f₂≡̇f₃ x rewrite f₁≡̇f₂ x = f₂≡̇f₃ x

-- -- -- --       IsEquivalence∁Proposextensequality : IsEquivalence∁ Proposextensequality⟦ 𝔓 ⟧
-- -- -- --       IsEquivalence∁.⌶𝓡eflexivity∁ IsEquivalence∁Proposextensequality = !
-- -- -- --       IsEquivalence∁.⌶𝓢ymmetry∁ IsEquivalence∁Proposextensequality = !
-- -- -- --       IsEquivalence∁.⌶𝓣ransitivity∁ IsEquivalence∁Proposextensequality = !

-- -- -- --       𝓒̇ongruity∁Proposextensequality : ∀ {a b} → 𝓒̇ongruity∁ a b Proposextensequality
-- -- -- --       𝓒̇ongruity∁.ċongruity 𝓒̇ongruity∁Proposextensequality _ f≡̇g x rewrite f≡̇g x = ∅

-- -- -- -- module _ where

-- -- -- --   module _ {𝔬} {𝔒 : Ø 𝔬} {𝔭} (𝔓 : 𝔒 → Ø 𝔭) where

-- -- -- --     SetoidProposextensequality : Setoid _ _
-- -- -- --     Setoid.Object SetoidProposextensequality = _
-- -- -- --     Setoid.ObjectEquality SetoidProposextensequality = Proposextensequality⟦ 𝔓 ⟧

-- -- -- -- module _ where

-- -- -- --   module _
-- -- -- --     {a}
-- -- -- --     where

-- -- -- --     instance

-- -- -- --       𝓡eflexivity∁Function : 𝓡eflexivity∁ Function⟦ a ⟧
-- -- -- --       𝓡eflexivity∁.reflexivity 𝓡eflexivity∁Function = ¡

-- -- -- --       𝓣ransitivity∁Function : 𝓣ransitivity∁ Function⟦ a ⟧
-- -- -- --       𝓣ransitivity∁.transitivity 𝓣ransitivity∁Function f g = g ∘ f

-- -- -- -- module _ where

-- -- -- --   module _
-- -- -- --     {a} {A : Ø a} {b} {B : A → Ø b}
-- -- -- --     where

-- -- -- --     instance

-- -- -- --       𝓡eflexivity∁Extension : 𝓡eflexivity∁ (Extension B)
-- -- -- --       𝓡eflexivity∁.reflexivity 𝓡eflexivity∁Extension = ¡

-- -- -- --       𝓣ransitivity∁Extension : 𝓣ransitivity∁ (Extension B)
-- -- -- --       𝓣ransitivity∁.transitivity 𝓣ransitivity∁Extension f g = g ∘ f

-- -- -- --       𝓣ransassociativity/Extension : 𝓣ransassociativity/ (Extension B) Proposextensequality
-- -- -- --       𝓣ransassociativity/Extension .𝓣ransassociativity/.transassociativity _ _ _ _ = !

-- -- -- --       𝓣ransassociativity∁Extension = 𝓣ransassociativity∁ (Extension B) Proposextensequality ∋ record {}

-- -- -- --       𝓣ransextensionality/Extensional : 𝓣ransextensionality/ (Extension B) Proposextensequality
-- -- -- --       𝓣ransextensionality/Extensional .𝓣ransextensionality/.transextensionality {f₂ = f₂} f₁≡̇f₂ g₁≡̇g₂ x rewrite f₁≡̇f₂ x = g₁≡̇g₂ (f₂ x)

-- -- -- --       𝓣ransextensionality∁Extensional = 𝓣ransextensionality∁ (Extension B) Proposextensequality ∋ record {}

-- -- -- --       𝓣ransleftidentity/Extension : 𝓣ransleftidentity/ (Extension B) Proposextensequality
-- -- -- --       𝓣ransleftidentity/Extension .𝓣ransleftidentity/.transleftidentity _ = !

-- -- -- --       𝓣ransleftidentity∁Extension = 𝓣ransleftidentity∁ (Extension B) Proposextensequality ∋ record {}

-- -- -- --       𝓣ransrightidentity/Extension : 𝓣ransrightidentity/ (Extension B) Proposextensequality
-- -- -- --       𝓣ransrightidentity/Extension .𝓣ransrightidentity/.transrightidentity _ = !

-- -- -- --       𝓣ransrightidentity∁Extension = 𝓣ransrightidentity∁ (Extension B) Proposextensequality ∋ record {}

-- -- -- --       IsPrecategory∁Extension = IsPrecategory∁ (Extension B) Proposextensequality ∋ record {}

-- -- -- --       IsCategory/Extension : IsCategory/ (Extension B) Proposextensequality
-- -- -- --       IsCategory/Extension = record {}

-- -- -- --       IsCategory∁Extension = IsCategory∁ (Extension B) Proposextensequality ∋ record {}

-- -- -- --   module _
-- -- -- --     {a} {A : Ø a} {b} (B : A → Ø b)
-- -- -- --     where

-- -- -- --     PrecategoryExtension' = Precategory _ _ _ ∋ record { Object = _ ; Arrow = Extension B ; ArrowEquivalent = Proposextensequality }

-- -- -- --     PrecategoryExtension : Precategory _ _ _
-- -- -- --     PrecategoryExtension .Precategory.Object = _
-- -- -- --     PrecategoryExtension .Precategory.Arrow = Extension B
-- -- -- --     PrecategoryExtension .Precategory.ArrowEquivalent = Proposextensequality

-- -- -- --     CategoryExtension : Category _ _ _
-- -- -- --     CategoryExtension .Category.Object = _
-- -- -- --     CategoryExtension .Category.Arrow = Extension B
-- -- -- --     CategoryExtension .Category.ArrowEquivalent = Proposextensequality

-- -- -- -- record Substitunction⌶ {𝔭} (𝔓 : Ø 𝔭) : Ø₀ where
-- -- -- --   no-eta-equality

-- -- -- --   open Substitunction 𝔓
-- -- -- --   open Term 𝔓

-- -- -- --   private

-- -- -- --     mutual

-- -- -- --       𝓶apSubstitunctionExtensionTerm : 𝓶ap/ Substitunction (Extension Term) ¡
-- -- -- --       𝓶apSubstitunctionExtensionTerm σ (i x) = σ x
-- -- -- --       𝓶apSubstitunctionExtensionTerm σ leaf = leaf
-- -- -- --       𝓶apSubstitunctionExtensionTerm σ (τ₁ fork τ₂) = 𝓶apSubstitunctionExtensionTerm σ τ₁ fork 𝓶apSubstitunctionExtensionTerm σ τ₂
-- -- -- --       𝓶apSubstitunctionExtensionTerm σ (function p τs) = function p (𝓶apSubstitunctionExtensionTerms σ τs)

-- -- -- --       𝓶apSubstitunctionExtensionTerms : ∀ {N} → 𝓶ap/ Substitunction (Extension $ Terms N) ¡
-- -- -- --       𝓶apSubstitunctionExtensionTerms σ ∅ = ∅
-- -- -- --       𝓶apSubstitunctionExtensionTerms σ (τ , τs) = 𝓶apSubstitunctionExtensionTerm σ τ , 𝓶apSubstitunctionExtensionTerms σ τs

-- -- -- --   instance

-- -- -- --     𝓜ap/SubstitunctionExtensionTerm : 𝓜ap/ Substitunction (Extension Term) ¡
-- -- -- --     𝓜ap/SubstitunctionExtensionTerm .𝓜ap/.map = 𝓶apSubstitunctionExtensionTerm

-- -- -- --     𝓜ap∁SubstitunctionExtensionTerm = 𝓜ap∁ Substitunction (Extension Term) ∋ record { μ = ¡ }

-- -- -- --     𝓜ap/SubstitunctionExtensionTerms : ∀ {N} → 𝓜ap/ Substitunction (Extension $ Terms N) ¡
-- -- -- --     𝓜ap/SubstitunctionExtensionTerms .𝓜ap/.map = 𝓶apSubstitunctionExtensionTerms

-- -- -- --     𝓜ap∁SubstitunctionExtensionTerms = λ {N} → 𝓜ap∁ Substitunction (Extension $ Terms N) ∋ record { μ = ¡ }

-- -- -- --     𝓣ransitivity∁Substitunction : 𝓣ransitivity∁ Substitunction
-- -- -- --     𝓣ransitivity∁Substitunction .𝓣ransitivity∁.transitivity f g = map g ∘ f

-- -- -- --   private

-- -- -- --     mutual

-- -- -- --       𝓶apextensionalitySubstitunctionExtensionTerm : 𝓶apextensionality/ Substitunction Proposextensequality (Extension Term) Proposextensequality
-- -- -- --       𝓶apextensionalitySubstitunctionExtensionTerm p (i x) = p x
-- -- -- --       𝓶apextensionalitySubstitunctionExtensionTerm p leaf = ∅
-- -- -- --       𝓶apextensionalitySubstitunctionExtensionTerm p (s fork t) = congruity₂ _fork_ (𝓶apextensionalitySubstitunctionExtensionTerm p s) (𝓶apextensionalitySubstitunctionExtensionTerm p t)
-- -- -- --       𝓶apextensionalitySubstitunctionExtensionTerm p (function fn ts) = congruity (function fn) (𝓶apextensionalitySubstitunctionExtensionTerms p ts)

-- -- -- --       𝓶apextensionalitySubstitunctionExtensionTerms : ∀ {N} → 𝓶apextensionality/ Substitunction Proposextensequality (Extension $ Terms N) Proposextensequality
-- -- -- --       𝓶apextensionalitySubstitunctionExtensionTerms p ∅ = ∅
-- -- -- --       𝓶apextensionalitySubstitunctionExtensionTerms p (t , ts) = congruity₂ _,_ (𝓶apextensionalitySubstitunctionExtensionTerm p t) (𝓶apextensionalitySubstitunctionExtensionTerms p ts)

-- -- -- --   instance

-- -- -- --     𝓜apextensionality/SubstitunctionExtensionTerm : 𝓜apextensionality/ Substitunction Proposextensequality (Extension Term) Proposextensequality
-- -- -- --     𝓜apextensionality/SubstitunctionExtensionTerm .𝓜apextensionality/.mapextensionality = 𝓶apextensionalitySubstitunctionExtensionTerm

-- -- -- --     𝓜apextensionality∁SubstitunctionExtensionTerm = 𝓜apextensionality∁ Substitunction Proposextensequality (Extension Term) Proposextensequality ∋ record {}

-- -- -- --     𝓜apextensionality/SubstitunctionExtensionTerms : ∀ {N} → 𝓜apextensionality/ Substitunction Proposextensequality (Extension $ Terms N) Proposextensequality
-- -- -- --     𝓜apextensionality/SubstitunctionExtensionTerms .𝓜apextensionality/.mapextensionality = 𝓶apextensionalitySubstitunctionExtensionTerms

-- -- -- --     𝓜apextensionality∁SubstitunctionExtensionTerms = λ {N} → 𝓜apextensionality∁ Substitunction Proposextensequality (Extension $ Terms N) Proposextensequality ∋ record {}

-- -- -- --   private

-- -- -- --     mutual

-- -- -- --       𝓶aptranscommutativitySubstitunctionExtensionTerm : 𝓶aptranscommutativity/ Substitunction (Extension Term) Proposextensequality
-- -- -- --       𝓶aptranscommutativitySubstitunctionExtensionTerm _ _ (i _) = !
-- -- -- --       𝓶aptranscommutativitySubstitunctionExtensionTerm _ _ leaf = !
-- -- -- --       𝓶aptranscommutativitySubstitunctionExtensionTerm _ _ (τ₁ fork τ₂) = congruity₂ _fork_ (𝓶aptranscommutativitySubstitunctionExtensionTerm _ _ τ₁) (𝓶aptranscommutativitySubstitunctionExtensionTerm _ _ τ₂)
-- -- -- --       𝓶aptranscommutativitySubstitunctionExtensionTerm f g (function fn ts) = congruity (function fn) (𝓶aptranscommutativitySubstitunctionExtensionTerms f g ts)

-- -- -- --       𝓶aptranscommutativitySubstitunctionExtensionTerms : ∀ {N} → 𝓶aptranscommutativity/ Substitunction (Extension $ Terms N) Proposextensequality
-- -- -- --       𝓶aptranscommutativitySubstitunctionExtensionTerms _ _ ∅ = !
-- -- -- --       𝓶aptranscommutativitySubstitunctionExtensionTerms _ _ (τ , τs) = congruity₂ _,_ (𝓶aptranscommutativitySubstitunctionExtensionTerm _ _ τ) (𝓶aptranscommutativitySubstitunctionExtensionTerms _ _ τs)

-- -- -- --   instance

-- -- -- --     𝓜aptranscommutativity/SubstitunctionExtensionTerm : 𝓜aptranscommutativity/ Substitunction (Extension Term) Proposextensequality
-- -- -- --     𝓜aptranscommutativity/SubstitunctionExtensionTerm .𝓜aptranscommutativity/.maptranscommutativity = 𝓶aptranscommutativitySubstitunctionExtensionTerm

-- -- -- --     𝓜aptranscommutativity∁SubstitunctionExtensionTerm = 𝓜aptranscommutativity∁ Substitunction (Extension Term) Proposextensequality ∋ record {}

-- -- -- --     𝓜aptranscommutativity/SubstitunctionExtensionTerms : ∀ {N} → 𝓜aptranscommutativity/ Substitunction (Extension $ Terms N) Proposextensequality
-- -- -- --     𝓜aptranscommutativity/SubstitunctionExtensionTerms {N} .𝓜aptranscommutativity/.maptranscommutativity = 𝓶aptranscommutativitySubstitunctionExtensionTerms

-- -- -- --     𝓜aptranscommutativity∁SubstitunctionExtensionTerms = λ {N} → 𝓜aptranscommutativity∁ Substitunction (Extension $ Terms N) Proposextensequality ∋ record {}

-- -- -- --   instance

-- -- -- --     𝓣ransassociativity/Substitunction : 𝓣ransassociativity/ Substitunction Proposextensequality
-- -- -- --     𝓣ransassociativity/Substitunction .𝓣ransassociativity/.transassociativity f g h = maptranscommutativity g h ∘ f

-- -- -- --     𝓣ransassociativity∁Substitunction = 𝓣ransassociativity∁ Substitunction Proposextensequality ∋ record {}

-- -- -- --     𝓣ransextensionality/Substitunction : 𝓣ransextensionality/ Substitunction Proposextensequality
-- -- -- --     𝓣ransextensionality/Substitunction .𝓣ransextensionality/.transextensionality {f₂ = f₂} f₁≡̇f₂ g₁≡̇g₂ x rewrite f₁≡̇f₂ x = mapextensionality g₁≡̇g₂ $ f₂ x

-- -- -- --     𝓣ransextensionality∁Substitunction = 𝓣ransextensionality∁ Substitunction Proposextensequality ∋ record {}

-- -- -- --     IsPrecategory∁Substitunction = IsPrecategory∁ Substitunction Proposextensequality ∋ record {}

-- -- -- --   PrecategorySubstitunction = Precategory _ _ _ ∋ record { Object = _ ; Arrow = Substitunction ; ArrowEquivalent = Proposextensequality }

-- -- -- --   instance

-- -- -- --     IsPrefunctor∁SubstitunctionExtensionTerm = IsPrefunctor∁ Substitunction Proposextensequality (Extension Term) Proposextensequality ∋ record {}
-- -- -- --     IsPrefunctor∁SubstitunctionExtensionTerms = λ {N} → IsPrefunctor∁ Substitunction Proposextensequality (Extension $ Terms N) Proposextensequality ∋ record {}

-- -- -- --   PrefunctorSubstitunctionExtensionTerm : Prefunctor _ _ _ _ _ _
-- -- -- --   PrefunctorSubstitunctionExtensionTerm .Prefunctor.Object₁ = _
-- -- -- --   PrefunctorSubstitunctionExtensionTerm .Prefunctor.Arrow₁ = Substitunction
-- -- -- --   PrefunctorSubstitunctionExtensionTerm .Prefunctor.ArrowEquivalent₁ = Proposextensequality
-- -- -- --   PrefunctorSubstitunctionExtensionTerm .Prefunctor.Object₂ = _
-- -- -- --   PrefunctorSubstitunctionExtensionTerm .Prefunctor.Arrow₂ = Extension Term
-- -- -- --   PrefunctorSubstitunctionExtensionTerm .Prefunctor.ArrowEquivalent₂ = Proposextensequality

-- -- -- --   PrefunctorSubstitunctionExtensionTerms : ¶ → Prefunctor _ _ _ _ _ _
-- -- -- --   PrefunctorSubstitunctionExtensionTerms _ .Prefunctor.Object₁ = _
-- -- -- --   PrefunctorSubstitunctionExtensionTerms _ .Prefunctor.Arrow₁ = Substitunction
-- -- -- --   PrefunctorSubstitunctionExtensionTerms _ .Prefunctor.ArrowEquivalent₁ = Proposextensequality
-- -- -- --   PrefunctorSubstitunctionExtensionTerms _ .Prefunctor.Object₂ = _
-- -- -- --   PrefunctorSubstitunctionExtensionTerms N .Prefunctor.Arrow₂ = Extension $ Terms N
-- -- -- --   PrefunctorSubstitunctionExtensionTerms _ .Prefunctor.ArrowEquivalent₂ = Proposextensequality

-- -- -- --   instance

-- -- -- --     𝓡eflexivity∁Substitunction : 𝓡eflexivity∁ Substitunction
-- -- -- --     𝓡eflexivity∁Substitunction .𝓡eflexivity∁.reflexivity = i

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   private

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     mutual

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --       𝓲dentitySubstitunctionExtensionTerm : 𝓲dentity Substitunction (Extension Term) _ ¡
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --       𝓲dentitySubstitunctionExtensionTerm (i x) = ∅
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --       𝓲dentitySubstitunctionExtensionTerm leaf = ∅
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --       𝓲dentitySubstitunctionExtensionTerm (s fork t) = congruity₂ _fork_ (𝓲dentitySubstitunctionExtensionTerm s) (𝓲dentitySubstitunctionExtensionTerm t)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --       𝓲dentitySubstitunctionExtensionTerm (function fn ts) = congruity (function fn) (𝓲dentitySubstitunctionExtensionTerms ts)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --       𝓲dentitySubstitunctionExtensionTerms : ∀ {N} → 𝓲dentity Substitunction (Extension $ Terms N) _ ¡
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --       𝓲dentitySubstitunctionExtensionTerms ∅ = ∅
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --       𝓲dentitySubstitunctionExtensionTerms (t , ts) = congruity₂ _,_ (𝓲dentitySubstitunctionExtensionTerm t) (𝓲dentitySubstitunctionExtensionTerms ts)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   instance

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- {-
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Identity!SubstitunctionExtensionTerm : Identity! Substitunction (Extension Term) _ ¡
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Identity!.identity! Identity!SubstitunctionExtensionTerm = {!!} -- 𝓲dentitySubstitunctionExtensionTerm

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Identity!SubstitunctionExtensionTerms : ∀ {N} → Identity! Substitunction (Extension $ Terms N) _ ¡
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Identity!.identity! Identity!SubstitunctionExtensionTerms = {!!} -- 𝓲dentitySubstitunctionExtensionTerms

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Identity?SubstitunctionExtensionTerm : Identity? Substitunction (Extension Term) _ ¡
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Identity?.identity? Identity?SubstitunctionExtensionTerm = 𝓲dentitySubstitunctionExtensionTerm

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Identity?SubstitunctionExtensionTerms : ∀ {N} → Identity? Substitunction (Extension $ Terms N) _ ¡
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Identity?.identity? Identity?SubstitunctionExtensionTerms = 𝓲dentitySubstitunctionExtensionTerms

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     LeftIdentity!Substitunction : LeftIdentity! Substitunction _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     LeftIdentity!.left-identity! LeftIdentity!Substitunction f x = ((Term _ → Proposequality (𝓶apSubstitunctionExtensionTerm i (f x)) (f x)) ∋ identity?) (f x) -- {!{!identity!!} ∘ f!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     IdentitySubstitunctionExtensionTerm : Identity Substitunction (Extension Term) _ ¡
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Identity′.identity IdentitySubstitunctionExtensionTerm = 𝓲dentitySubstitunctionExtensionTerm

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     IdentitySubstitunctionExtensionTerms : ∀ {N} → Identity Substitunction (Extension $ Terms N) _ ¡
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Identity′.identity IdentitySubstitunctionExtensionTerms = 𝓲dentitySubstitunctionExtensionTerms

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     LeftIdentitySubstitunction : LeftIdentity Substitunction _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     LeftIdentity.left-identity LeftIdentitySubstitunction f = identity ∘ f

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     RightIdentitySubstitunction : RightIdentity Substitunction _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     RightIdentity.right-identity RightIdentitySubstitunction _ _ = ∅

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     IsCategorySubstitunction : IsCategory Substitunction _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     IsCategorySubstitunction = record {}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     IsFunctorSubstitunctionExtensionTerm : IsFunctor Substitunction _ (Extension Term) _ ¡
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     IsFunctorSubstitunctionExtensionTerm = record {}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     IsFunctorSubstitunctionExtensionTerms : ∀ {N} → IsFunctor Substitunction _ (Extension $ Terms N) _ ¡
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     IsFunctorSubstitunctionExtensionTerms = record {}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- module SubstitunctionØ {𝔭} (𝔓 : Ø 𝔭) where

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   open Substitunction 𝔓
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   open Term 𝔓

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   open Substitunction⌶ (Substitunction⌶ 𝔓 ∋ record {})

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   SemigroupoidSubstitunction : Semigroupoid _ _ _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   Semigroupoid.Object SemigroupoidSubstitunction = _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   Semigroupoid.Morphism SemigroupoidSubstitunction = Substitunction

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   SemifunctorSubstitunctionExtensionTerm : Semifunctor _ _ _ _ _ _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   Semifunctor.Object₁ SemifunctorSubstitunctionExtensionTerm = _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   Semifunctor.Morphism₁ SemifunctorSubstitunctionExtensionTerm = Substitunction
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   Semifunctor.Object₂ SemifunctorSubstitunctionExtensionTerm = _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   Semifunctor.Morphism₂ SemifunctorSubstitunctionExtensionTerm = Extension Term
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   Semifunctor.μ SemifunctorSubstitunctionExtensionTerm = ¡

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   CategorySubstitunction : Category _ _ _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   Category.Object CategorySubstitunction = _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   Category.Morphism CategorySubstitunction = Substitunction

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   FunctorSubstitunctionExtensionTerm : Functor _ _ _ _ _ _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   Functor.Object₁ FunctorSubstitunctionExtensionTerm = _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   Functor.Morphism₁ FunctorSubstitunctionExtensionTerm = Substitunction
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   Functor.Object₂ FunctorSubstitunctionExtensionTerm = _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   Functor.Morphism₂ FunctorSubstitunctionExtensionTerm = Extension Term
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   Functor.μ FunctorSubstitunctionExtensionTerm = ¡

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   module _ (N : ¶) where

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     FunctorSubstitunctionExtensionTerms : Functor _ _ _ _ _ _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Functor.Object₁ FunctorSubstitunctionExtensionTerms = _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Functor.Morphism₁ FunctorSubstitunctionExtensionTerms = Substitunction
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Functor.Object₂ FunctorSubstitunctionExtensionTerms = _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Functor.Morphism₂ FunctorSubstitunctionExtensionTerms = Extension $ Terms N
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Functor.μ FunctorSubstitunctionExtensionTerms = ¡

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- open SubstitunctionØ public

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- module AList⌶ {a} {A : Nat → Set a} where

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   private AList = Descender⟨ A ⟩

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   instance

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Reflexivity⌶AList : Reflexivity AList
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Reflexivity.reflexivity Reflexivity⌶AList = ∅

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Transitivity⌶AList : Transitivity AList
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Contiguity.contiguity Transitivity⌶AList f ∅ = f
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Contiguity.contiguity Transitivity⌶AList f (x , g) = x , contiguity f g

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     MorphismEquivalence⌶AList : MorphismEquivalence AList _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     MorphismEquivalence.morphismEquivalence MorphismEquivalence⌶AList = Proposequality

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Associativity⌶AList : Associativity AList _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Associativity.associativity Associativity⌶AList _ _ ∅ = ∅
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Associativity.associativity Associativity⌶AList f g (x , h) = congruity (x ,_) $ associativity f g h

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     IsSemigroupoid⌶AList : IsSemigroupoid AList _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     IsSemigroupoid⌶AList = record {}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     LeftIdentity⌶AList : LeftIdentity AList _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     LeftIdentity.left-identity LeftIdentity⌶AList _ = ∅

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     RightIdentity⌶AList : RightIdentity AList _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     RightIdentity.right-identity RightIdentity⌶AList ∅ = ∅
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     RightIdentity.right-identity RightIdentity⌶AList (x , f) = congruity (x ,_) $ right-identity f

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     IsCategory⌶AList : IsCategory AList _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     IsCategory⌶AList = record {}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- module Substitist⌶ {𝔭} {𝔓 : Ø 𝔭} where

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   open Substitunction 𝔓
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   open Term 𝔓
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   open Substitist 𝔓
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   open Substitunction⌶ (Substitunction⌶ 𝔓 ∋ record {})

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   postulate
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     _for_ : ∀ {n} (t' : Term n) (x : Fin (↑ n)) -> Fin (↑ n) -> Term n

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   instance

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Map⌶Substitist,Substitunction : Map Substitist Substitunction
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Map.map Map⌶Substitist,Substitunction ∅ = i
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Map.map Map⌶Substitist,Substitunction ((x , t) , σ) = map σ ∙ (t for x)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- module Fin⌶ where

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   instance

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Map⌶Maybe : ∀ {x} → Map {A = Ø x} (λ x y → x → y) (λ x y → Maybe x → Maybe y)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Map.map Map⌶Maybe f ∅ = ∅
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Map.map Map⌶Maybe f (↑ x) = ↑ (f x)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   instance

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Successor₀⌶¶ : Successor₀ ¶
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Successor₀.⇑₀ Successor₀⌶¶ = ↑_

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Principal₁Fin : Principal₁ Fin
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Principal₁Fin = record {}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Successor₁⌶Fin : Successor₁ Fin
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Successor₁.⇑₁ Successor₁⌶Fin = ↑_

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Thin⌶Fin,Fin : Thin Fin Fin
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Thin.thin Thin⌶Fin,Fin ∅ = ↑_
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Thin.thin Thin⌶Fin,Fin (↑ x) ∅ = ∅
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Thin.thin Thin⌶Fin,Fin (↑ x) (↑ y) = ↑ (thin x y)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Equivalence⌶Fin : ∀ {n} → Equivalence (Fin n) ∅̂
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Equivalence.equivalence Equivalence⌶Fin = Proposequality

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Equivalence⌶¶ : Equivalence ¶ ∅̂
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Equivalence.equivalence Equivalence⌶¶ = Proposequality

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     pattern Fin↑ n = ¶⟨<_⟩.↑_ {n = n}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Injectivity₀⌶¶↑ : Injectivity₀ ¶.↑_ ∅̂ ∅̂
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Injectivity₀⌶¶↑ = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Injectivity₀⌶Fin↑ : ∀ {n} → Injectivity₀ (Fin↑ n) ∅̂ ∅̂
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Injectivity₀.injectivity₀ (Injectivity₀⌶Fin↑ {n}) = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Injectivity₁⌶Fin↑ : Injectivity₁ Fin↑ ∅̂ ∅̂
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Injectivity₁.injectivity₁ Injectivity₁⌶Fin↑ = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Injectivity!⌶Fin↑ : Injectivity? Fin↑ ∅̂ ∅̂
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Injectivity!.injectivity! Injectivity!⌶Fin↑ = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Injectivity₁⌶ThinFin : ∀ {m} → Injectivity₁ (thin {A = Fin} {B = Fin} {m = m}) ∅̂ ∅̂
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Injectivity₁.injectivity₁ (Injectivity₁⌶ThinFin {m}) (∅ {n = .m}) {x} {y} x₁ = injectivity₁[ Fin↑ ] _ x₁
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Injectivity₁.injectivity₁ (Injectivity₁⌶ThinFin {m}) (↑_ {n = .m} w) {x} {y} x₁ = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Injectivity!⌶ThinFin : ∀ {m} → Injectivity? (thin {A = Fin} {B = Fin} {m = m}) ∅̂ ∅̂
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Injectivity!.injectivity! (Injectivity!⌶ThinFin {m}) (∅ {n = .m}) {x} {y} x₁ = injectivity?[ Fin↑ ] _ x₁
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Injectivity!.injectivity! (Injectivity!⌶ThinFin {m}) (↑_ {n = .m} w) {x} {y} x₁ = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Injectivity₂⌶ThinFin : ∀ {m} → Injectivity₂ (thin {A = Fin} {B = Fin} {m = m}) ∅̂ ∅̂
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Injectivity₂.injectivity₂ (Injectivity₂⌶ThinFin {m}) (∅ {n = .m}) {x} {y} x₁ = injectivity₀[ Fin↑ m ] x₁
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Injectivity₂.injectivity₂ (Injectivity₂⌶ThinFin {m}) (↑_ {n = .m} w) {x} {y} x₁ = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   test-thin-injective : ∀ {m} (x : Fin (↑ m)) {y₁ y₂ : Fin m} → thin x y₁ ≋ thin x y₂ → y₁ ≋ y₂
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   test-thin-injective x eq = injectivity₂[ thin[ Fin ] ] x eq

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- injectivity₂[ thin[ Fin ] ] x eq
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- injectivity₁[ thin[ Fin ] ] x eq

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     -- ∀ {n} → Injectivity₁ (thin {A = Fin} {B = Fin} {m = n}) ∅̂ ∅̂
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     -- Injectivity₁⌶ThinFin = ?


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Injectivity₁.injectivity₁ (Injectivity₁⌶ThinFin {n}) (∅ {n = .n}) {x} {y} eq = injectivity![ (λ n → ¶⟨<_⟩.↑_ {n = n}) ] _ _ _ eq
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       -- injectivity₁⋆[ (λ {n} → ¶⟨<_⟩.↑_ {n}) ] eq -- injectivity₀[ ¶⟨<_⟩.↑_ {n = n} ] eq
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Injectivity₁.injectivity₁ (Injectivity₁⌶ThinFin {n}) (↑_ {n = .n} w) {x} {y} eq = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     InjThinFin : ∀ {m} {x : Fin (↑ m)} → INJ (thin[ Fin ] x) ∅̂ ∅̂
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     INJ.inj (InjThinFin {m} {∅ {n = .m}}) {x} {y} = INj (¶⟨<_⟩.↑_ {m}) ⦃ it ⦄ ⦃ it ⦄ ⦃ {!InjThinFin {m = m} {x = ∅}!} ⦄ {x} {y}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     INJ.inj (InjThinFin {m} {↑_ {n = .m} x}) {x₁} {y} = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   test-thin-injective : ∀ {m} {x : Fin (↑ m)} {y₁ y₂ : Fin m} → thin x y₁ ≋ thin x y₂ → y₁ ≋ y₂
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   test-thin-injective {m = m} {x = x} eq = INj2 (thin {A = Fin} {B = Fin}) {w = x} eq -- INj2 (thin[ Fin ]) {w = x} eq -- INj2 (thin {A = Fin} {B = Fin}) eq

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   test-thin-injective2 : ∀ {m} {x : Fin (↑ m)} {y₁ y₂ : Fin m} → thin x y₁ ≋ thin x y₂ → y₁ ≋ y₂
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   test-thin-injective2 {x = x} = test-thin-injective {x = x}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   instance

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Injectivity⌶↑¶ : Injectivity ¶.↑_ ∅̂ ∅̂
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Injectivity.injectivity Injectivity⌶↑¶ ∅ = ∅

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Injectivity⌶↑Fin : ∀ {n} → Injectivity {A = ¶⟨< n ⟩} {B = ¶⟨< ↑ n ⟩} ¶⟨<_⟩.↑_ ∅̂ ∅̂
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Injectivity.injectivity (Injectivity⌶↑Fin {n}) {x} {.x} ∅ = ∅

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   Injectivity⌶ThinFin : ∀ {m} {x : Fin (⇑₀ m)} → Injectivity (thin[ Fin ] x) ∅̂ ∅̂
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   Injectivity.injectivity (Injectivity⌶ThinFin {m = m} {x = ∅}) e = injectivity {B = Fin (↑ m)} {f = ↑_ {n = m}} e -- injectivity {B = Fin m} {f = ↑_ {n = _}} e -- injectivity {f = ¶⟨<_⟩.↑_ {n = _}} ⦃ r = {!!} ⦄ {!e!} -- injectivity {f = ¶⟨<_⟩.↑_} e
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       -- injectivity[ ¶⟨<_⟩.↑_ ] ⦃ e1 = ! ⦄ ⦃ e2 = Equivalence⌶Fin ⦄ ⦃ i1 = Injectivity⌶↑Fin ⦄ e
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       -- injectivity[ ¶.↑_ ] e
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   Injectivity.injectivity (Injectivity⌶ThinFin {.(↑ _)} {↑_ {n = .(↑ n)} x}) {∅ {n = n}} {y} x₂ = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   Injectivity.injectivity (Injectivity⌶ThinFin {.(↑ _)} {↑_ {n = .(↑ n)} x}) {↑_ {n = n} x₁} {y} x₂ = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   instance

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ThinInjective⌶Fin,Fin : ThinInjective Fin Fin ∅̂
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ThinInjective.iInjectivity ThinInjective⌶Fin,Fin {m} {x} = Injectivity⌶ThinFin {m} {x} -- Injectivity⌶ThinFin

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   test-thin-injective : ∀ {m} {x : Fin (↑ m)} {y₁ y₂ : Fin m} → thin x y₁ ≋ thin x y₂ → y₁ ≋ y₂
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   test-thin-injective {x = x} = thin-injective {B = Fin} { x = x }

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   instance I1 = Injectivity⌶ThinFin

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   test-thin-injective' : ∀ {m} {x : Fin (↑ m)} {y₁ y₂ : Fin m} → thin x y₁ ≋ thin x y₂ → y₁ ≋ y₂
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   test-thin-injective' {m} {x = x} eq = injectivity {A = Fin m} {B = Fin (↑ m)} {f = thin {A = Fin} {B = λ v → Fin v} x} ⦃ r = I1 {m} {{!!}} ⦄ eq --

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   instance

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     InjectivityP⌶Fin : ∀ {m} {x : Fin m} → InjectivityP (¶⟨<_⟩.↑_ {n = m})
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     InjectivityP.injectivityP (InjectivityP⌶Fin {m} {x}) = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     InjectivityP⌶ThinFin : ∀ {m} {x : Fin (⇑₀ m)} → InjectivityP (thin[ Fin ] x)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     InjectivityP.injectivityP (InjectivityP⌶ThinFin {m} {∅ {n = .m}}) {x} {y} x₂ = injectivityP x₂
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     InjectivityP.injectivityP (InjectivityP⌶ThinFin {m} {↑_ {n = .m} x}) {x₁} {y} x₂ = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   test-fin-injective : ∀ {m} {y₁ y₂ : Fin m} → ¶⟨<_⟩.↑ y₁ ≋ ↑ y₂ → y₁ ≋ y₂
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   test-fin-injective {m} = injectivity {f = λ v → ¶⟨<_⟩.↑_ {m} v}


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- {-
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ThinInjective⌶Fin,Fin : ThinInjective Fin Fin ∅̂
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ThinInjective.thin-injective ThinInjective⌶Fin,Fin {x = ∅} e = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ThinInjective.thin-injective ThinInjective⌶Fin,Fin {x = ↑ x} {∅} {∅} _ = ∅
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ThinInjective.thin-injective ThinInjective⌶Fin,Fin {x = ↑ x} {∅} {↑ _} ()
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ThinInjective.thin-injective ThinInjective⌶Fin,Fin {x = ↑ x} {↑ _} {∅} ()
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ThinInjective.thin-injective ThinInjective⌶Fin,Fin {x = ↑ x} {↑ y₁} {↑ y₂} = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Thick⌶Fin,Fin : Thick Fin Fin
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Thick.thick Thick⌶Fin,Fin = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ThickThinId⌶Fin,Fin : ThickThinId Fin Fin ∅̂
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ThickThinId.thick∘thin=id ThickThinId⌶Fin,Fin = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Maybe*⌶ : ∀ {a} → Maybe* a
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Maybe*.Maybe Maybe*⌶ = Maybe
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Maybe*.just Maybe*⌶ = ↑_

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Check⌶Fin,Fin : Check Fin Fin
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Check.check Check⌶Fin,Fin ∅ ∅ = ∅
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Check.check Check⌶Fin,Fin ∅ (↑ y) = ↑ y
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Check.check Check⌶Fin,Fin {∅} (↑ ()) _
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Check.check Check⌶Fin,Fin {↑ _} (↑ x) ∅ = ↑ ∅
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Check.check Check⌶Fin,Fin {↑ _} (↑ x) (↑ y) = map ¶⟨<_⟩.↑_ $ check x y

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- {-
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Equivalence⌶Maybe : ∀ {a} {A : Ø a} {ℓ} ⦃ _ : Equivalence A ℓ ⦄ → Equivalence (Maybe A) ℓ
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Equivalence.equivalence Equivalence⌶Maybe ∅ ∅ = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Equivalence.equivalence Equivalence⌶Maybe ∅ (↑ x₁) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Equivalence.equivalence Equivalence⌶Maybe (↑ x₁) ∅ = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Equivalence.equivalence Equivalence⌶Maybe (↑ x₁) (↑ x₂) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Equivalence.⌶IsSetoid Equivalence⌶Maybe = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Equivalence⌶MaybeFin : ∀ {n} → Equivalence (Maybe (Fin n)) ∅̂
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Equivalence.equivalence Equivalence⌶MaybeFin = Proposequality

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ThinCheckId⌶Fin,Fin : ThinCheckId Fin Fin ∅̂ ∅̂
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ThinCheckId.thin-check-id ThinCheckId⌶Fin,Fin x y y' x₁ = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ThickAndThin⌶FinFin : ThickAndThin Fin Fin ∅̂ ∅̂
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ThickAndThin⌶FinFin = record {}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   module _ {𝔭} {𝔓 : Ø 𝔭} where

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     open Term 𝔓

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     instance

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       Principal₁⌶Term : Principal₁ Term
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       Principal₁⌶Term = record {}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     private

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       mutual

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         𝓶ap⌶ExtensionFin,ExtensionTerm : 𝓶ap (Extension Fin) (Extension Term)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         𝓶ap⌶ExtensionFin,ExtensionTerm f (i x) = i (f x)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         𝓶ap⌶ExtensionFin,ExtensionTerm f leaf = leaf
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         𝓶ap⌶ExtensionFin,ExtensionTerm f (t1 fork t2) = (𝓶ap⌶ExtensionFin,ExtensionTerm f t1) fork 𝓶ap⌶ExtensionFin,ExtensionTerm f t2
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         𝓶ap⌶ExtensionFin,ExtensionTerm f (function F ts) = function F (𝓶ap⌶ExtensionFin,ExtensionTerms f ts)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         𝓶ap⌶ExtensionFin,ExtensionTerms : ∀ {N} → 𝓶ap (Extension Fin) (Extension (Terms N))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         𝓶ap⌶ExtensionFin,ExtensionTerms f ∅ = ∅
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         𝓶ap⌶ExtensionFin,ExtensionTerms f (t , ts) = 𝓶ap⌶ExtensionFin,ExtensionTerm f t , 𝓶ap⌶ExtensionFin,ExtensionTerms f ts

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     instance

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       Map⌶ExtensionFin,ExtensionTerm : Map (Extension Fin) (Extension Term)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       Map.map Map⌶ExtensionFin,ExtensionTerm = 𝓶ap⌶ExtensionFin,ExtensionTerm

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       Map⌶ExtensionFin,ExtensionTerms : ∀ {N} → Map (Extension Fin) (Extension (Terms N))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       Map.map Map⌶ExtensionFin,ExtensionTerms = 𝓶ap⌶ExtensionFin,ExtensionTerms

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       Thin⌶Fin,Term : Thin Fin Term
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       Thin.thin Thin⌶Fin,Term = map ∘ thin

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       Equivalence⌶Term : ∀ {n} → Equivalence (Term n) ∅̂
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       Equivalence.equivalence Equivalence⌶Term = Proposequality

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       Injectivity⌶ASD : Injectivity

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       ThinInjective⌶Fin,Term : ThinInjective Fin Term ∅̂
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       ThinInjective.thin-injective ThinInjective⌶Fin,Term = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Successor₀⌶¶ : Upper Fin
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     Upper.up Upper⌶Fin = ↑_

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ThickAndThin⌶Fin : ThickAndThin Fin Fin
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ThickAndThin.thin ThickAndThin⌶Fin ∅ y = ↑ y
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ThickAndThin.thin ThickAndThin⌶Fin (↑ x) ∅ = ∅
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ThickAndThin.thin ThickAndThin⌶Fin (↑ x) (↑ y) = ↑ thin x y
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ThickAndThin.thin-injective ThickAndThin⌶Fin x x₁ = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ThickAndThin.thick ThickAndThin⌶Fin = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ThickAndThin.thick∘thin=id ThickAndThin⌶Fin = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ThickAndThin.check ThickAndThin⌶Fin = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ThickAndThin.thin-check-id ThickAndThin⌶Fin = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- module Term⌶ {𝔭} {𝔓 : Ø 𝔭} where

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   open Term 𝔓

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   instance

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ThickAndThin⌶Term : ThickAndThin Term
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ThickAndThin.thin ThickAndThin⌶Term x (i x₁) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ThickAndThin.thin ThickAndThin⌶Term x leaf = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ThickAndThin.thin ThickAndThin⌶Term x (x₁ fork x₂) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ThickAndThin.thin ThickAndThin⌶Term x (function x₁ x₂) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ThickAndThin.thin-injective ThickAndThin⌶Term = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ThickAndThin.thick ThickAndThin⌶Term = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ThickAndThin.thick∘thin=id ThickAndThin⌶Term = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ThickAndThin.check ThickAndThin⌶Term = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ThickAndThin.thin-check-id ThickAndThin⌶Term = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- {-
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Data
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   Nat
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   ≤↓List -- m ≤ n, n-1...m
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   Substitunction
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   Substitist
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Record
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   Product
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   Functor
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- Class
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   Reflexivity
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   IsFunctor
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   ThickAndThin

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -}
















-- -- -- -- -- -- open import Oscar.Data

-- -- -- -- -- -- module _ where

-- -- -- -- -- --   module _ {𝔬} {𝔒 : Ø 𝔬} where

-- -- -- -- -- --     instance

-- -- -- -- -- --       𝓡eflexivity∁Proposequality : 𝓡eflexivity∁ Proposequality⟦ 𝔒 ⟧
-- -- -- -- -- --       𝓡eflexivity∁Proposequality .𝓡eflexivity∁.reflexivity = !

-- -- -- -- -- --       𝓢ymmetry∁Proposequality : 𝓢ymmetry∁ Proposequality⟦ 𝔒 ⟧
-- -- -- -- -- --       𝓢ymmetry∁Proposequality .𝓢ymmetry∁.symmetry ∅ = !

-- -- -- -- -- --       𝓣ransitivity∁Proposequality : 𝓣ransitivity∁ Proposequality⟦ 𝔒 ⟧
-- -- -- -- -- --       𝓣ransitivity∁Proposequality .𝓣ransitivity∁.transitivity ∅ = ¡

-- -- -- -- -- --       IsEquivalence∁Proposequality : IsEquivalence∁ Proposequality⟦ 𝔒 ⟧
-- -- -- -- -- --       IsEquivalence∁Proposequality .IsEquivalence∁.isReflexive = !
-- -- -- -- -- --       IsEquivalence∁Proposequality .IsEquivalence∁.isSymmetric = !
-- -- -- -- -- --       IsEquivalence∁Proposequality .IsEquivalence∁.isTransitive = !

-- -- -- -- -- -- -- open import Oscar.Data using (_≡_{-; ∅-})

-- -- -- -- -- -- {-
-- -- -- -- -- -- transport : ∀ {a b} {A : Set a} (B : A → Set b) {x y} → x ≡ y → B x → B y
-- -- -- -- -- -- transport _ ∅ = ¡

-- -- -- -- -- -- transport₂ : ∀ {a b c} {A : Set a} {B : Set b} (C : A → B → Set c) {x₁ x₂ y₁ y₂} → x₁ ≡ x₂ → y₁ ≡ y₂ → C x₁ y₁ → C x₂ y₂
-- -- -- -- -- -- transport₂ C refl refl cxy = cxy
-- -- -- -- -- -- -}


-- -- -- -- -- -- -- {-
-- -- -- -- -- -- --   instance ⌶𝓘njectivity∁ : ∀ {m : X} {x : A (⇑₀ m)} → 𝓘njectivity∁ (B m) (B (⇑₀ m)) _≈B_ _≈B_
-- -- -- -- -- -- --   ⌶𝓘njectivity∁ {_} {x} = record { f = thin x }
-- -- -- -- -- -- -- -}

-- -- -- -- -- -- --   postulate

-- -- -- -- -- -- --     X : Set
-- -- -- -- -- -- --     X' : Set
-- -- -- -- -- -- --     A : X → Set
-- -- -- -- -- -- --     A' : X → Set
-- -- -- -- -- -- --     B : X → Set
-- -- -- -- -- -- --     E? : Set → Set
-- -- -- -- -- -- --     _≈B_ : ∀ {x} → B x → B x → Set
-- -- -- -- -- -- --     _≈E?_ : ∀ {A : Set} → E? A → E? A → Set
-- -- -- -- -- -- --     just : ∀ {x} → B x → E? (B x)
-- -- -- -- -- -- --     foo : ∀ {m} →
-- -- -- -- -- -- --       A (magic {∅̂} {X → X} m) → B m → B (magic {∅̂} {X → X} m)

-- -- -- -- -- -- --   instance

-- -- -- -- -- -- --     ⌶Thickandthin : Thickandthin _ _ _ _ _ _
-- -- -- -- -- -- --     ⌶Thickandthin = ?

-- -- -- -- -- -- --     ⌶Thickandthin' : Thickandthin _ _ _ _ _ _
-- -- -- -- -- -- --     ⌶Thickandthin' = ?

-- -- -- -- -- -- --   instance

-- -- -- -- -- -- -- --    ⌶𝓢uccessor₀∁X : 𝓢uccessor₀∁ X
-- -- -- -- -- -- -- --    ⌶𝓢uccessor₀∁X .𝓢uccessor₀∁.successor₀ = magic

-- -- -- -- -- -- --     ⌶𝓢uccessor₀∁X' : 𝓢uccessor₀∁ X'
-- -- -- -- -- -- --     ⌶𝓢uccessor₀∁X' .𝓢uccessor₀∁.successor₀ = magic

-- -- -- -- -- -- --   test' : ∀ {m : X} → A' (⇑₀ ⦃ {!Thickandthin.⌶𝓢uccessor₀∁ ⌶Thickandthin!} ⦄ m)
-- -- -- -- -- -- --   test' = {!!}

-- -- -- -- -- -- -- --   test-thin : ∀ {m : X} → A (⇑₀ m) → B m → B (⇑₀ m)
-- -- -- -- -- -- -- --   test-thin = thin

-- -- -- -- -- -- -- --   test-injectivity : ∀ {m : X} {z : A (⇑₀ m)} → ∀ {x y} → thin z x ≈B thin z y → x ≈B y
-- -- -- -- -- -- -- --   test-injectivity = injectivity

-- -- -- -- -- -- -- -- -- record FMap {x} {y} (F : Ø x → Ø y) : Ø (↑̂ x) ∙̂ y where
-- -- -- -- -- -- -- -- --   field fmap : ∀ {A B : Ø x} → (A → B) → F A → F B

-- -- -- -- -- --       -- EqualityExtension : ∀ {x y : A} → Equality (Extension B x y) _
-- -- -- -- -- --       -- EqualityExtension .Equality._≋_ = Proposextensequality
-- -- -- -- -- --       -- EqualityExtension .Equality.isEquivalence = it

-- -- -- -- -- --     EqualitySubstitunction : ∀ {x y} → Equality (Substitunction x y) _
-- -- -- -- -- --     EqualitySubstitunction {x} {y} .Equality._≋_ = Proposextensequality
-- -- -- -- -- --     EqualitySubstitunction {x} {y} .Equality.isEquivalence = it

-- -- -- -- -- --     EqualityExtensionTerm : ∀ {x y} → Equality (Extension Term x y) _
-- -- -- -- -- --     EqualityExtensionTerm .Equality._≋_ = Proposextensequality
-- -- -- -- -- --     EqualityExtensionTerm .Equality.isEquivalence = it

-- -- -- -- -- --     EqualityExtensionTerms : ∀ {N x y} → Equality (Extension (Terms N) x y) _
-- -- -- -- -- --     EqualityExtensionTerms .Equality._≋_ = Proposextensequality
-- -- -- -- -- --     EqualityExtensionTerms .Equality.isEquivalence = it
