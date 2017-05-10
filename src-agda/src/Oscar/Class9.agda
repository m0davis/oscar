-- {-# OPTIONS --show-implicit #-}
module Oscar.Class9 where

open import Oscar.Prelude

record IsEquivalence
  {a} {A : Ø a} {ℓ}
    (_≋_ : A → A → Ø ℓ)
  : Ø a ∙̂ ℓ where
  field
    ≋-reflexivity : ∀ {x} → x ≋ x
    ≋-symmetry : ∀ {x y} → x ≋ y → y ≋ x
    ≋-transitivity : ∀ {x y z} → x ≋ y → y ≋ z → x ≋ z

open IsEquivalence ⦃ … ⦄ public

record Equivalence
  {a}
    (A : Ø a)
    ℓ
  : Ø a ∙̂ ↑̂ ℓ where
  infix 4 _≋_
  field
    _≋_ : A → A → Ø ℓ
    ⦃ ⌶IsEquivalence ⦄ : IsEquivalence _≋_

open Equivalence ⦃ … ⦄ public

record IsSemigroupoid {a} {A : Ø a} {m} (_⊸_ : A → A → Ø m) ℓ ⦃ _ : ∀ {x y} → Equivalence (x ⊸ y) ℓ ⦄ : Ø a ∙̂ m ∙̂ ℓ where
  infixr 9 _∙_
  field
    _∙_ : ∀ {x y z} → y ⊸ z → x ⊸ y → x ⊸ z
    ∙-extensionality : ∀ {x y z} {f₁ f₂ : x ⊸ y} {g₁ g₂ : y ⊸ z} → f₁ ≋ f₂ → g₁ ≋ g₂ → g₁ ∙ f₁ ≋ g₂ ∙ f₂
    ∙-associativity : ∀ {w x y z} (f : w ⊸ x) (g : x ⊸ y) (h : y ⊸ z) → (h ∙ g) ∙ f ≋ h ∙ g ∙ f

open IsSemigroupoid ⦃ … ⦄ public

{-
module _
  {a₁} {A₁ : Ø a₁} {m₁} (_⊸₁_ : A₁ → A₁ → Ø m₁) ℓ₁ ⦃ _ : ∀ {x y} → Equivalence (x ⊸₁ y) ℓ₁ ⦄ ⦃ _ : IsSemigroupoid _⊸₁_ ℓ₁ ⦄
  {a₂} {A₂ : Ø a₂} {m₂} (_⊸₂_ : A₂ → A₂ → Ø m₂) ℓ₂ ⦃ _ : ∀ {x y} → Equivalence (x ⊸₂ y) ℓ₂ ⦄ ⦃ _ : IsSemigroupoid _⊸₂_ ℓ₂ ⦄
  (μ : A₁ → A₂)
  where
  record Map
    : Ø a₁ ∙̂ m₁ ∙̂ a₂ ∙̂ m₂
    where
    field
      map : ∀ {x y} → x ⊸₁ y → μ x ⊸₂ μ y
  open Map ⦃ … ⦄ public
-}

{-
module _
  {a₁} {A₁ : Ø a₁} {m₁} (_⊸₁_ : A₁ → A₁ → Ø m₁)
  {a₂} {A₂ : Ø a₂} {m₂} (_⊸₂_ : A₂ → A₂ → Ø m₂)
  (μ : A₁ → A₂)
  where
  record Map
    : Ø a₁ ∙̂ m₁ ∙̂ a₂ ∙̂ m₂
    where
    field
      map : ∀ {x y} → x ⊸₁ y → μ x ⊸₂ μ y
  open Map ⦃ … ⦄ public
-}

𝓶ap : ∀
  {a} {A : Set a}
  {b} (B : A → A → Set b)
  {c} (C : A → A → Set c)
  → Ø a ∙̂ b ∙̂ c
𝓶ap B C = ∀ {x y} → B x y → C x y

record MapExtensionality
  {a₁} {A₁ : Ø a₁} {m₁}
    (_⊸₁_ : A₁ → A₁ → Ø m₁)
  {ℓ₁}
    (_≋₁_ : ∀ {x y} → x ⊸₁ y → x ⊸₁ y → Ø ℓ₁)
  {ℓ₂/map}
    (_≋₂/map_ : ∀ {x y} → x ⊸₁ y → x ⊸₁ y → Ø ℓ₂/map)
  : Ø a₁ ∙̂ m₁ ∙̂ ℓ₁ ∙̂ ℓ₂/map where
  field map-extensionality : ∀ {x y} {f₁ f₂ : x ⊸₁ y} → f₁ ≋₁ f₂ → f₁ ≋₂/map f₂
open MapExtensionality ⦃ … ⦄ public

record Map
  {a} {A : Set a}
  {m₁} (_⊸₁_ : A → A → Set m₁)
  {m₂/μ} (_⊸₂/μ_ : A → A → Set m₂/μ)
  : Ø a ∙̂ m₁ ∙̂ m₂/μ
  where
  field map : 𝓶ap _⊸₁_ _⊸₂/μ_

open Map ⦃ … ⦄ public

{-
record ExtensionalMap
  {a} {A : Set a}
  {m₁} (_⊸₁_ : A → A → Set m₁)
  {m₂/μ} (_⊸₂/μ_ : A → A → Set m₂/μ)
  b
  ℓ₁ ⦃ _ : ∀ {x y} → Equivalence (x ⊸₁ y) ℓ₁ ⦄
  ℓ₂
  -- ℓ₂/μ ⦃ _ : ∀ {x y} → Equivalence (x ⊸₂/μ y) ℓ₂/μ ⦄
  : Ø a ∙̂ m₁ ∙̂ m₂/μ ∙̂ ℓ₁ ∙̂ ↑̂ b ∙̂ ↑̂ ℓ₂
  where
  field emap : 𝓶ap _⊸₁_ _⊸₂/μ_
  field B : Ø b
  field μ : A → B
  field emap-≋₂ : ∀ {x y} → μ x _⊸₂/μ_ y → x ⊸₁ y → Ø ℓ₁
  field ⦃ emap-⌶ ⦄ : MapExtensionality _⊸₁_ {ℓ₁ = ℓ₁} _≋_ {ℓ₂/map = ℓ₂/μ} _≋_
open ExtensionalMap ⦃ … ⦄ public
-}

module _
  {a₁} {A₁ : Ø a₁} {m₁} (_⊸₁_ : A₁ → A₁ → Ø m₁) ℓ₁ ⦃ _ : ∀ {x y} → Equivalence (x ⊸₁ y) ℓ₁ ⦄
  {a₂} {A₂ : Ø a₂} {m₂} (_⊸₂_ : A₂ → A₂ → Ø m₂) ℓ₂ ⦃ _ : ∀ {x y} → Equivalence (x ⊸₂ y) ℓ₂ ⦄
  (μ : A₁ → A₂)
  where

  record IsSemifunctor
    : Ø a₁ ∙̂ m₁ ∙̂ ℓ₁ ∙̂ a₂ ∙̂ m₂ ∙̂ ↑̂ ℓ₂
    where
    field
      ⦃ ⌶IsSemigroupoid₁ ⦄ : IsSemigroupoid _⊸₁_ ℓ₁
      ⦃ ⌶IsSemigroupoid₂ ⦄ : IsSemigroupoid _⊸₂_ ℓ₂
      ⦃ ⌶Map ⦄ : Map _⊸₁_ (_⊸₂_ on μ) -- ℓ₂ -- (λ f₁ f₂ m → m f₁ ≋ m f₂)
      ⦃ ⌶MapExtensionality ⦄ : MapExtensionality _⊸₁_ _≋_ (_≋_ on map {_⊸₂/μ_ = _⊸₂_ on μ})

test-map-extensionality : ∀
  {a₁} {A₁ : Ø a₁} {m₁} (_⊸₁_ : A₁ → A₁ → Ø m₁) ℓ₁ ⦃ _ : ∀ {x y} → Equivalence (x ⊸₁ y) ℓ₁ ⦄
  {a₂} {A₂ : Ø a₂} {m₂} (_⊸₂_ : A₂ → A₂ → Ø m₂) ℓ₂ ⦃ _ : ∀ {x y} → Equivalence (x ⊸₂ y) ℓ₂ ⦄
  (μ : A₁ → A₂)
  ⦃ _ : IsSemifunctor _⊸₁_ ℓ₁ _⊸₂_ ℓ₂ μ ⦄
  → ∀ {x y} {f₁ f₂ : x ⊸₁ y} → f₁ ≋ f₂ → map {_⊸₂/μ_ = _⊸₂_ on μ} f₁ ≋ map f₂
test-map-extensionality _⊸₁_ ℓ₁ _⊸₂_ ℓ₂ μ = map-extensionality


--

--     foo : ∀ {x y} {f₁ f₂ : x ⊸₁ y} → f₁ ≋ f₂ → map {C = _⊸₂_ on μ} f₁ ≋ map f₂ --
--     foo {f₁ = f₁} eq = map-extensionality' {C = _⊸₂_ on μ} {f₁ = f₁} eq
-- --       map-commutativity : ∀ {x y z} (f : x ⊸₁ y) (g : y ⊸₁ z) → map (g ∙ f) ≋ map g ∙ map f

-- --   open IsSemifunctor ⦃ … ⦄ public

-- -- test-map : ∀
-- --   {a₁} {A₁ : Ø a₁} {m₁} (_⊸₁_ : A₁ → A₁ → Ø m₁) ℓ₁ ⦃ _ : ∀ {x y} → Equivalence (x ⊸₁ y) ℓ₁ ⦄
-- --   {a₂} {A₂ : Ø a₂} {m₂} (_⊸₂_ : A₂ → A₂ → Ø m₂) ℓ₂ ⦃ _ : ∀ {x y} → Equivalence (x ⊸₂ y) ℓ₂ ⦄
-- --   (μ : A₁ → A₂)
-- --   ⦃ _ : IsSemifunctor _⊸₁_ ℓ₁ _⊸₂_ ℓ₂ μ ⦄
-- --   → ∀ {x y} → x ⊸₁ y → μ x ⊸₂ μ y
-- -- test-map _ _ _ _ μ = map {μ = μ}

-- -- -- module _
-- -- --   {a₁} {A₁ : Ø a₁} {m₁} (_⊸₁_ : A₁ → A₁ → Ø m₁) ℓ₁ ⦃ _ : ∀ {x y} → Equivalence (x ⊸₁ y) ℓ₁ ⦄
-- -- --   {a₂} {A₂ : Ø a₂} {m₂} (_⊸₂_ : A₂ → A₂ → Ø m₂) ℓ₂ ⦃ _ : ∀ {x y} → Equivalence (x ⊸₂ y) ℓ₂ ⦄
-- -- --   (μ : A₁ → A₂)
-- -- --   where

-- -- --   𝓶ap : ∀
-- -- --     {a} {A : Ø a}
-- -- --     {b} (B : A → A → Ø b)
-- -- --     {c} (C : A → A → Ø c)
-- -- --     → Ø a ∙̂ b ∙̂ c
-- -- --   𝓶ap B C = ∀ {x y} → B x y → C x y

-- -- -- module _
-- -- --   {a} {A : Ø a}
-- -- --   {b} (B : A → A → Ø b)
-- -- --   {c} (C : ∀ {x y} → B x y → B x y → Ø c)
-- -- --   {d} (D : ∀ {x y} → B x y → B x y → Ø d)
-- -- --   where

-- -- --   𝓶ap-extensionality₁′ : Ø a ∙̂ b ∙̂ c ∙̂ d
-- -- --   𝓶ap-extensionality₁′ = ∀ {x y} {f₁ f₂ : B x y} → C f₁ f₂ → D f₁ f₂

-- -- --   record Extensionality₁′ : Ø a ∙̂ b ∙̂ c ∙̂ d where field extensionality₁ : 𝓮xtensionality₁′

-- -- -- open Extensionality₁′ ⦃ … ⦄ public

-- -- -- module _
-- -- --   {a₁} {A₁ : Ø a₁} {b₁} (B₁ : A₁ → A₁ → Ø b₁) c₁ ⦃ _ : MorphismEquivalence B₁ c₁ ⦄
-- -- --   {a₂} {A₂ : Ø a₂} {b₂} (B₂ : A₂ → A₂ → Ø b₂) c₂ ⦃ _ : MorphismEquivalence B₂ c₂ ⦄
-- -- --   (μ : A₁ → A₂)
-- -- --   ⦃ _ : Map B₁ (B₂ on μ) ⦄
-- -- --   where
-- -- --   Extensionality₁ = Extensionality₁′ B₁ _≋_ (λ f₁ f₂ → map[ B₂ on μ ] f₁ ≋ map f₂)
-- -- --   𝓮xtensionality₁ = 𝓮xtensionality₁′ B₁ _≋_ (λ f₁ f₂ → map[ B₂ on μ ] f₁ ≋ map f₂)


-- -- -- -- module _
-- -- -- --   {a} {A : Ø a}
-- -- -- --   {b} (B : A → A → Ø b)
-- -- -- --   where
-- -- -- --   𝓻eflexivity = ∀ {x} → B x x
-- -- -- --   record Reflexivity : Ø a ∙̂ b where field reflexivity : 𝓻eflexivity
-- -- -- --   open Reflexivity ⦃ … ⦄ public

-- -- -- -- ε : ∀ {a} {A : Ø a}
-- -- -- --       {b} {B : A → A → Ø b}
-- -- -- --     ⦃ _ : Reflexivity B ⦄
-- -- -- --     → ∀ {x} → B x x
-- -- -- -- ε = reflexivity

-- -- -- -- ε[_] : ∀ {a} {A : Ø a}
-- -- -- --          {b} (B : A → A → Ø b)
-- -- -- --        ⦃ _ : Reflexivity B ⦄
-- -- -- --        → ∀ {x} → B x x
-- -- -- -- ε[ _ ] = reflexivity

-- -- -- -- module _
-- -- -- --   {a} {A : Ø a}
-- -- -- --   {b} (B : A → A → Ø b)
-- -- -- --   {c} (C : ∀ {x y} → B x y → Ø c)
-- -- -- --   where
-- -- -- --   𝓻elationality = ∀ {x y} → (f : B x y) → C f
-- -- -- --   record Relationality : Ø a ∙̂ b ∙̂ c where field relationality : 𝓻elationality
-- -- -- --   open Relationality ⦃ … ⦄ public
-- -- -- -- {-
-- -- -- -- 𝓶ap : ∀
-- -- -- --   {a} {A : Ø a}
-- -- -- --   {b} (B : A → A → Ø b)
-- -- -- --   {c} (C : A → A → Ø c)
-- -- -- --   → Ø a ∙̂ b ∙̂ c
-- -- -- -- 𝓶ap B C = ∀ {x y} → B x y → C x y
-- -- -- -- -}

-- -- -- -- module _
-- -- -- --   {a} {A : Ø a}
-- -- -- --   {b} (B : A → A → Ø b)
-- -- -- --   {c} (C : A → A → Ø c)
-- -- -- --   where
-- -- -- --   𝓶ap = 𝓻elationality B (λ {x y} _ → C x y)
-- -- -- --   Map = Relationality B (λ {x y} _ → C x y)

-- -- -- -- map : ∀
-- -- -- --   {a} {A : Ø a}
-- -- -- --   {b} {B : A → A → Ø b}
-- -- -- --   {c} {C : A → A → Ø c}
-- -- -- --   ⦃ _ : Map B C ⦄
-- -- -- --   → 𝓶ap B C
-- -- -- -- map = relationality

-- -- -- -- {-
-- -- -- -- record Map
-- -- -- --   {a} {A : Ø a}
-- -- -- --   {b} (B : A → A → Ø b)
-- -- -- --   {c} (C : A → A → Ø c)
-- -- -- --   : Ø a ∙̂ b ∙̂ c where
-- -- -- --   field map : 𝓶ap B C

-- -- -- -- open Map ⦃ … ⦄ public
-- -- -- -- -}

-- -- -- -- map[_] : ∀
-- -- -- --   {a} {A : Ø a}
-- -- -- --   {b} {B : A → A → Ø b}
-- -- -- --   {c} (C : A → A → Ø c)
-- -- -- --   ⦃ _ : Map B C ⦄
-- -- -- --   → ∀ {x y} → B x y → C x y
-- -- -- -- map[ C ] f = map f

-- -- -- -- module _
-- -- -- --   {a} {A : Ø a}
-- -- -- --   {b} (B : A → A → Ø b)
-- -- -- --   where
-- -- -- --   𝓼ymmetry = 𝓻elationality B (λ {x y} _ → B y x)
-- -- -- --   Symmetry = Relationality B (λ {x y} _ → B y x)

-- -- -- -- symmetry : ∀
-- -- -- --   {a} {A : Ø a}
-- -- -- --   {b} {B : A → A → Ø b}
-- -- -- --   ⦃ _ : Symmetry B ⦄
-- -- -- --   → 𝓼ymmetry B
-- -- -- -- symmetry = relationality
-- -- -- -- {-
-- -- -- --   𝓼ymmetry = ∀ {x y} → B x y → B y x
-- -- -- --   record Symmetry : Ø a ∙̂ b where field symmetry : 𝓼ymmetry
-- -- -- --   open Symmetry ⦃ … ⦄ public
-- -- -- -- -}

-- -- -- -- module _
-- -- -- --   {a} {A : Ø a}
-- -- -- --   {b} (B : A → A → Ø b)
-- -- -- --   {c} (C : ∀ {x y z} → B x y → B y z → Ø c)
-- -- -- --   where
-- -- -- --   𝓬ontiguity = ∀ {x y z} (f : B x y) (g : B y z) → C f g
-- -- -- --   record Contiguity : Ø a ∙̂ b ∙̂ c where field contiguity : 𝓬ontiguity
-- -- -- --   open Contiguity ⦃ … ⦄ public

-- -- -- -- module _
-- -- -- --   {a} {A : Ø a}
-- -- -- --   {b} (B : A → A → Ø b)
-- -- -- --   where
-- -- -- --   𝓽ransitivity = 𝓬ontiguity B λ {x y z} f g → B x z
-- -- -- --   Transitivity = Contiguity B λ {x y z} f g → B x z

-- -- -- -- transitivity : ∀
-- -- -- --   {a} {A : Ø a}
-- -- -- --   {b} {B : A → A → Ø b}
-- -- -- --   ⦃ _ : Transitivity B ⦄
-- -- -- --   → 𝓽ransitivity B
-- -- -- -- transitivity = contiguity

-- -- -- -- infixr 9 _∙_
-- -- -- -- _∙_ : ∀ {a} {A : Ø a}
-- -- -- --         {b} {B : A → A → Ø b}
-- -- -- --       ⦃ _ : Transitivity B ⦄
-- -- -- --       → ∀ {y z x} → B y z → B x y → B x z
-- -- -- -- g ∙ f = contiguity f g

-- -- -- -- record IndexedEquivalence
-- -- -- --   {a} {A : Ø a} {b}
-- -- -- --     (B : A → Ø b)
-- -- -- --     c
-- -- -- --   : Ø a ∙̂ b ∙̂ ↑̂ c where
-- -- -- --   field
-- -- -- --     indexedEquivalence : ∀ {x} → B x → B x → Ø c
-- -- -- --     ⦃ ⌶IsSetoid ⦄ : ∀ {x} → IsSetoid (indexedEquivalence {x})
-- -- -- --   instance ⌶Equivalence : ∀ {x} → Equivalence (B x) c
-- -- -- --   Equivalence.equivalence ⌶Equivalence = indexedEquivalence

-- -- -- -- module _
-- -- -- --   {a} {A : Ø a} {b}
-- -- -- --     (B : A → A → Ø b)
-- -- -- --     c
-- -- -- --   where
-- -- -- --   𝓶orphismEquivalence = ∀ {x y} → B x y → B x y → Ø c

-- -- -- --   record MorphismEquivalence : Ø a ∙̂ b ∙̂ ↑̂ c where
-- -- -- --     field
-- -- -- --       morphismEquivalence : 𝓶orphismEquivalence
-- -- -- --       ⦃ ⌶IsSetoid ⦄ : ∀ {x y} → IsSetoid (morphismEquivalence {x} {y})
-- -- -- --     instance ⌶Equivalence : ∀ {x y} → Equivalence (B x y) c
-- -- -- --     Equivalence.equivalence ⌶Equivalence = morphismEquivalence

-- -- -- -- open MorphismEquivalence ⦃ … ⦄ public

-- -- -- -- record Congruity
-- -- -- --   a b {c} (C : ∀ {x} {X : Ø x} → X → X → Ø c)
-- -- -- --   : Ø ↑̂ (a ∙̂ b ∙̂ c) where
-- -- -- --   field congruity : ∀ {A : Ø a} {B : Ø b} {x y} (f : A → B) → C x y → C (f x) (f y)

-- -- -- -- open Congruity ⦃ … ⦄ public

-- -- -- -- record Congruity₂
-- -- -- --   a b c {ℓ} (EQ : ∀ {x} {X : Ø x} → X → X → Ø ℓ)
-- -- -- --   : Ø ↑̂ (a ∙̂ b ∙̂ c) ∙̂ ℓ where
-- -- -- --   field congruity₂ : ∀ {A : Ø a} {B : Ø b} {C : Ø c} {x y} {x' y'} (f : A → B → C) → EQ x y → EQ x' y' → EQ (f x x') (f y y')

-- -- -- -- open Congruity₂ ⦃ … ⦄ public

-- -- -- -- record Ċongruity
-- -- -- --   𝔬 𝔭 {c}
-- -- -- --   (C : ∀ {𝔒 : Ø 𝔬} {𝔓 : 𝔒 → Ø 𝔭} → ((𝓞 : 𝔒) → 𝔓 𝓞) → ((𝓞 : 𝔒) → 𝔓 𝓞) → Ø c)
-- -- -- --   : Ø ↑̂ (𝔬 ∙̂ 𝔭) ∙̂ c where
-- -- -- --   field ċongruity : ∀ {𝔒 : Ø 𝔬} {𝔓 : 𝔒 → Ø 𝔭} {f g : (𝓞 : 𝔒) → 𝔓 𝓞} (F : ∀ {𝓞 : 𝔒} → 𝔓 𝓞 → 𝔓 𝓞) → C f g → C (F ∘ f) (F ∘ g)

-- -- -- -- open Ċongruity ⦃ … ⦄ public

-- -- -- -- module _
-- -- -- --   {a₁} {A₁ : Ø a₁} {b₁} (B₁ : A₁ → A₁ → Ø b₁)
-- -- -- --   {a₂} {A₂ : Ø a₂} {b₂} (B₂ : A₂ → A₂ → Ø b₂)
-- -- -- --   c₂ ⦃ _ : MorphismEquivalence B₂ c₂ ⦄
-- -- -- --   (μ : A₁ → A₂)
-- -- -- --   ⦃ _ : Transitivity B₁ ⦄
-- -- -- --   ⦃ _ : Transitivity B₂ ⦄
-- -- -- --   ⦃ _ : Map B₁ (B₂ on μ) ⦄
-- -- -- --   where
-- -- -- --   𝓒ommutativity : ∀ {x y z} → B₁ x y → B₁ y z → Ø c₂
-- -- -- --   𝓒ommutativity = λ f g → map[ B₂ on μ ] (g ∙ f) ≋ map g ∙ map f
-- -- -- --   𝓬ommutativity = 𝓬ontiguity B₁ 𝓒ommutativity
-- -- -- --   Commutativity = Contiguity B₁ 𝓒ommutativity

-- -- -- -- commutativity : ∀
-- -- -- --   {a} {A : Ø a}
-- -- -- --   {b} {B : A → A → Ø b}
-- -- -- --   {c} {C : ∀ {x y z} → B x y → B y z → Ø c}
-- -- -- --   ⦃ _ : Contiguity B C ⦄
-- -- -- --   → 𝓬ontiguity B C
-- -- -- -- commutativity = contiguity

-- -- -- -- commutativity[_] : ∀
-- -- -- --   {a₁} {A₁ : Ø a₁} {b₁} {B₁ : A₁ → A₁ → Ø b₁}
-- -- -- --   {a₂} {A₂ : Ø a₂} {b₂} (B₂ : A₂ → A₂ → Ø b₂)
-- -- -- --   {c₂} ⦃ _ : MorphismEquivalence B₂ c₂ ⦄
-- -- -- --   {μ : A₁ → A₂}
-- -- -- --   ⦃ _ : Transitivity B₁ ⦄
-- -- -- --   ⦃ _ : Transitivity B₂ ⦄
-- -- -- --   ⦃ _ : Map B₁ (B₂ on μ) ⦄
-- -- -- --   ⦃ _ : Commutativity B₁ B₂ c₂ μ ⦄
-- -- -- --   → 𝓬ommutativity B₁ B₂ c₂ μ
-- -- -- -- commutativity[ _ ] = contiguity

-- -- -- -- module _
-- -- -- --   {a} {A : Ø a}
-- -- -- --   {b} (B : A → Ø b)
-- -- -- --   where
-- -- -- --   𝓲dentity′ = ∀ {x} → B x
-- -- -- --   record Identity′ : Ø a ∙̂ b where field identity : 𝓲dentity′

-- -- -- -- open Identity′ ⦃ … ⦄ public

-- -- -- -- module _
-- -- -- --   {a₁} {A₁ : Ø a₁} {b₁} (B₁ : A₁ → A₁ → Ø b₁)
-- -- -- --   {a₂} {A₂ : Ø a₂} {b₂} (B₂ : A₂ → A₂ → Ø b₂) c₂ ⦃ _ : MorphismEquivalence B₂ c₂ ⦄
-- -- -- --   (μ : A₁ → A₂)
-- -- -- --   ⦃ _ : Reflexivity B₁ ⦄
-- -- -- --   ⦃ _ : Reflexivity B₂ ⦄
-- -- -- --   ⦃ _ : Map B₁ (B₂ on μ) ⦄
-- -- -- --   where
-- -- -- --   𝓘dentity : A₁ → Ø c₂
-- -- -- --   𝓘dentity = λ x → map (ε[ B₁ ] {x = x}) ≋ ε[ B₂ ] {x = μ x}
-- -- -- --   𝓲dentity = 𝓲dentity′ 𝓘dentity
-- -- -- --   Identity = Identity′ 𝓘dentity

-- -- -- -- record LeftIdentity
-- -- -- --   {a} {A : Ø a} {b}
-- -- -- --     (B : A → A → Ø b)
-- -- -- --     c
-- -- -- --     ⦃ _ : MorphismEquivalence B c ⦄
-- -- -- --     ⦃ _ : Reflexivity B ⦄
-- -- -- --     ⦃ _ : Transitivity B ⦄
-- -- -- --   : Ø a ∙̂ b ∙̂ c where
-- -- -- --   field left-identity : ∀ {x y} (f : B x y) → ε ∙ f ≋ f

-- -- -- -- open LeftIdentity ⦃ … ⦄ public

-- -- -- -- record RightIdentity
-- -- -- --   {a} {A : Ø a} {b}
-- -- -- --     (B : A → A → Ø b)
-- -- -- --     c
-- -- -- --     ⦃ _ : MorphismEquivalence B c ⦄
-- -- -- --     ⦃ _ : Reflexivity B ⦄
-- -- -- --     ⦃ _ : Transitivity B ⦄
-- -- -- --   : Ø a ∙̂ b ∙̂ c where
-- -- -- --   field right-identity : ∀ {x y} (f : B x y) → f ∙ ε ≋ f
-- -- -- -- open RightIdentity ⦃ … ⦄ public

-- -- -- -- record Associativity
-- -- -- --   {a} {A : Ø a} {b}
-- -- -- --     (B : A → A → Ø b)
-- -- -- --     c
-- -- -- --     ⦃ _ : MorphismEquivalence B c ⦄
-- -- -- --     ⦃ _ : Transitivity B ⦄
-- -- -- --   : Ø a ∙̂ b ∙̂ c where
-- -- -- --   field associativity : ∀ {w x y z} (f : B w x) (g : B x y) (h : B y z) → (h ∙ g) ∙ f ≋ h ∙ g ∙ f
-- -- -- -- open Associativity ⦃ … ⦄ public


-- -- -- -- module _
-- -- -- --   {a} {A : Ø a}
-- -- -- --   {b} (B : A → A → Ø b)
-- -- -- --   {c} (C : ∀ {x y} → B x y → B x y → Ø c)
-- -- -- --   {d} (D : ∀ {x y} → B x y → B x y → Ø d)
-- -- -- --   where

-- -- -- --   𝓮xtensionality₁′ : Ø a ∙̂ b ∙̂ c ∙̂ d
-- -- -- --   𝓮xtensionality₁′ = ∀ {x y} {f₁ f₂ : B x y} → C f₁ f₂ → D f₁ f₂

-- -- -- --   record Extensionality₁′ : Ø a ∙̂ b ∙̂ c ∙̂ d where field extensionality₁ : 𝓮xtensionality₁′

-- -- -- -- open Extensionality₁′ ⦃ … ⦄ public

-- -- -- -- module _
-- -- -- --   {a₁} {A₁ : Ø a₁} {b₁} (B₁ : A₁ → A₁ → Ø b₁) c₁ ⦃ _ : MorphismEquivalence B₁ c₁ ⦄
-- -- -- --   {a₂} {A₂ : Ø a₂} {b₂} (B₂ : A₂ → A₂ → Ø b₂) c₂ ⦃ _ : MorphismEquivalence B₂ c₂ ⦄
-- -- -- --   (μ : A₁ → A₂)
-- -- -- --   ⦃ _ : Map B₁ (B₂ on μ) ⦄
-- -- -- --   where
-- -- -- --   Extensionality₁ = Extensionality₁′ B₁ _≋_ (λ f₁ f₂ → map[ B₂ on μ ] f₁ ≋ map f₂)
-- -- -- --   𝓮xtensionality₁ = 𝓮xtensionality₁′ B₁ _≋_ (λ f₁ f₂ → map[ B₂ on μ ] f₁ ≋ map f₂)

-- -- -- -- module _
-- -- -- --   {a} {A : Ø a}
-- -- -- --   {b} (B : A → A → Ø b)
-- -- -- --   {c} (C : ∀ {x y} → B x y → B x y → Ø c)
-- -- -- --   {d} (D : ∀ {x y} → B x y → B x y → ∀ {z} → B y z → B y z → Ø d)
-- -- -- --   where

-- -- -- --   𝓮xtensionality₂′ = ∀ {x y} {f₁ f₂ : B x y} {z} {g₁ g₂ : B y z} → C f₁ f₂ → C g₁ g₂ → D f₁ f₂ g₁ g₂
-- -- -- --   record Extensionality₂′ : Ø a ∙̂ b ∙̂ c ∙̂ d where field extensionality₂ : 𝓮xtensionality₂′

-- -- -- -- open Extensionality₂′ ⦃ … ⦄ public

-- -- -- -- module _
-- -- -- --   {a} {A : Ø a} {b} (B : A → A → Ø b) c ⦃ _ : MorphismEquivalence B c ⦄
-- -- -- --   ⦃ _ : Transitivity B ⦄
-- -- -- --   where
-- -- -- --   𝓮xtensionality₂ = 𝓮xtensionality₂′ B equivalence (λ f₁ f₂ g₁ g₂ → g₁ ∙ f₁ ≋ g₂ ∙ f₂)
-- -- -- --   Extensionality₂ = Extensionality₂′ B equivalence (λ f₁ f₂ g₁ g₂ → g₁ ∙ f₁ ≋ g₂ ∙ f₂)

-- -- -- -- record IsCategory
-- -- -- --   {a} {A : Ø a} {b}
-- -- -- --     (B : A → A → Ø b)
-- -- -- --     c
-- -- -- --     ⦃ _ : MorphismEquivalence B c ⦄
-- -- -- --   : Ø a ∙̂ b ∙̂ c where
-- -- -- --   field
-- -- -- --     ⦃ ⌶IsSemigroupoid ⦄ : IsSemigroupoid B c
-- -- -- --     ⦃ ⌶Reflexivity ⦄ : Reflexivity B
-- -- -- --     ⦃ ⌶LeftIdentity ⦄ : LeftIdentity B c
-- -- -- --     ⦃ ⌶RightIdentity ⦄ : RightIdentity B c

-- -- -- -- record IsSemifunctor
-- -- -- --   {a₁} {A₁ : Ø a₁} {b₁} (B₁ : A₁ → A₁ → Ø b₁) c₁ ⦃ _ : MorphismEquivalence B₁ c₁ ⦄
-- -- -- --   {a₂} {A₂ : Ø a₂} {b₂} (B₂ : A₂ → A₂ → Ø b₂) c₂ ⦃ _ : MorphismEquivalence B₂ c₂ ⦄
-- -- -- --   (μ : A₁ → A₂)
-- -- -- --   : Ø a₁ ∙̂ b₁ ∙̂ c₁ ∙̂ a₂ ∙̂ b₂ ∙̂ c₂
-- -- -- --   where
-- -- -- --   field
-- -- -- --     ⦃ ⌶IsSemigroupoid₁ ⦄ : IsSemigroupoid B₁ c₁
-- -- -- --     ⦃ ⌶IsSemigroupoid₂ ⦄ : IsSemigroupoid B₂ c₂
-- -- -- --     ⦃ ⌶Map ⦄ : Map B₁ (B₂ on μ)
-- -- -- --     ⦃ ⌶Extensionality₁ ⦄ : Extensionality₁ B₁ c₁ B₂ c₂ μ
-- -- -- --     ⦃ ⌶Commutativity ⦄ : Commutativity B₁ B₂ c₂ μ

-- -- -- -- record IsFunctor
-- -- -- --   {a₁} {A₁ : Ø a₁} {b₁} (B₁ : A₁ → A₁ → Ø b₁) c₁ ⦃ _ : MorphismEquivalence B₁ c₁ ⦄
-- -- -- --   {a₂} {A₂ : Ø a₂} {b₂} (B₂ : A₂ → A₂ → Ø b₂) c₂ ⦃ _ : MorphismEquivalence B₂ c₂ ⦄
-- -- -- --   (μ : A₁ → A₂)
-- -- -- --   : Ø a₁ ∙̂ b₁ ∙̂ c₁ ∙̂ a₂ ∙̂ b₂ ∙̂ c₂
-- -- -- --   where
-- -- -- --   field
-- -- -- --     ⦃ ⌶IsCategory₁ ⦄ : IsCategory B₁ c₁
-- -- -- --     ⦃ ⌶IsCategory₂ ⦄ : IsCategory B₂ c₂
-- -- -- --     ⦃ ⌶IsSemifunctor ⦄ : IsSemifunctor B₁ c₁ B₂ c₂ μ
-- -- -- --     ⦃ ⌶Identity ⦄ : Identity B₁ B₂ c₂ μ

-- -- -- -- record Setoid a b : Ø ↑̂ (a ∙̂ b) where
-- -- -- --   field
-- -- -- --     Object : Ø a
-- -- -- --     Eq : Object → Object → Ø b
-- -- -- --     ⦃ ⌶IsSetoid ⦄ : IsSetoid Eq

-- -- -- -- record Semigroupoid a b c : Ø ↑̂ (a ∙̂ b ∙̂ c) where
-- -- -- --   field
-- -- -- --     Object : Ø a
-- -- -- --     Morphism : Object → Object → Ø b
-- -- -- --     ⦃ ⌶MorophismEquivalence ⦄ : MorphismEquivalence Morphism c
-- -- -- --     ⦃ ⌶IsSemigroupoid ⦄ : IsSemigroupoid Morphism c

-- -- -- -- record Category a b c : Ø ↑̂ (a ∙̂ b ∙̂ c) where
-- -- -- --   field
-- -- -- --     Object : Ø a
-- -- -- --     Morphism : Object → Object → Ø b
-- -- -- --     ⦃ ⌶MorophismEquivalence ⦄ : MorphismEquivalence Morphism c
-- -- -- --     ⦃ ⌶IsCategory ⦄ : IsCategory Morphism c

-- -- -- -- record Semifunctor a b c d e f : Ø ↑̂ (a ∙̂ b ∙̂ c ∙̂ d ∙̂ e ∙̂ f) where
-- -- -- --   field
-- -- -- --     Object₁ : Ø a
-- -- -- --     Morphism₁ : Object₁ → Object₁ → Ø b
-- -- -- --     ⦃ ⌶MorophismEquivalence₁ ⦄ : MorphismEquivalence Morphism₁ c
-- -- -- --     Object₂ : Ø d
-- -- -- --     Morphism₂ : Object₂ → Object₂ → Ø e
-- -- -- --     ⦃ ⌶MorophismEquivalence₂ ⦄ : MorphismEquivalence Morphism₂ f
-- -- -- --     μ : Object₁ → Object₂
-- -- -- --     ⦃ ⌶IsSemifunctor ⦄ : IsSemifunctor Morphism₁ c Morphism₂ f μ

-- -- -- -- record Functor a b c d e f : Ø ↑̂ (a ∙̂ b ∙̂ c ∙̂ d ∙̂ e ∙̂ f) where
-- -- -- --   field
-- -- -- --     Object₁ : Ø a
-- -- -- --     Morphism₁ : Object₁ → Object₁ → Ø b
-- -- -- --     ⦃ ⌶MorophismEquivalence₁ ⦄ : MorphismEquivalence Morphism₁ c
-- -- -- --     Object₂ : Ø d
-- -- -- --     Morphism₂ : Object₂ → Object₂ → Ø e
-- -- -- --     ⦃ ⌶MorophismEquivalence₂ ⦄ : MorphismEquivalence Morphism₂ f
-- -- -- --     μ : Object₁ → Object₂
-- -- -- --     ⦃ ⌶IsFunctor ⦄ : IsFunctor Morphism₁ c Morphism₂ f μ

-- -- -- -- module _ where

-- -- -- --   record Successor₀ {x} (X : Ø x) : Ø x where
-- -- -- --     field
-- -- -- --       ⇑₀ : X → X
-- -- -- --   open Successor₀ ⦃ … ⦄ public

-- -- -- --   record Principal₁ {x} {X : Ø x} {a} (A : X → Ø a) : Ø₀ where no-eta-equality
-- -- -- --   record Principal₁₊₁ {x} {X : Ø x} {a} (A : X → Ø a) {b} (B : X → Ø b) : Ø₀ where no-eta-equality

-- -- -- --   record Successor₁ {x} {X : Ø x} {a} (A : X → Ø a)
-- -- -- --     ⦃ _ : Successor₀ X ⦄
-- -- -- --     ⦃ _ : Principal₁ A ⦄
-- -- -- --     : Ø x ∙̂ a where
-- -- -- --     field
-- -- -- --       ⇑₁ : ∀ {m} → A m → A (⇑₀ m)
-- -- -- --   open Successor₁ ⦃ … ⦄ public

-- -- -- --   record Thin {x} {X : Ø x} {a} (A : X → Ø a) {b} (B : X → Ø b)
-- -- -- --     ⦃ _ : Successor₀ X ⦄
-- -- -- --     ⦃ _ : Principal₁ A ⦄
-- -- -- --     ⦃ _ : Principal₁ B ⦄
-- -- -- --     : Ø x ∙̂ a ∙̂ b where
-- -- -- --     field
-- -- -- --       thin : ∀ {m : X} → A (⇑₀ m) → B m → B (⇑₀ m)
-- -- -- --   open Thin ⦃ … ⦄ public

-- -- -- --   thin[_] : ∀
-- -- -- --     {x} {X : Ø x} {a} {A : X → Ø a} {b} (B : X → Ø b)
-- -- -- --     ⦃ _ : Successor₀ X ⦄
-- -- -- --     ⦃ _ : Principal₁ A ⦄
-- -- -- --     ⦃ _ : Principal₁ B ⦄
-- -- -- --     ⦃ _ : Thin A B ⦄
-- -- -- --     → ∀ {m : X} → A (⇑₀ m) → B m → B (⇑₀ m)
-- -- -- --   thin[ _ ] = thin

-- -- -- --   record Injectivity₀
-- -- -- --     {a} {A : Ø a}
-- -- -- --     {b} {B : Ø b}
-- -- -- --     (f : A → B)
-- -- -- --     ℓa
-- -- -- --     ℓb
-- -- -- --     ⦃ _ : Equivalence B ℓb ⦄
-- -- -- --     ⦃ _ : Equivalence A ℓa ⦄
-- -- -- --     : Ø a ∙̂ b ∙̂ ℓa ∙̂ ℓb where
-- -- -- --     field injectivity₀ : ∀ {x y} → f x ≋ f y → x ≋ y
-- -- -- --   open Injectivity₀ ⦃ … ⦄ public

-- -- -- --   injectivity₀[_] : ∀
-- -- -- --     {a} {A : Ø a}
-- -- -- --     {b} {B : Ø b}
-- -- -- --     (f : A → B)
-- -- -- --     {ℓa}
-- -- -- --     {ℓb}
-- -- -- --     ⦃ _ : Equivalence A ℓa ⦄
-- -- -- --     ⦃ _ : Equivalence B ℓb ⦄
-- -- -- --     ⦃ _ : Injectivity₀ f ℓa ℓb ⦄
-- -- -- --     → ∀ {x y} → f x ≋ f y → x ≋ y
-- -- -- --   injectivity₀[ f ] = injectivity₀ { f = f }

-- -- -- --   record Injectivity!
-- -- -- --     {a} {A : Ø a}
-- -- -- --     {b} {B : A → Ø b}
-- -- -- --     {c} (C : ∀ x → B x → B x → Ø c)
-- -- -- --     {d} (D : ∀ x → B x → B x → Ø d)
-- -- -- --     : Ø a ∙̂ b ∙̂ c ∙̂ d where
-- -- -- --     field injectivity! : ∀ w {x y : B w} → C w x y → D w x y
-- -- -- --   open Injectivity! ⦃ … ⦄ public

-- -- -- --   module _
-- -- -- --     {a} {A : Ø a}
-- -- -- --     {b} {B : A → Ø b}
-- -- -- --     {c} {C : A → Ø c}
-- -- -- --     (f : (x : A) → B x → C x)
-- -- -- --     ℓb
-- -- -- --     ℓc
-- -- -- --     ⦃ _ : ∀ {x} → Equivalence (B x) ℓb ⦄
-- -- -- --     ⦃ _ : ∀ {x} → Equivalence (C x) ℓc ⦄
-- -- -- --     where
-- -- -- --     Injectivity? = Injectivity! (λ w x y → f w x ≋ f w y) (λ w x y → x ≋ y)

-- -- -- --   injectivity?[_] : ∀
-- -- -- --     {a} {A : Ø a}
-- -- -- --     {b} {B : A → Ø b}
-- -- -- --     {c} {C : A → Ø c}
-- -- -- --     (f : (x : A) → B x → C x)
-- -- -- --     {ℓb}
-- -- -- --     {ℓc}
-- -- -- --     ⦃ _ : ∀ {x} → Equivalence (B x) ℓb ⦄
-- -- -- --     ⦃ _ : ∀ {x} → Equivalence (C x) ℓc ⦄
-- -- -- --     ⦃ _ : Injectivity? f ℓb ℓc ⦄
-- -- -- --     → ∀ w {x y} → f w x ≋ f w y → x ≋ y
-- -- -- --   injectivity?[ _ ] = injectivity!

-- -- -- --   record Injectivity₁
-- -- -- --     {a} {A : Ø a}
-- -- -- --     {b} {B : A → Ø b}
-- -- -- --     {c} {C : A → Ø c}
-- -- -- --     (f : (x : A) → B x → C x)
-- -- -- --     ℓb
-- -- -- --     ℓc
-- -- -- --     ⦃ _ : ∀ {x} → Equivalence (B x) ℓb ⦄
-- -- -- --     ⦃ _ : ∀ {x} → Equivalence (C x) ℓc ⦄
-- -- -- --     : Ø a ∙̂ b ∙̂ ℓb ∙̂ ℓc where
-- -- -- --     field injectivity₁ : ∀ w {x y} → f w x ≋ f w y → x ≋ y
-- -- -- --   open Injectivity₁ ⦃ … ⦄ public

-- -- -- --   injectivity₁[_] : ∀
-- -- -- --     {a} {A : Ø a}
-- -- -- --     {b} {B : A → Ø b}
-- -- -- --     {c} {C : A → Ø c}
-- -- -- --     (f : (x : A) → B x → C x)
-- -- -- --     {ℓb}
-- -- -- --     {ℓc}
-- -- -- --     ⦃ _ : ∀ {x} → Equivalence (B x) ℓb ⦄
-- -- -- --     ⦃ _ : ∀ {x} → Equivalence (C x) ℓc ⦄
-- -- -- --     ⦃ _ : Injectivity₁ f ℓb ℓc ⦄
-- -- -- --     → ∀ w {x y} → f w x ≋ f w y → x ≋ y
-- -- -- --   injectivity₁[ f ] = injectivity₁ {f = f}

-- -- -- --   record Injectivity₂
-- -- -- --     {a} {A : Ø a}
-- -- -- --     {b} {B : Ø b}
-- -- -- --     {c} {C : Ø c}
-- -- -- --     (f : A → B → C)
-- -- -- --     ℓb
-- -- -- --     ℓc
-- -- -- --     ⦃ _ : Equivalence B ℓb ⦄
-- -- -- --     ⦃ _ : Equivalence C ℓc ⦄
-- -- -- --     : Ø a ∙̂ b ∙̂ ℓb ∙̂ ℓc where
-- -- -- --     field injectivity₂ : ∀ w {x y} → f w x ≋ f w y → x ≋ y
-- -- -- --   open Injectivity₂ ⦃ … ⦄ public

-- -- -- --   injectivity₂[_] : ∀
-- -- -- --     {a} {A : Ø a}
-- -- -- --     {b} {B : Ø b}
-- -- -- --     {c} {C : Ø c}
-- -- -- --     (f : A → B → C)
-- -- -- --     {ℓb}
-- -- -- --     {ℓc}
-- -- -- --     ⦃ _ : Equivalence B ℓb ⦄
-- -- -- --     ⦃ _ : Equivalence C ℓc ⦄
-- -- -- --     ⦃ _ : Injectivity₂ f ℓb ℓc ⦄
-- -- -- --     → ∀ w {x y} → f w x ≋ f w y → x ≋ y
-- -- -- --   injectivity₂[ f ] = injectivity₂ {f = f}

-- -- -- --   record ThinInjective {x} {X : Ø x} {a} (A : X → Ø a) {b} (B : X → Ø b) c
-- -- -- --     ⦃ _ : Successor₀ X ⦄
-- -- -- --     ⦃ _ : ∀ {x} → Equivalence (B x) c ⦄
-- -- -- --     ⦃ _ : Principal₁ A ⦄
-- -- -- --     ⦃ _ : Principal₁ B ⦄
-- -- -- --     ⦃ _ : Thin A B ⦄
-- -- -- --     : Ø x ∙̂ a ∙̂ b ∙̂ ↑̂ c where
-- -- -- --     field
-- -- -- --       ⦃ ⌶Injectivity₁ ⦄ : ∀ {m : X} → Injectivity₁ {A = A (⇑₀ m)} {B = λ _ → B _} (λ w x → thin w x) c c
-- -- -- --       ⦃ ⌶Injectivity₂ ⦄ : ∀ {m : X} → Injectivity₂ (λ (w : A (⇑₀ m)) x → thin[ B ] w x) c c
-- -- -- --       -- (thin[ B ] {m = m})
-- -- -- --     thin-injective : ∀ {m : X} (x : A (⇑₀ m)) {y₁ y₂ : B m} → thin x y₁ ≋ thin x y₂ → y₁ ≋ y₂
-- -- -- --     thin-injective = injectivity₁[ thin ]
-- -- -- --     -- injectivity₂[ thin[ B ] ]
-- -- -- --     -- injectivity₁[ thin ]
-- -- -- --   open ThinInjective ⦃ … ⦄ public

-- -- -- --   record Thick {x} {X : Ø x} {a} (A : X → Ø a) {b} (B : X → Ø b)
-- -- -- --     ⦃ _ : Successor₀ X ⦄
-- -- -- --     ⦃ _ : Principal₁ B ⦄
-- -- -- --     : Ø x ∙̂ a ∙̂ b where
-- -- -- --     field
-- -- -- --       thick : ∀ {m} → B (⇑₀ m) → A m → B m
-- -- -- --   open Thick ⦃ … ⦄ public

-- -- -- --   record ThickThinId {x} {X : Ø x} {a} (A : X → Ø a) {b} (B : X → Ø b) c
-- -- -- --     ⦃ _ : Successor₀ X ⦄
-- -- -- --     ⦃ _ : Principal₁ A ⦄
-- -- -- --     ⦃ _ : Principal₁ B ⦄
-- -- -- --     ⦃ _ : Successor₁ A ⦄
-- -- -- --     ⦃ _ : ∀ {x} → Equivalence (B x) c ⦄
-- -- -- --     ⦃ _ : Thin A B ⦄
-- -- -- --     ⦃ _ : Thick A B ⦄
-- -- -- --     : Ø x ∙̂ a ∙̂ b ∙̂ ↑̂ c where
-- -- -- --     field
-- -- -- --       thick∘thin=id : ∀ {m} (x : A m) (y : B m) → thick (thin (⇑₁ x) y) x ≋ y
-- -- -- --   open ThickThinId ⦃ … ⦄ public

-- -- -- --   record Maybe* a : Ø ↑̂ a where
-- -- -- --     field
-- -- -- --       Maybe : Ø a → Ø a
-- -- -- --       just : ∀ {A} → A → Maybe A
-- -- -- --       nothing : ∀ {A} → Maybe A
-- -- -- --   open Maybe* ⦃ … ⦄ -- public

-- -- -- --   record Check {x} {X : Ø x} {a} (A : X → Ø a) {b} (B : X → Ø b)
-- -- -- --     ⦃ _ : Successor₀ X ⦄
-- -- -- --     ⦃ _ : Principal₁ A ⦄
-- -- -- --     ⦃ _ : Principal₁ B ⦄
-- -- -- --     ⦃ _ : Maybe* b ⦄
-- -- -- --     : Ø x ∙̂ a ∙̂ ↑̂ b where
-- -- -- --     field
-- -- -- --       check : ∀ {m} → A (⇑₀ m) → B (⇑₀ m) → Maybe (B m)
-- -- -- --   open Check ⦃ … ⦄ public

-- -- -- --   record ThinCheckId {x} {X : Ø x} {a} (A : X → Ø a) {b} (B : X → Ø b) ℓb ℓc
-- -- -- --     ⦃ _ : Successor₀ X ⦄
-- -- -- --     ⦃ _ : Maybe* b ⦄
-- -- -- --     ⦃ _ : ∀ {x} → Equivalence (B x) ℓb ⦄
-- -- -- --     ⦃ _ : ∀ {x} → Equivalence (Maybe (B x)) ℓc ⦄
-- -- -- --     ⦃ _ : Principal₁ A ⦄
-- -- -- --     ⦃ _ : Principal₁ B ⦄
-- -- -- --     ⦃ _ : Thin A B ⦄
-- -- -- --     ⦃ _ : Check A B ⦄
-- -- -- --     : Ø x ∙̂ a ∙̂ b ∙̂ ℓb ∙̂ ℓc where
-- -- -- --     field
-- -- -- --       thin-check-id : ∀ {m} (x : A (⇑₀ m)) y → ∀ (y' : B m) → thin x y' ≋ y → check x y ≋ just y'
-- -- -- --   open ThinCheckId ⦃ … ⦄ public

-- -- -- --   test-thin-check-id : ∀ {x} {X : Ø x} {a} (A : X → Ø a) {b} (B : X → Ø b) ℓb ℓc
-- -- -- --                          ⦃ _ : Successor₀ X ⦄
-- -- -- --                          ⦃ _ : ∀ {x} → Equivalence (B x) ℓb ⦄
-- -- -- --                          ⦃ _ : Maybe* b ⦄
-- -- -- --                          ⦃ _ : ∀ {x} → Equivalence (Maybe (B x)) ℓc ⦄
-- -- -- --                          ⦃ _ : Principal₁ A ⦄
-- -- -- --                          ⦃ _ : Principal₁ B ⦄
-- -- -- --                          ⦃ _ : Thin A B ⦄
-- -- -- --                          ⦃ _ : Check A B ⦄
-- -- -- --                          ⦃ _ : ThinCheckId A B ℓb ℓc ⦄
-- -- -- --                          → ∀ {m} (x : A (⇑₀ m)) y → ∀ (y' : B m) → thin x y' ≋ y → check x y ≋ just y'
-- -- -- --   test-thin-check-id A B ℓb ℓc = thin-check-id

-- -- -- --   record ThickAndThin {x} {X : Ø x} {a} (A : X → Ø a) {b} (B : X → Ø b) c ℓc
-- -- -- --     ⦃ _ : Successor₀ X ⦄
-- -- -- --     ⦃ _ : Principal₁ A ⦄
-- -- -- --     ⦃ _ : Principal₁ B ⦄
-- -- -- --     ⦃ _ : Successor₁ A ⦄
-- -- -- --     ⦃ _ : Maybe* b ⦄
-- -- -- --     ⦃ _ : ∀ {x} → Equivalence (B x) c ⦄
-- -- -- --     ⦃ _ : ∀ {x} → Equivalence (Maybe (B x)) ℓc ⦄
-- -- -- --     : Ø x ∙̂ a ∙̂ ↑̂ b ∙̂ ↑̂ c ∙̂ ↑̂ ℓc where
-- -- -- --     field
-- -- -- --       ⦃ iThin ⦄ : Thin A B
-- -- -- --       ⦃ iThinInjective ⦄ : ThinInjective A B c
-- -- -- --       ⦃ iThick ⦄ : Thick A B
-- -- -- --       ⦃ iThickThinId ⦄ : ThickThinId A B c
-- -- -- --       ⦃ iCheck ⦄ : Check A B
-- -- -- --       ⦃ iThinCheckId ⦄ : ThinCheckId A B c ℓc
-- -- -- --   open ThickAndThin ⦃ … ⦄

-- -- -- -- module _ where

-- -- -- --   record FMap {x} {y} (F : Ø x → Ø y) : Ø (↑̂ x) ∙̂ y where
-- -- -- --     field fmap : ∀ {A B : Ø x} → (A → B) → F A → F B
