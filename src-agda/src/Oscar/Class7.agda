{-# OPTIONS --show-implicit #-}
module Oscar.Class7 where

open import Oscar.Prelude

module _
  {a} {A : Set a}
  {b} (B : A → A → Set b)
  where
  𝓻eflexivity = ∀ {x} → B x x
  record Reflexivity : Ø a ∙̂ b where field reflexivity : 𝓻eflexivity
  open Reflexivity ⦃ … ⦄ public

ε : ∀ {a} {A : Set a}
      {b} {B : A → A → Set b}
    ⦃ _ : Reflexivity B ⦄
    → ∀ {x} → B x x
ε = reflexivity

ε[_] : ∀ {a} {A : Set a}
         {b} (B : A → A → Set b)
       ⦃ _ : Reflexivity B ⦄
       → ∀ {x} → B x x
ε[ _ ] = reflexivity

module _
  {a} {A : Set a}
  {b} (B : A → A → Set b)
  where
  𝓼ymmetry = ∀ {x y} → B x y → B y x
  record Symmetry : Ø a ∙̂ b where field symmetry : 𝓼ymmetry
  open Symmetry ⦃ … ⦄ public

module _
  {a} {A : Set a}
  {b} (B : A → A → Set b)
  where
  𝓽ransitivity = ∀ {x y z} → B x y → B y z → B x z
  record Transitivity : Ø a ∙̂ b where field transitivity : 𝓽ransitivity
  open Transitivity ⦃ … ⦄ public

record IsSetoid
  {a} {A : Set a}
  {b} (B : A → A → Set b) : Ø a ∙̂ b where
  field
    ⦃ ⌶Reflexivity ⦄ : Reflexivity B
    ⦃ ⌶Symmetry ⦄ : Symmetry B
    ⦃ ⌶Transitivity ⦄ : Transitivity B

record Equivalence
  {a}
    (A : Set a)
    b
  : Ø a ∙̂ ↑̂ b where
  field
    equivalence : A → A → Ø b
    ⦃ ⌶IsSetoid ⦄ : IsSetoid equivalence

open Equivalence ⦃ … ⦄ public

infix 4 _≋_
_≋_ : ∀ {a} {A : Set a} {b} ⦃ _ : Equivalence A b ⦄ → A → A → Ø b
_≋_ = equivalence

record IndexedEquivalence
  {a} {A : Set a} {b}
    (B : A → Set b)
    c
  : Ø a ∙̂ b ∙̂ ↑̂ c where
  field
    indexedEquivalence : ∀ {x} → B x → B x → Ø c
    ⦃ ⌶IsSetoid ⦄ : ∀ {x} → IsSetoid (indexedEquivalence {x})
  instance ⌶Equivalence : ∀ {x} → Equivalence (B x) c
  Equivalence.equivalence ⌶Equivalence = indexedEquivalence

record MorphismEquivalence
  {a} {A : Set a} {b}
    (B : A → A → Set b)
    c
  : Ø a ∙̂ b ∙̂ ↑̂ c where
  field
    morphismEquivalence : ∀ {x y} → B x y → B x y → Ø c
    ⦃ ⌶IsSetoid ⦄ : ∀ {x y} → IsSetoid (morphismEquivalence {x} {y})
  instance ⌶Equivalence : ∀ {x y} → Equivalence (B x y) c
  Equivalence.equivalence ⌶Equivalence = morphismEquivalence

open MorphismEquivalence ⦃ … ⦄ public

record Congruity
  a b {c} (C : ∀ {x} {X : Set x} → X → X → Set c)
  : Ø ↑̂ (a ∙̂ b ∙̂ c) where
  field congruity : ∀ {A : Set a} {B : Set b} {x y} (f : A → B) → C x y → C (f x) (f y)

open Congruity ⦃ … ⦄ public

record Congruity₂
  a b c {ℓ} (EQ : ∀ {x} {X : Set x} → X → X → Set ℓ)
  : Ø ↑̂ (a ∙̂ b ∙̂ c) ∙̂ ℓ where
  field congruity₂ : ∀ {A : Set a} {B : Set b} {C : Set c} {x y} {x' y'} (f : A → B → C) → EQ x y → EQ x' y' → EQ (f x x') (f y y')

open Congruity₂ ⦃ … ⦄ public

record Ċongruity
  𝔬 𝔭 {c}
  (C : ∀ {𝔒 : Ø 𝔬} {𝔓 : 𝔒 → Ø 𝔭} → ((𝓞 : 𝔒) → 𝔓 𝓞) → ((𝓞 : 𝔒) → 𝔓 𝓞) → Ø c)
  : Ø ↑̂ (𝔬 ∙̂ 𝔭) ∙̂ c where
  field ċongruity : ∀ {𝔒 : Ø 𝔬} {𝔓 : 𝔒 → Ø 𝔭} {f g : (𝓞 : 𝔒) → 𝔓 𝓞} (F : ∀ {𝓞 : 𝔒} → 𝔓 𝓞 → 𝔓 𝓞) → C f g → C (F ∘ f) (F ∘ g)

open Ċongruity ⦃ … ⦄ public

𝓶ap : ∀
  {a} {A : Set a}
  {b} (B : A → A → Set b)
  {c} (C : A → A → Set c)
  → Ø a ∙̂ b ∙̂ c
𝓶ap B C = ∀ {x y} → B x y → C x y

record Map
  {a} {A : Set a}
  {b} (B : A → A → Set b)
  {c} (C : A → A → Set c)
  : Ø a ∙̂ b ∙̂ c where
  field map : 𝓶ap B C

open Map ⦃ … ⦄ public

map[_] : ∀
  {a} {A : Set a}
  {b} {B : A → A → Set b}
  {c} (C : A → A → Set c)
  ⦃ _ : Map B C ⦄
  → ∀ {x y} → B x y → C x y
map[ C ] f = map f

module _
  {a} {A : Set a}
  {b} (B : A → Set b)
  where
  𝓲dentity′ = ∀ {x} → B x
  record Identity′ : Ø a ∙̂ b where field identity : 𝓲dentity′

open Identity′ ⦃ … ⦄ public

module _
  {a₁} {A₁ : Ø a₁} {b₁} (B₁ : A₁ → A₁ → Ø b₁)
  {a₂} {A₂ : Ø a₂} {b₂} (B₂ : A₂ → A₂ → Ø b₂) c₂ ⦃ _ : MorphismEquivalence B₂ c₂ ⦄
  (μ : A₁ → A₂)
  ⦃ _ : Reflexivity B₁ ⦄
  ⦃ _ : Reflexivity B₂ ⦄
  ⦃ _ : Map B₁ (B₂ on μ) ⦄
  where
  𝓘dentity : A₁ → Ø c₂
  𝓘dentity = λ x → map (ε[ B₁ ] {x = x}) ≋ ε[ B₂ ] {x = μ x}
  𝓲dentity = 𝓲dentity′ 𝓘dentity
  Identity = Identity′ 𝓘dentity

module _
  {a₂} {A₂ : Ø a₂} {b₂} (B₂ : A₂ → A₂ → Ø b₂) c₂ ⦃ _ : MorphismEquivalence B₂ c₂ ⦄
  (μ : A₂ → A₂)
  ⦃ _ : Reflexivity B₂ ⦄
  ⦃ _ : Map B₂ (B₂ on μ) ⦄
  where
  record Identity! : Ø a₂ ∙̂ c₂ where
    field identity! : ∀ {x} → map (ε[ B₂ ] {x = x}) ≋ ε[ B₂ ] {x = μ x}
  open Identity! ⦃ … ⦄ public

{-
test-identity! : ∀
  {a₂} {A₂ : Ø a₂} {b₂} {B₂ : A₂ → A₂ → Ø b₂} {c₂} ⦃ _ : MorphismEquivalence B₂ c₂ ⦄
  {μ : A₂ → A₂}
  ⦃ _ : Reflexivity B₂ ⦄
  ⦃ m : Map B₂ (B₂ on μ) ⦄
  ⦃ _ : Identity! B₂ c₂ μ ⦄
  ⦃ _ : Map B₂ (B₂ on ¡) ⦄
  ⦃ _ : Identity! B₂ c₂ ¡ ⦄
  → ∀ {x} ⦃ _ : Map B₂ (λ _ _ → B₂ (μ x) (μ x)) ⦄ ⦃ _ : Identity! B₂ c₂ (λ v → μ x) ⦄
  → map ⦃ m ⦄ (ε[ B₂ ] {x = x}) ≋ ε[ B₂ ] {x = μ x}
test-identity! {B₂ = B₂} ⦃ me ⦄ {μ = μ} ⦃ r ⦄ ⦃ m1 ⦄ ⦃ i1 ⦄ ⦃ m2 ⦄ ⦃ i2 ⦄ {x = x} ⦃ m! ⦄ ⦃ i! ⦄ = identity! {B₂ = B₂} ⦃ me ⦄ {λ v → μ x} ⦃ r ⦄ ⦃ {!it!} ⦄ ⦃ {!!} ⦄ {_}
-}

{-
module _
  {a₂} {A₂ : Ø a₂} {b₂} {B₂ : A₂ → A₂ → Ø b₂} {c₂}
  ⦃ me : MorphismEquivalence B₂ c₂ ⦄
  {μ : A₂ → A₂}
  ⦃ r : Reflexivity B₂ ⦄
  where
  postulate mapper : ∀ {x y} → B₂ x y → B₂ (μ x) (μ y)
  instance m : Map B₂ (B₂ on μ)
  Map.map m x = {!mapper x!}
  instance i : Identity! B₂ c₂ μ
  Identity!.identity! i = {!!}
  module _ {x} where
    postulate mapper! : ∀ {x' y'} → B₂ x' y' → B₂ (μ x) (μ x)
    instance m! : Map B₂ (λ _ _ → B₂ (μ x) (μ x))
    Map.map m! x₂ = {!!} -- mapper! x₂
    instance i! : Identity! B₂ c₂ (λ v → μ x)
    Identity!.identity! i! = {!!}
    foo : map ⦃ m ⦄ (ε[ B₂ ] {x = x}) ≋ ε[ B₂ ] {x = μ x}
    foo = identity! {B₂ = B₂} ⦃ me ⦄ {λ v → μ x} ⦃ r ⦄ ⦃ m! ⦄ ⦃ i! ⦄ {x}
-}

{-
module M where
  postulate
    magic : ∀ {A : Set} → A
  data A₂ : Set where
    DA1 : A₂
  data B₂ : A₂ → A₂ → Set where
    DB1 : B₂ DA1 DA1
  module _ {c₂}
    ⦃ me : MorphismEquivalence B₂ c₂ ⦄
    where
    μ : A₂ → A₂
    μ DA1 = DA1
    module _
      where
      instance r : Reflexivity B₂
      Reflexivity.reflexivity r {DA1} = DB1
      mapper : ∀ {x y} → B₂ x y → B₂ (μ x) (μ y)
      mapper = magic
      instance m : Map B₂ (B₂ on μ)
      Map.map m x = mapper x
      instance i : Identity! B₂ c₂ μ
      Identity!.identity! i = {!!}
      module _ {x} where
        mapper! : ∀ {x' y'} → B₂ x' y' → B₂ (μ x) (μ x)
        mapper! = magic
        instance m! : Map B₂ (λ _ _ → B₂ (μ x) (μ x))
        Map.map m! x₂ = mapper! x₂
        instance i! : Identity! B₂ c₂ (λ v → μ x)
        Identity!.identity! i! = {!!}
        foo : map ⦃ m ⦄ (ε[ B₂ ] {x = x}) ≋ ε[ B₂ ] {x = μ x}
        foo = identity! ⦃ me ⦄ ⦃ it ⦄ ⦃ m! ⦄
        -- identity! {B₂ = B₂} ⦃ me ⦄ {λ v → μ x} ⦃ r ⦄ ⦃ m! ⦄ ⦃ i! ⦄ {x}
        -- identity! {B₂ = B₂} ⦃ me ⦄ {μ} ⦃ r ⦄ ⦃ m ⦄ ⦃ i ⦄ {x}
        -- identity! {B₂ = B₂} ⦃ me ⦄ {λ v → μ x} ⦃ r ⦄ ⦃ m! ⦄ ⦃ i! ⦄ {x}
-}

module _
  {a} {A : Set a}
  {b} (B : A → A → Set b)
  {c} (C : ∀ {x y} → B x y → ∀ {z} → B y z → Set c)
  where
  𝓬ommutativity′ = ∀ {x y} (f : B x y) {z} (g : B y z) → C f g
  record Commutativity′ : Ø a ∙̂ b ∙̂ c where field commutativity : 𝓬ommutativity′

open Commutativity′ ⦃ … ⦄ public

record Compositionality {a} {A : Set a} {b} (B : A → A → Set b) : Ø a ∙̂ b where
  infixr 9 _∙_
  field _∙_ : ∀ {y z x} → B y z → B x y → B x z

open Compositionality ⦃ … ⦄ public

instance CompositionalityFromTransitivity : ∀ {a} {A : Set a} {b} {B : A → A → Set b} ⦃ _ : Transitivity B ⦄ → Compositionality B
Compositionality._∙_ CompositionalityFromTransitivity g f = transitivity f g

instance CompositionalityFromCommutativity′ : ∀ {a} {A : Set a} {b} {B : A → A → Set b} ⦃ _ : Commutativity′ B (λ {x y} f {z} g → B x z) ⦄ → Compositionality B
Compositionality._∙_ CompositionalityFromCommutativity′ g f = commutativity f g

{-
infixr 9 _∙_
_∙_ : ∀ {a} {A : Set a}
        {b} {B : A → A → Set b}
      ⦃ _ : Transitivity B ⦄
      → ∀ {y z x} → B y z → B x y → B x z
g ∙ f = transitivity f g
-}
module _
  {a₁} {A₁ : Ø a₁} {b₁} (B₁ : A₁ → A₁ → Ø b₁)
  {a₂} {A₂ : Ø a₂} {b₂} (B₂ : A₂ → A₂ → Ø b₂)
  c₂ ⦃ _ : MorphismEquivalence B₂ c₂ ⦄
  (μ : A₁ → A₂)
  ⦃ _ : Transitivity B₁ ⦄
  ⦃ _ : Transitivity B₂ ⦄
  ⦃ _ : Map B₁ (B₂ on μ) ⦄
  where
  𝓬ommutativity = 𝓬ommutativity′ B₁ (λ f g → map[ B₂ on μ ] (g ∙ f) ≋ (map g ∙ map f))
  Commutativity = Commutativity′ B₁ (λ f g → map[ B₂ on μ ] (g ∙ f) ≋ (map g ∙ map f))

record LeftIdentity
  {a} {A : Ø a} {b}
    (B : A → A → Ø b)
    c
    ⦃ _ : MorphismEquivalence B c ⦄
    ⦃ _ : Reflexivity B ⦄
    ⦃ _ : Transitivity B ⦄
  : Ø a ∙̂ b ∙̂ c where
  field left-identity : ∀ {x y} (f : B x y) → ε ∙ f ≋ f

open LeftIdentity ⦃ … ⦄

record RightIdentity
  {a} {A : Ø a} {b}
    (B : A → A → Ø b)
    c
    ⦃ _ : MorphismEquivalence B c ⦄
    ⦃ _ : Reflexivity B ⦄
    ⦃ _ : Transitivity B ⦄
  : Ø a ∙̂ b ∙̂ c where
  field right-identity : ∀ {x y} (f : B x y) → f ∙ ε ≋ f
open RightIdentity ⦃ … ⦄ public

record Associativity
  {a} {A : Ø a} {b}
    (B : A → A → Ø b)
    c
    ⦃ _ : MorphismEquivalence B c ⦄
    ⦃ _ : Transitivity B ⦄
  : Ø a ∙̂ b ∙̂ c where
  field associativity : ∀ {w x y z} (f : B w x) (g : B x y) (h : B y z) → (h ∙ g) ∙ f ≋ h ∙ g ∙ f
open Associativity ⦃ … ⦄ public

module _
  {a} {A : Set a}
  {b} (B : A → A → Set b)
  {c} (C : ∀ {x y} → B x y → B x y → Set c)
  {d} (D : ∀ {x y} → B x y → B x y → Set d)
  where

  𝓮xtensionality₁′ : Ø a ∙̂ b ∙̂ c ∙̂ d
  𝓮xtensionality₁′ = ∀ {x y} {f₁ f₂ : B x y} → C f₁ f₂ → D f₁ f₂

  record Extensionality₁′ : Ø a ∙̂ b ∙̂ c ∙̂ d where field extensionality₁ : 𝓮xtensionality₁′

open Extensionality₁′ ⦃ … ⦄ public

module _
  {a₁} {A₁ : Ø a₁} {b₁} (B₁ : A₁ → A₁ → Ø b₁) c₁ ⦃ _ : MorphismEquivalence B₁ c₁ ⦄
  {a₂} {A₂ : Ø a₂} {b₂} (B₂ : A₂ → A₂ → Ø b₂) c₂ ⦃ _ : MorphismEquivalence B₂ c₂ ⦄
  (μ : A₁ → A₂)
  ⦃ _ : Map B₁ (B₂ on μ) ⦄
  where
  Extensionality₁ = Extensionality₁′ B₁ _≋_ (λ f₁ f₂ → map[ B₂ on μ ] f₁ ≋ map f₂)
  𝓮xtensionality₁ = 𝓮xtensionality₁′ B₁ _≋_ (λ f₁ f₂ → map[ B₂ on μ ] f₁ ≋ map f₂)

module _
  {a} {A : Set a}
  {b} (B : A → A → Set b)
  {c} (C : ∀ {x y} → B x y → B x y → Set c)
  {d} (D : ∀ {x y} → B x y → B x y → ∀ {z} → B y z → B y z → Set d)
  where

  𝓮xtensionality₂′ = ∀ {x y} {f₁ f₂ : B x y} {z} {g₁ g₂ : B y z} → C f₁ f₂ → C g₁ g₂ → D f₁ f₂ g₁ g₂
  record Extensionality₂′ : Ø a ∙̂ b ∙̂ c ∙̂ d where field extensionality₂ : 𝓮xtensionality₂′

open Extensionality₂′ ⦃ … ⦄ public

module _
  {a} {A : Ø a} {b} (B : A → A → Ø b) c ⦃ _ : MorphismEquivalence B c ⦄
  ⦃ _ : Transitivity B ⦄
  where
  𝓮xtensionality₂ = 𝓮xtensionality₂′ B equivalence (λ f₁ f₂ g₁ g₂ → g₁ ∙ f₁ ≋ g₂ ∙ f₂)
  Extensionality₂ = Extensionality₂′ B equivalence (λ f₁ f₂ g₁ g₂ → g₁ ∙ f₁ ≋ g₂ ∙ f₂)

record IsSemigroupoid {a} {A : Ø a} {b} (B : A → A → Ø b) c ⦃ _ : MorphismEquivalence B c ⦄ : Ø a ∙̂ b ∙̂ c where
  field
    ⦃ ⌶Transitivity ⦄ : Transitivity B
    ⦃ ⌶Extensionality₂ ⦄ : Extensionality₂ B c
    ⦃ ⌶Associativity ⦄ : Associativity B c

record IsCategory
  {a} {A : Ø a} {b}
    (B : A → A → Ø b)
    c
    ⦃ _ : MorphismEquivalence B c ⦄
  : Ø a ∙̂ b ∙̂ c where
  field
    ⦃ ⌶IsSemigroupoid ⦄ : IsSemigroupoid B c
    ⦃ ⌶Reflexivity ⦄ : Reflexivity B
    ⦃ ⌶LeftIdentity ⦄ : LeftIdentity B c
    ⦃ ⌶RightIdentity ⦄ : RightIdentity B c

record IsSemifunctor
  {a₁} {A₁ : Ø a₁} {b₁} (B₁ : A₁ → A₁ → Ø b₁) c₁ ⦃ _ : MorphismEquivalence B₁ c₁ ⦄
  {a₂} {A₂ : Ø a₂} {b₂} (B₂ : A₂ → A₂ → Ø b₂) c₂ ⦃ _ : MorphismEquivalence B₂ c₂ ⦄
  (μ : A₁ → A₂)
  : Ø a₁ ∙̂ b₁ ∙̂ c₁ ∙̂ a₂ ∙̂ b₂ ∙̂ c₂
  where
  field
    ⦃ ⌶IsSemigroupoid₁ ⦄ : IsSemigroupoid B₁ c₁
    ⦃ ⌶IsSemigroupoid₂ ⦄ : IsSemigroupoid B₂ c₂
    ⦃ ⌶Map ⦄ : Map B₁ (B₂ on μ)
    ⦃ ⌶Extensionality₁ ⦄ : Extensionality₁ B₁ c₁ B₂ c₂ μ
    ⦃ ⌶Commutativity ⦄ : Commutativity B₁ B₂ c₂ μ

record IsFunctor
  {a₁} {A₁ : Ø a₁} {b₁} (B₁ : A₁ → A₁ → Ø b₁) c₁ ⦃ _ : MorphismEquivalence B₁ c₁ ⦄
  {a₂} {A₂ : Ø a₂} {b₂} (B₂ : A₂ → A₂ → Ø b₂) c₂ ⦃ _ : MorphismEquivalence B₂ c₂ ⦄
  (μ : A₁ → A₂)
  : Ø a₁ ∙̂ b₁ ∙̂ c₁ ∙̂ a₂ ∙̂ b₂ ∙̂ c₂
  where
  field
    ⦃ ⌶IsCategory₁ ⦄ : IsCategory B₁ c₁
    ⦃ ⌶IsCategory₂ ⦄ : IsCategory B₂ c₂
    ⦃ ⌶IsSemifunctor ⦄ : IsSemifunctor B₁ c₁ B₂ c₂ μ
    ⦃ ⌶Identity ⦄ : Identity B₁ B₂ c₂ μ

record Setoid a b : Ø ↑̂ (a ∙̂ b) where
  field
    Object : Ø a
    Eq : Object → Object → Ø b
    ⦃ ⌶IsSetoid ⦄ : IsSetoid Eq

record Semigroupoid a b c : Ø ↑̂ (a ∙̂ b ∙̂ c) where
  field
    Object : Ø a
    Morphism : Object → Object → Ø b
    ⦃ ⌶MorophismEquivalence ⦄ : MorphismEquivalence Morphism c
    ⦃ ⌶IsSemigroupoid ⦄ : IsSemigroupoid Morphism c

record Category a b c : Ø ↑̂ (a ∙̂ b ∙̂ c) where
  field
    Object : Ø a
    Morphism : Object → Object → Ø b
    ⦃ ⌶MorophismEquivalence ⦄ : MorphismEquivalence Morphism c
    ⦃ ⌶IsCategory ⦄ : IsCategory Morphism c

record Semifunctor a b c d e f : Ø ↑̂ (a ∙̂ b ∙̂ c ∙̂ d ∙̂ e ∙̂ f) where
  field
    Object₁ : Ø a
    Morphism₁ : Object₁ → Object₁ → Ø b
    ⦃ ⌶MorophismEquivalence₁ ⦄ : MorphismEquivalence Morphism₁ c
    Object₂ : Ø d
    Morphism₂ : Object₂ → Object₂ → Ø e
    ⦃ ⌶MorophismEquivalence₂ ⦄ : MorphismEquivalence Morphism₂ f
    μ : Object₁ → Object₂
    ⦃ ⌶IsSemifunctor ⦄ : IsSemifunctor Morphism₁ c Morphism₂ f μ

record Functor a b c d e f : Ø ↑̂ (a ∙̂ b ∙̂ c ∙̂ d ∙̂ e ∙̂ f) where
  field
    Object₁ : Ø a
    Morphism₁ : Object₁ → Object₁ → Ø b
    ⦃ ⌶MorophismEquivalence₁ ⦄ : MorphismEquivalence Morphism₁ c
    Object₂ : Ø d
    Morphism₂ : Object₂ → Object₂ → Ø e
    ⦃ ⌶MorophismEquivalence₂ ⦄ : MorphismEquivalence Morphism₂ f
    μ : Object₁ → Object₂
    ⦃ ⌶IsFunctor ⦄ : IsFunctor Morphism₁ c Morphism₂ f μ

module _ where

  record Successor₀ {x} (X : Ø x) : Ø x where
    field
      ⇑₀ : X → X
  open Successor₀ ⦃ … ⦄ public

  record Principal₁ {x} {X : Ø x} {a} (A : X → Ø a) : Ø₀ where no-eta-equality
  record Principal₁₊₁ {x} {X : Ø x} {a} (A : X → Ø a) {b} (B : X → Ø b) : Ø₀ where no-eta-equality

  record Successor₁ {x} {X : Ø x} {a} (A : X → Ø a)
    ⦃ _ : Successor₀ X ⦄
    ⦃ _ : Principal₁ A ⦄
    : Ø x ∙̂ a where
    field
      ⇑₁ : ∀ {m} → A m → A (⇑₀ m)
  open Successor₁ ⦃ … ⦄ public

  record Thin {x} {X : Ø x} {a} (A : X → Ø a) {b} (B : X → Ø b)
    ⦃ _ : Successor₀ X ⦄
    ⦃ _ : Principal₁ A ⦄
    ⦃ _ : Principal₁ B ⦄
    : Ø x ∙̂ a ∙̂ b where
    field
      thin : ∀ {m : X} → A (⇑₀ m) → B m → B (⇑₀ m)
  open Thin ⦃ … ⦄ public

  thin[_] : ∀
    {x} {X : Ø x} {a} {A : X → Ø a} {b} (B : X → Ø b)
    ⦃ _ : Successor₀ X ⦄
    ⦃ _ : Principal₁ A ⦄
    ⦃ _ : Principal₁ B ⦄
    ⦃ _ : Thin A B ⦄
    → ∀ {m : X} → A (⇑₀ m) → B m → B (⇑₀ m)
  thin[ _ ] = thin

  record Injectivity₀
    {a} {A : Ø a}
    {b} {B : Ø b}
    (f : A → B)
    ℓa
    ℓb
    ⦃ _ : Equivalence B ℓb ⦄
    ⦃ _ : Equivalence A ℓa ⦄
    : Ø a ∙̂ b ∙̂ ℓa ∙̂ ℓb where
    field injectivity₀ : ∀ {x y} → f x ≋ f y → x ≋ y
  open Injectivity₀ ⦃ … ⦄ public

  injectivity₀[_] : ∀
    {a} {A : Ø a}
    {b} {B : Ø b}
    (f : A → B)
    {ℓa}
    {ℓb}
    ⦃ _ : Equivalence A ℓa ⦄
    ⦃ _ : Equivalence B ℓb ⦄
    ⦃ _ : Injectivity₀ f ℓa ℓb ⦄
    → ∀ {x y} → f x ≋ f y → x ≋ y
  injectivity₀[ f ] = injectivity₀ { f = f }

  record Injectivity!
    {a} {A : Ø a}
    {b} {B : A → Ø b}
    {c} (C : ∀ x → B x → B x → Ø c)
    {d} (D : ∀ x → B x → B x → Ø d)
    : Ø a ∙̂ b ∙̂ c ∙̂ d where
    field injectivity! : ∀ w {x y : B w} → C w x y → D w x y
  open Injectivity! ⦃ … ⦄ public

  module _
    {a} {A : Ø a}
    {b} {B : A → Ø b}
    {c} {C : A → Ø c}
    (f : (x : A) → B x → C x)
    ℓb
    ℓc
    ⦃ _ : ∀ {x} → Equivalence (B x) ℓb ⦄
    ⦃ _ : ∀ {x} → Equivalence (C x) ℓc ⦄
    where
    Injectivity? = Injectivity! (λ w x y → f w x ≋ f w y) (λ w x y → x ≋ y)

  injectivity?[_] : ∀
    {a} {A : Ø a}
    {b} {B : A → Ø b}
    {c} {C : A → Ø c}
    (f : (x : A) → B x → C x)
    {ℓb}
    {ℓc}
    ⦃ _ : ∀ {x} → Equivalence (B x) ℓb ⦄
    ⦃ _ : ∀ {x} → Equivalence (C x) ℓc ⦄
    ⦃ _ : Injectivity? f ℓb ℓc ⦄
    → ∀ w {x y} → f w x ≋ f w y → x ≋ y
  injectivity?[ _ ] = injectivity!

  record Injectivity₁
    {a} {A : Ø a}
    {b} {B : A → Ø b}
    {c} {C : A → Ø c}
    (f : (x : A) → B x → C x)
    ℓb
    ℓc
    ⦃ _ : ∀ {x} → Equivalence (B x) ℓb ⦄
    ⦃ _ : ∀ {x} → Equivalence (C x) ℓc ⦄
    : Ø a ∙̂ b ∙̂ ℓb ∙̂ ℓc where
    field injectivity₁ : ∀ w {x y} → f w x ≋ f w y → x ≋ y
  open Injectivity₁ ⦃ … ⦄ public

  injectivity₁[_] : ∀
    {a} {A : Ø a}
    {b} {B : A → Ø b}
    {c} {C : A → Ø c}
    (f : (x : A) → B x → C x)
    {ℓb}
    {ℓc}
    ⦃ _ : ∀ {x} → Equivalence (B x) ℓb ⦄
    ⦃ _ : ∀ {x} → Equivalence (C x) ℓc ⦄
    ⦃ _ : Injectivity₁ f ℓb ℓc ⦄
    → ∀ w {x y} → f w x ≋ f w y → x ≋ y
  injectivity₁[ f ] = injectivity₁ {f = f}

  record Injectivity₂
    {a} {A : Ø a}
    {b} {B : Ø b}
    {c} {C : Ø c}
    (f : A → B → C)
    ℓb
    ℓc
    ⦃ _ : Equivalence B ℓb ⦄
    ⦃ _ : Equivalence C ℓc ⦄
    : Ø a ∙̂ b ∙̂ ℓb ∙̂ ℓc where
    field injectivity₂ : ∀ w {x y} → f w x ≋ f w y → x ≋ y
  open Injectivity₂ ⦃ … ⦄ public

  injectivity₂[_] : ∀
    {a} {A : Ø a}
    {b} {B : Ø b}
    {c} {C : Ø c}
    (f : A → B → C)
    {ℓb}
    {ℓc}
    ⦃ _ : Equivalence B ℓb ⦄
    ⦃ _ : Equivalence C ℓc ⦄
    ⦃ _ : Injectivity₂ f ℓb ℓc ⦄
    → ∀ w {x y} → f w x ≋ f w y → x ≋ y
  injectivity₂[ f ] = injectivity₂ {f = f}

  record ThinInjective {x} {X : Ø x} {a} (A : X → Ø a) {b} (B : X → Ø b) c
    ⦃ _ : Successor₀ X ⦄
    ⦃ _ : ∀ {x} → Equivalence (B x) c ⦄
    ⦃ _ : Principal₁ A ⦄
    ⦃ _ : Principal₁ B ⦄
    ⦃ _ : Thin A B ⦄
    : Ø x ∙̂ a ∙̂ b ∙̂ ↑̂ c where
    field
      ⦃ ⌶Injectivity₁ ⦄ : ∀ {m : X} → Injectivity₁ {A = A (⇑₀ m)} {B = λ _ → B _} (λ w x → thin w x) c c
      ⦃ ⌶Injectivity₂ ⦄ : ∀ {m : X} → Injectivity₂ (λ (w : A (⇑₀ m)) x → thin[ B ] w x) c c
      -- (thin[ B ] {m = m})
    thin-injective : ∀ {m : X} (x : A (⇑₀ m)) {y₁ y₂ : B m} → thin x y₁ ≋ thin x y₂ → y₁ ≋ y₂
    thin-injective = injectivity₁[ thin ]
    -- injectivity₂[ thin[ B ] ]
    -- injectivity₁[ thin ]
  open ThinInjective ⦃ … ⦄ public

  record Thick {x} {X : Ø x} {a} (A : X → Ø a) {b} (B : X → Ø b)
    ⦃ _ : Successor₀ X ⦄
    ⦃ _ : Principal₁ B ⦄
    : Ø x ∙̂ a ∙̂ b where
    field
      thick : ∀ {m} → B (⇑₀ m) → A m → B m
  open Thick ⦃ … ⦄ public

  record ThickThinId {x} {X : Ø x} {a} (A : X → Ø a) {b} (B : X → Ø b) c
    ⦃ _ : Successor₀ X ⦄
    ⦃ _ : Principal₁ A ⦄
    ⦃ _ : Principal₁ B ⦄
    ⦃ _ : Successor₁ A ⦄
    ⦃ _ : ∀ {x} → Equivalence (B x) c ⦄
    ⦃ _ : Thin A B ⦄
    ⦃ _ : Thick A B ⦄
    : Ø x ∙̂ a ∙̂ b ∙̂ ↑̂ c where
    field
      thick∘thin=id : ∀ {m} (x : A m) (y : B m) → thick (thin (⇑₁ x) y) x ≋ y
  open ThickThinId ⦃ … ⦄ public

  record Maybe* a : Ø ↑̂ a where
    field
      Maybe : Ø a → Ø a
      just : ∀ {A} → A → Maybe A
      nothing : ∀ {A} → Maybe A
  open Maybe* ⦃ … ⦄ -- public

  record Check {x} {X : Ø x} {a} (A : X → Ø a) {b} (B : X → Ø b)
    ⦃ _ : Successor₀ X ⦄
    ⦃ _ : Principal₁ A ⦄
    ⦃ _ : Principal₁ B ⦄
    ⦃ _ : Maybe* b ⦄
    : Ø x ∙̂ a ∙̂ ↑̂ b where
    field
      check : ∀ {m} → A (⇑₀ m) → B (⇑₀ m) → Maybe (B m)
  open Check ⦃ … ⦄ public

  record ThinCheckId {x} {X : Ø x} {a} (A : X → Ø a) {b} (B : X → Ø b) ℓb ℓc
    ⦃ _ : Successor₀ X ⦄
    ⦃ _ : Maybe* b ⦄
    ⦃ _ : ∀ {x} → Equivalence (B x) ℓb ⦄
    ⦃ _ : ∀ {x} → Equivalence (Maybe (B x)) ℓc ⦄
    ⦃ _ : Principal₁ A ⦄
    ⦃ _ : Principal₁ B ⦄
    ⦃ _ : Thin A B ⦄
    ⦃ _ : Check A B ⦄
    : Ø x ∙̂ a ∙̂ b ∙̂ ℓb ∙̂ ℓc where
    field
      thin-check-id : ∀ {m} (x : A (⇑₀ m)) y → ∀ (y' : B m) → thin x y' ≋ y → check x y ≋ just y'
  open ThinCheckId ⦃ … ⦄ public

  test-thin-check-id : ∀ {x} {X : Ø x} {a} (A : X → Ø a) {b} (B : X → Ø b) ℓb ℓc
                         ⦃ _ : Successor₀ X ⦄
                         ⦃ _ : ∀ {x} → Equivalence (B x) ℓb ⦄
                         ⦃ _ : Maybe* b ⦄
                         ⦃ _ : ∀ {x} → Equivalence (Maybe (B x)) ℓc ⦄
                         ⦃ _ : Principal₁ A ⦄
                         ⦃ _ : Principal₁ B ⦄
                         ⦃ _ : Thin A B ⦄
                         ⦃ _ : Check A B ⦄
                         ⦃ _ : ThinCheckId A B ℓb ℓc ⦄
                         → ∀ {m} (x : A (⇑₀ m)) y → ∀ (y' : B m) → thin x y' ≋ y → check x y ≋ just y'
  test-thin-check-id A B ℓb ℓc = thin-check-id

  record ThickAndThin {x} {X : Ø x} {a} (A : X → Ø a) {b} (B : X → Ø b) c ℓc
    ⦃ _ : Successor₀ X ⦄
    ⦃ _ : Principal₁ A ⦄
    ⦃ _ : Principal₁ B ⦄
    ⦃ _ : Successor₁ A ⦄
    ⦃ _ : Maybe* b ⦄
    ⦃ _ : ∀ {x} → Equivalence (B x) c ⦄
    ⦃ _ : ∀ {x} → Equivalence (Maybe (B x)) ℓc ⦄
    : Ø x ∙̂ a ∙̂ ↑̂ b ∙̂ ↑̂ c ∙̂ ↑̂ ℓc where
    field
      ⦃ iThin ⦄ : Thin A B
      ⦃ iThinInjective ⦄ : ThinInjective A B c
      ⦃ iThick ⦄ : Thick A B
      ⦃ iThickThinId ⦄ : ThickThinId A B c
      ⦃ iCheck ⦄ : Check A B
      ⦃ iThinCheckId ⦄ : ThinCheckId A B c ℓc
  open ThickAndThin ⦃ … ⦄

module _ where

  record FMap {x} {y} (F : Ø x → Ø y) : Ø (↑̂ x) ∙̂ y where
    field fmap : ∀ {A B : Ø x} → (A → B) → F A → F B
