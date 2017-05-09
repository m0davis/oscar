-- {-# OPTIONS --show-implicit #-}
module Oscar.Class where

open import Oscar.Prelude

module _
  {a} {A : Ø a}
  {b} (B : A → A → Ø b)
  where
  𝓻eflexivity = ∀ {x} → B x x
  record Reflexivity : Ø a ∙̂ b where field reflexivity : 𝓻eflexivity
  open Reflexivity ⦃ … ⦄ public

ε : ∀ {a} {A : Ø a}
      {b} {B : A → A → Ø b}
    ⦃ _ : Reflexivity B ⦄
    → ∀ {x} → B x x
ε = reflexivity

ε[_] : ∀ {a} {A : Ø a}
         {b} (B : A → A → Ø b)
       ⦃ _ : Reflexivity B ⦄
       → ∀ {x} → B x x
ε[ _ ] = reflexivity

module _
  {a} {A : Ø a}
  {b} (B : A → A → Ø b)
  {c} (C : ∀ {x y} → B x y → Ø c)
  where
  𝓻elationality = ∀ {x y} → (f : B x y) → C f
  record Relationality : Ø a ∙̂ b ∙̂ c where field relationality : 𝓻elationality
  open Relationality ⦃ … ⦄ public
{-
𝓶ap : ∀
  {a} {A : Ø a}
  {b} (B : A → A → Ø b)
  {c} (C : A → A → Ø c)
  → Ø a ∙̂ b ∙̂ c
𝓶ap B C = ∀ {x y} → B x y → C x y
-}

module _
  {a} {A : Ø a}
  {b} (B : A → A → Ø b)
  {c} (C : A → A → Ø c)
  where
  𝓶ap = 𝓻elationality B (λ {x y} _ → C x y)
  Map = Relationality B (λ {x y} _ → C x y)

map : ∀
  {a} {A : Ø a}
  {b} {B : A → A → Ø b}
  {c} {C : A → A → Ø c}
  ⦃ _ : Map B C ⦄
  → 𝓶ap B C
map = relationality

{-
record Map
  {a} {A : Ø a}
  {b} (B : A → A → Ø b)
  {c} (C : A → A → Ø c)
  : Ø a ∙̂ b ∙̂ c where
  field map : 𝓶ap B C

open Map ⦃ … ⦄ public
-}

map[_] : ∀
  {a} {A : Ø a}
  {b} {B : A → A → Ø b}
  {c} (C : A → A → Ø c)
  ⦃ _ : Map B C ⦄
  → ∀ {x y} → B x y → C x y
map[ C ] f = map f

module _
  {a} {A : Ø a}
  {b} (B : A → A → Ø b)
  where
  𝓼ymmetry = 𝓻elationality B (λ {x y} _ → B y x)
  Symmetry = Relationality B (λ {x y} _ → B y x)

symmetry : ∀
  {a} {A : Ø a}
  {b} {B : A → A → Ø b}
  ⦃ _ : Symmetry B ⦄
  → 𝓼ymmetry B
symmetry = relationality
{-
  𝓼ymmetry = ∀ {x y} → B x y → B y x
  record Symmetry : Ø a ∙̂ b where field symmetry : 𝓼ymmetry
  open Symmetry ⦃ … ⦄ public
-}

module _
  {a} {A : Ø a}
  {b} (B : A → A → Ø b)
  {c} (C : ∀ {x y z} → B x y → B y z → Ø c)
  where
  𝓬ontiguity = ∀ {x y z} (f : B x y) (g : B y z) → C f g
  record Contiguity : Ø a ∙̂ b ∙̂ c where field contiguity : 𝓬ontiguity
  open Contiguity ⦃ … ⦄ public

module _
  {a} {A : Ø a}
  {b} (B : A → A → Ø b)
  where
  𝓽ransitivity = 𝓬ontiguity B λ {x y z} f g → B x z
  Transitivity = Contiguity B λ {x y z} f g → B x z

transitivity : ∀
  {a} {A : Ø a}
  {b} {B : A → A → Ø b}
  ⦃ _ : Transitivity B ⦄
  → 𝓽ransitivity B
transitivity = contiguity

infixr 9 _∙_
_∙_ : ∀ {a} {A : Ø a}
        {b} {B : A → A → Ø b}
      ⦃ _ : Transitivity B ⦄
      → ∀ {y z x} → B y z → B x y → B x z
g ∙ f = contiguity f g

record IsSetoid
  {a} {A : Ø a}
  {b} (B : A → A → Ø b) : Ø a ∙̂ b where
  field
    instance ⦃ ⌶Reflexivity ⦄ : Reflexivity B
    instance ⦃ ⌶Symmetry ⦄ : Symmetry B
    instance ⦃ ⌶Transitivity ⦄ : Transitivity B

record Equivalence
  {a}
    (A : Ø a)
    b
  : Ø a ∙̂ ↑̂ b where
  field
    equivalence : A → A → Ø b
    ⦃ ⌶IsSetoid ⦄ : IsSetoid equivalence

open Equivalence ⦃ … ⦄ public

infix 4 _≋_
_≋_ : ∀ {a} {A : Ø a} {b} ⦃ _ : Equivalence A b ⦄ → A → A → Ø b
_≋_ = equivalence

record IndexedEquivalence
  {a} {A : Ø a} {b}
    (B : A → Ø b)
    c
  : Ø a ∙̂ b ∙̂ ↑̂ c where
  field
    indexedEquivalence : ∀ {x} → B x → B x → Ø c
    ⦃ ⌶IsSetoid ⦄ : ∀ {x} → IsSetoid (indexedEquivalence {x})
  instance ⌶Equivalence : ∀ {x} → Equivalence (B x) c
  Equivalence.equivalence ⌶Equivalence = indexedEquivalence

module _
  {a} {A : Ø a} {b}
    (B : A → A → Ø b)
    c
  where
  𝓶orphismEquivalence = ∀ {x y} → B x y → B x y → Ø c

  record MorphismEquivalence : Ø a ∙̂ b ∙̂ ↑̂ c where
    field
      morphismEquivalence : 𝓶orphismEquivalence
      ⦃ ⌶IsSetoid ⦄ : ∀ {x y} → IsSetoid (morphismEquivalence {x} {y})
    instance ⌶Equivalence : ∀ {x y} → Equivalence (B x y) c
    Equivalence.equivalence ⌶Equivalence = morphismEquivalence

open MorphismEquivalence ⦃ … ⦄ public

record Congruity
  a b {c} (C : ∀ {x} {X : Ø x} → X → X → Ø c)
  : Ø ↑̂ (a ∙̂ b ∙̂ c) where
  field congruity : ∀ {A : Ø a} {B : Ø b} {x y} (f : A → B) → C x y → C (f x) (f y)

open Congruity ⦃ … ⦄ public

record Congruity₂
  a b c {ℓ} (EQ : ∀ {x} {X : Ø x} → X → X → Ø ℓ)
  : Ø ↑̂ (a ∙̂ b ∙̂ c) ∙̂ ℓ where
  field congruity₂ : ∀ {A : Ø a} {B : Ø b} {C : Ø c} {x y} {x' y'} (f : A → B → C) → EQ x y → EQ x' y' → EQ (f x x') (f y y')

open Congruity₂ ⦃ … ⦄ public

record Ċongruity
  𝔬 𝔭 {c}
  (C : ∀ {𝔒 : Ø 𝔬} {𝔓 : 𝔒 → Ø 𝔭} → ((𝓞 : 𝔒) → 𝔓 𝓞) → ((𝓞 : 𝔒) → 𝔓 𝓞) → Ø c)
  : Ø ↑̂ (𝔬 ∙̂ 𝔭) ∙̂ c where
  field ċongruity : ∀ {𝔒 : Ø 𝔬} {𝔓 : 𝔒 → Ø 𝔭} {f g : (𝓞 : 𝔒) → 𝔓 𝓞} (F : ∀ {𝓞 : 𝔒} → 𝔓 𝓞 → 𝔓 𝓞) → C f g → C (F ∘ f) (F ∘ g)

open Ċongruity ⦃ … ⦄ public

module _
  {a₁} {A₁ : Ø a₁} {b₁} (B₁ : A₁ → A₁ → Ø b₁)
  {a₂} {A₂ : Ø a₂} {b₂} (B₂ : A₂ → A₂ → Ø b₂)
  c₂ ⦃ _ : MorphismEquivalence B₂ c₂ ⦄
  (μ : A₁ → A₂)
  ⦃ _ : Transitivity B₁ ⦄
  ⦃ _ : Transitivity B₂ ⦄
  ⦃ _ : Map B₁ (B₂ on μ) ⦄
  where
  𝓒ommutativity : ∀ {x y z} → B₁ x y → B₁ y z → Ø c₂
  𝓒ommutativity = λ f g → map[ B₂ on μ ] (g ∙ f) ≋ map g ∙ map f
  𝓬ommutativity = 𝓬ontiguity B₁ 𝓒ommutativity
  Commutativity = Contiguity B₁ 𝓒ommutativity

commutativity : ∀
  {a} {A : Ø a}
  {b} {B : A → A → Ø b}
  {c} {C : ∀ {x y z} → B x y → B y z → Ø c}
  ⦃ _ : Contiguity B C ⦄
  → 𝓬ontiguity B C
commutativity = contiguity

commutativity[_] : ∀
  {a₁} {A₁ : Ø a₁} {b₁} {B₁ : A₁ → A₁ → Ø b₁}
  {a₂} {A₂ : Ø a₂} {b₂} (B₂ : A₂ → A₂ → Ø b₂)
  {c₂} ⦃ _ : MorphismEquivalence B₂ c₂ ⦄
  {μ : A₁ → A₂}
  ⦃ _ : Transitivity B₁ ⦄
  ⦃ _ : Transitivity B₂ ⦄
  ⦃ _ : Map B₁ (B₂ on μ) ⦄
  ⦃ _ : Commutativity B₁ B₂ c₂ μ ⦄
  → 𝓬ommutativity B₁ B₂ c₂ μ
commutativity[ _ ] = contiguity

module _
  {a} {A : Ø a}
  {b} (B : A → Ø b)
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

record LeftIdentity
  {a} {A : Ø a} {b}
    (B : A → A → Ø b)
    c
    ⦃ _ : MorphismEquivalence B c ⦄
    ⦃ _ : Reflexivity B ⦄
    ⦃ _ : Transitivity B ⦄
  : Ø a ∙̂ b ∙̂ c where
  field left-identity : ∀ {x y} (f : B x y) → ε ∙ f ≋ f

open LeftIdentity ⦃ … ⦄ public

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
  {a} {A : Ø a}
  {b} (B : A → A → Ø b)
  {c} (C : ∀ {x y} → B x y → B x y → Ø c)
  {d} (D : ∀ {x y} → B x y → B x y → Ø d)
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
  {a} {A : Ø a}
  {b} (B : A → A → Ø b)
  {c} (C : ∀ {x y} → B x y → B x y → Ø c)
  {d} (D : ∀ {x y} → B x y → B x y → ∀ {z} → B y z → B y z → Ø d)
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
