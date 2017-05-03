
module Oscar.Class where

open import Oscar.Prelude

record Reflexivity
  {a} {A : Set a}
  {b} (B : A → A → Set b) : Ø a ∙̂ b where
  field reflexivity : ∀ {x} → B x x

open Reflexivity ⦃ … ⦄ public

ε : ∀ {a} {A : Set a}
      {b} {B : A → A → Set b}
    ⦃ _ : Reflexivity B ⦄
    → ∀ {x} → B x x
ε = reflexivity

ε⟦_⟧ : ∀ {a} {A : Set a}
         {b} (B : A → A → Set b)
       ⦃ _ : Reflexivity B ⦄
       → ∀ {x} → B x x
ε⟦ _ ⟧ = reflexivity

record Symmetry
  {a} {A : Set a}
  {b} (B : A → A → Set b) : Ø a ∙̂ b where
  field symmetry : ∀ {x y} → B x y → B y x

open Symmetry ⦃ … ⦄ public

module _
  {a} {A : Set a}
  {b} (B : A → A → Set b)
  where
  𝓽ransitivity = ∀ {x y z} → B x y → B y z → B x z
  record Transitivity : Ø a ∙̂ b where field transitivity : 𝓽ransitivity

open Transitivity ⦃ … ⦄ public

infixr 9 _∙_
_∙_ : ∀ {a} {A : Set a}
        {b} {B : A → A → Set b}
      ⦃ _ : Transitivity B ⦄
      → ∀ {y z x} → B y z → B x y → B x z
g ∙ f = transitivity f g

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
  : Ø ↑̂ (𝔬 ∙̂ 𝔭) ∙̂ c
  where
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

map⟦_⟧ : ∀
  {a} {A : Set a}
  {b} (B : A → A → Set b)
  {c} {C : A → A → Set c}
  ⦃ _ : Map B C ⦄
  → ∀ {x y} → B x y → C x y
map⟦ B ⟧ f = map f

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
  𝓲dentity = 𝓲dentity′ (λ x → map (ε⟦ B₁ ⟧ {x = x}) ≋ ε⟦ B₂ ⟧ {x = μ x})
  Identity = Identity′ (λ x → map (ε⟦ B₁ ⟧ {x = x}) ≋ ε⟦ B₂ ⟧ {x = μ x})

{-
module _
  {a₁} {A₁ : Ø a₁} {b₁} (B₁ : A₁ → A₁ → Ø b₁)
  {a₂} {A₂ : Ø a₂} {b₂} (B₂ : A₂ → A₂ → Ø b₂) c₂
  (μ : A₁ → A₂)
  ⦃ _ : MorphismEquivalence B₂ c₂ ⦄
  ⦃ _ : Reflexivity B₁ ⦄
  ⦃ _ : Reflexivity B₂ ⦄
  ⦃ _ : Map B₁ (B₂ on μ) ⦄
  where
    𝓲dentity = ∀ {x} → map (ε⟦ B₁ ⟧ {x = x}) ≋ ε⟦ B₂ ⟧ {x = μ x}
    record Identity : Ø a₁ ∙̂ b₁ ∙̂ a₂ ∙̂ b₂ ∙̂ c₂ where field identity : 𝓲dentity
open Identity ⦃ … ⦄ public
-}

module _
  {a} {A : Set a}
  {b} (B : A → A → Set b)
  {c} (C : ∀ {x y} → B x y → Set c)
  where
  𝓵eftIdentity′ = ∀ {x y} (f : B x y) → C f
  record LeftIdentity′ : Ø a ∙̂ b ∙̂ c where field left-identity : 𝓵eftIdentity′

open LeftIdentity′ ⦃ … ⦄ public

module _
  {a} {A : Ø a} {b}
    (B : A → A → Ø b)
    c
    ⦃ _ : MorphismEquivalence B c ⦄
    ⦃ _ : Reflexivity B ⦄
    ⦃ _ : Transitivity B ⦄
  where
  𝓵eftIdentity = 𝓵eftIdentity′ B (λ f → (ε ∙ f) ≋ f)
  LeftIdentity = LeftIdentity′ B (λ f → (ε ∙ f) ≋ f)

module _
  {a} {A : Set a}
  {b} (B : A → A → Set b)
  {c} (C : ∀ {x y} → B x y → Set c)
  where
  𝓻ightIdentity′ = ∀ {x y} (f : B x y) → C f
  record RightIdentity′ : Ø a ∙̂ b ∙̂ c where field right-identity : 𝓻ightIdentity′

open RightIdentity′ ⦃ … ⦄ public

module _
  {a} {A : Ø a} {b}
    (B : A → A → Ø b)
    c
    ⦃ _ : MorphismEquivalence B c ⦄
    ⦃ _ : Reflexivity B ⦄
    ⦃ _ : Transitivity B ⦄
  where
  𝓻ightIdentity = 𝓻ightIdentity′ B (λ f → (f ∙ ε) ≋ f)
  RightIdentity = RightIdentity′ B (λ f → (f ∙ ε) ≋ f)

module _
  {a} {A : Set a}
  {b} (B : A → A → Set b)
  {c} (C : ∀ {x y} → B x y → ∀ {z} → B y z → Set c)
  where
  𝓬ommutativity′ = ∀ {x y} (f : B x y) {z} (g : B y z) → C f g
  record Commutativity′ : Ø a ∙̂ b ∙̂ c where field commutativity : 𝓬ommutativity′

open Commutativity′ ⦃ … ⦄ public

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

module _
  {a} {A : Set a}
  {b} (B : A → A → Set b)
  {c} (C : ∀ {w x y z} → B w x → B x y → B y z → Set c)
  where
  𝓪ssociativity′ = ∀ {w x y z} (f : B w x) (g : B x y) (h : B y z) → C f g h
  record Associativity′ : Ø a ∙̂ b ∙̂ c where field associativity : 𝓪ssociativity′

open Associativity′ ⦃ … ⦄ public

associativity⟦_⟧ : ∀
  {a} {A : Set a}
  {b} {B : A → A → Set b}
  {c} (C : ∀ {w x y z} → B w x → B x y → B y z → Set c)
  ⦃ _ : Associativity′ B C ⦄
  → 𝓪ssociativity′ B C
associativity⟦ _ ⟧ = associativity

module _
  {a} {A : Ø a} {b}
    (B : A → A → Ø b)
    c
    ⦃ _ : MorphismEquivalence B c ⦄
    ⦃ _ : Transitivity B ⦄
  where
  𝑎ssociativity : ∀ {w x y z} → B w x → B x y → B y z → Set c
  𝑎ssociativity = λ f g h → ((h ∙ g) ∙ f) ≋ (h ∙ g ∙ f)
  𝓪ssociativity = 𝓪ssociativity′ B 𝑎ssociativity
  Associativity = Associativity′ B 𝑎ssociativity

associativity[_] : ∀
  {a} {A : Ø a} {b}
    (B : A → A → Ø b)
    {c}
    ⦃ _ : MorphismEquivalence B c ⦄
    ⦃ _ : Transitivity B ⦄
    ⦃ _ : Associativity B c ⦄
  → 𝓪ssociativity B c
associativity[ _ ] = associativity

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

  record Succ {x} (X : Ø x) : Ø x where
    field
      ⇑ : X → X
  open Succ ⦃ … ⦄

  record PrincipalX {x} {X : Ø x} {a} (A : X → Ø a) : Ø₀ where no-eta-equality
  record PrincipalX2 {x} {X : Ø x} {a} (A : X → Ø a) {b} (B : X → Ø b) : Ø₀ where no-eta-equality

  record Succ* {x} {X : Ø x} {a} (A : X → Ø a)
    -- ⦃ iS : Succ X ⦄
    -- ⦃ _ : PrincipalX A ⦄
    : Ø x ∙̂ a where
    field
      ⟰ : ⦃ _ : Succ X ⦄ → ∀ {m} → A m → A (⇑ m)
  open Succ* ⦃ … ⦄

  record Maybe* a b : Ø ↑̂ (a ∙̂ b) where
    field
      Maybe : Ø a → Ø b
      just : ∀ {A : Ø a} → A → Maybe A
  open Maybe* ⦃ … ⦄

  record Thin {x} {X : Ø x} {a} (A : X → Ø a) {b} (B : X → Ø b)
--    ⦃ iS* : Succ X ⦄
    -- ⦃ _ : PrincipalX B ⦄
    : Ø x ∙̂ a ∙̂ b where
    field
      thin : ⦃ _ : Succ X ⦄ → ∀ {m : X} → A (⇑ m) → B m → B (⇑ m)
  open Thin ⦃ … ⦄

  record ThinInjective {x} {X : Ø x} {a} (A : X → Ø a) {b} (B : X → Ø b) c
    -- ⦃ _ : Succ X ⦄
    -- ⦃ _ : ∀ {x} → Equivalence (B x) c ⦄
    -- ⦃ _ : IndexedEquivalence B c ⦄
    -- ⦃ _ : PrincipalX B ⦄
    -- ⦃ _ : Thin A B ⦄
    -- ⦃ _ : Thin A B ⦄
    : Ø x ∙̂ a ∙̂ b ∙̂ ↑̂ c where
    field
      thin-injective : ⦃ _ : Succ X ⦄ ⦃ _ : ∀ {x} → Equivalence (B x) c ⦄ ⦃ _ : Thin A B ⦄ → ∀ {m} (x : A (⇑ m)) {y₁ y₂ : B m} → thin x y₁ ≋ thin x y₂ → y₁ ≋ y₂
  open ThinInjective ⦃ … ⦄

  record Thick {x} {X : Ø x} {a} (A : X → Ø a) {b} (B : X → Ø b)
    -- ⦃ _ : Succ X ⦄
    -- ⦃ _ : PrincipalX B ⦄
    : Ø x ∙̂ a ∙̂ b where
    field
      thick : ⦃ _ : Succ X ⦄ → ∀ {m} → B (⇑ m) → A m → B m
  open Thick ⦃ … ⦄

  record ThickThinId {x} {X : Ø x} {a} (A : X → Ø a) {b} (B : X → Ø b) c
    -- ⦃ _ : Succ X ⦄
    -- ⦃ _ : PrincipalX A ⦄
    -- ⦃ _ : PrincipalX B ⦄
    -- ⦃ _ : Succ* A ⦄
    -- ⦃ _ : ∀ {x} → Equivalence (B x) c ⦄
    -- ⦃ _ : Thin A B ⦄
    -- ⦃ _ : Thick A B ⦄
    : Ø x ∙̂ a ∙̂ b ∙̂ ↑̂ c where
    field
      thick∘thin=id : ⦃ _ : Succ X ⦄ ⦃ _ : Succ* A ⦄ ⦃ _ : ∀ {x} → Equivalence (B x) c ⦄ ⦃ _ : Thin A B ⦄ ⦃ _ : Thick A B ⦄ → ∀ {m} (x : A m) (y : B m) → thick (thin (⟰ x) y) x ≋ y
  open ThickThinId ⦃ … ⦄

  record Check {x} {X : Ø x} {a} (A : X → Ø a) {b} (B : X → Ø b) c
    -- ⦃ _ : Succ X ⦄
    -- ⦃ _ : PrincipalX B ⦄
    -- ⦃ _ : Maybe* b c ⦄
    : Ø x ∙̂ a ∙̂ ↑̂ (b ∙̂ c) where
    field
      check : ⦃ _ : Succ X ⦄ ⦃ _ : Maybe* b c ⦄ → ∀ {m} → A (⇑ m) → B (⇑ m) → Maybe (B m)
  open Check ⦃ … ⦄

  record ThinCheckId {x} {X : Ø x} {a} (A : X → Ø a) {b} (B : X → Ø b) c ℓc
    : Ø x ∙̂ a ∙̂ ↑̂ (b ∙̂ c ∙̂ ℓc) where
    field
      thin-check-id : ⦃ _ : Succ X ⦄ ⦃ _ : Maybe* b c ⦄ ⦃ _ : ∀ {x} → Equivalence (B x) c ⦄ ⦃ _ : ∀ {x} → Equivalence (Maybe (B x)) ℓc ⦄ ⦃ _ : Thin A B ⦄ ⦃ _ : Check A B c ⦄ → ∀ {m} (x : A (⇑ m)) y → ∀ (y' : B m) → thin x y' ≋ y → check x y ≋ just y'

  record ThickAndThin {x} {X : Ø x} {a} (A : X → Ø a) {b} (B : X → Ø b) c ℓc
    -- ⦃ _ : Succ X ⦄
    -- ⦃ _ : PrincipalX A ⦄
    -- ⦃ _ : PrincipalX B ⦄
    -- ⦃ _ : Succ* A ⦄
    -- ⦃ _ : Maybe* b c ⦄
    -- -- ⦃ _ : IndexedEquivalence B c ⦄
    -- -- ⦃ _ : IndexedEquivalence Maybe m ⦄
    -- ⦃ _ : ∀ {x} → Equivalence (B x) c ⦄
    -- ⦃ _ : ∀ {x} → Equivalence (Maybe (B x)) ℓc ⦄
    : Ø x ∙̂ a ∙̂ ↑̂ b ∙̂ ↑̂ c ∙̂ ↑̂ ℓc where
    field
      ⦃ iThin ⦄ : Thin A B
      -- thin : ∀ {m} → A (⇑ m) → B m → B (⇑ m)
      ⦃ iThinInjective ⦄ : ThinInjective A B c
      -- thin-injective : ∀ {m} (x : A (⇑ m)) {y₁ y₂ : B m} → thin x y₁ ≋ thin x y₂ → y₁ ≋ y₂
      ⦃ iThick ⦄ : Thick A B
      -- thick : ∀ {m} → B (⇑ m) → A m → B m
      ⦃ iThickThinId ⦄ : ThickThinId A B c
      -- thick∘thin=id : ∀ {m} (x : A m) (y : B m) → thick (thin (⟰ x) y) x ≋ y
      ⦃ iCheck ⦄ : Check A B c
      -- check : ∀ {m} → A (⇑ m) → B (⇑ m) → Maybe (B m)
      -- thin-check-id : ⦃ _ : Succ X ⦄ ⦃ _ : Maybe* b c ⦄ ⦃ _ : ∀ {x} → Equivalence (B x) c ⦄ ⦃ _ : ∀ {x} → Equivalence (Maybe (B x)) ℓc ⦄ → ∀ {m} (x : A (⇑ m)) y → ∀ (y' : B m) → thin x y' ≋ y → check x y ≋ just y'
  open ThickAndThin ⦃ … ⦄

--   module _
--     {x} {X : Ø x} {a} (A : X → Ø a) {b} (B : X → Ø b) c m
--     ⦃ iS* : Succ* A ⦄
--     ⦃ iS* : Succ* B ⦄
--     ⦃ iM* : Maybe* b c ⦄
--     -- ⦃ _ : IndexedEquivalence B c ⦄
--     -- ⦃ _ : IndexedEquivalence Maybe m ⦄
--     ⦃ _ : ∀ {x} → Equivalence (B x) c ⦄
--     ⦃ _ : ∀ {x} → Equivalence (Maybe (B x)) m ⦄
--     ⦃ _ : ThickAndThin A B c m ⦄
--     where
--     test-thin : ∀ {m} → A (⇑ m) → B m → B (⇑ m)
--     test-thin = thin

--     test-thin-injective : ∀ {m} (x : A (⇑ m)) {y₁ y₂ : B m} → thin x y₁ ≋ thin x y₂ → y₁ ≋ y₂
--     test-thin-injective = thin-injective

--     test-thick∘thin=id : ∀ {m} (x : A m) (y : B m) → thick (thin (⟰ x) y) x ≋ y
--     test-thick∘thin=id = thick∘thin=id

--     test-check : ∀ {m} → A (⇑ m) → B (⇑ m) → Maybe (B m)
--     test-check = check

--     test-thin-check-id : ∀ {m} (x : A (⇑ m)) y → ∀ (y' : B m) → thin x y' ≋ y → check x y ≋ just y'
--     test-thin-check-id = thin-check-id

-- --   record ThickAndThin {x} {X : Ø x} {a} (A : X → Ø a) {b} (B : X → Ø b) c : Ø x ∙̂ a ∙̂ ↑̂ b ∙̂ ↑̂ c where
-- --     field
-- --       ⦃ iS* ⦄ : Succ* A
-- --       ⦃ iM* ⦄ : Maybe* b c
-- --       thin : ∀ {m} → A (⇑ m) → B m → B (⇑ m)
-- --       thin-injective : ∀ {m} (x : A (⇑ m)) {y₁ y₂ : B m} → thin x y₁ ≡ thin x y₂ → y₁ ≡ y₂
-- --       thick : ∀ {m} → B (⇑ m) → A m → B m
-- --       thick∘thin=id : ∀ {m} (x : A m) (y : B m) → thick (thin (⟰ x) y) x ≡ y
-- --       check : ∀ {m} → A (⇑ m) → B (⇑ m) → Maybe (B m)
-- --       thin-check-id : ∀ {m} (x : A (⇑ m)) y → ∀ y' → thin x y' ≡ y → check x y ≡ just y'
-- --   open ThickAndThin ⦃ … ⦄

-- --   module _
-- --     {x} {X : Ø x} {a} (A : X → Ø a) {b} (B : X → Ø b) c
-- --     ⦃ _ : ThickAndThin A B c ⦄
-- --     where
-- --     test-thin-injective : ∀ {m} (x : A (⇑ m)) {y₁ y₂ : B m} → thin x y₁ ≡ thin x y₂ → y₁ ≡ y₂
-- --     test-thin-injective = thin-injective

-- --     test-thin-check-id : ∀ {m} (x : A (⇑ m)) y → ∀ (y' : B m) → thin x y' ≡ y → check x y ≡ just y'
-- --     test-thin-check-id = thin-check-id



-- -- --   postulate
-- -- --     foottt : ∀ {x} {X : Ø x} {a} (A : X → Ø a) ⦃ _ : Succ* A ⦄ → ∀ {m} (x : A m) → ⟰ x ≡ ⟰ x

-- -- -- --   record Succ {x} (X : Ø x) : Ø x where
-- -- -- --     field
-- -- -- --       ⇑ : X → X
-- -- -- --   open Succ ⦃ … ⦄

-- -- -- --   record Succ* {x} {X : Ø x} ⦃ _ : Succ X ⦄ {a} (A : X → Ø a) : Ø x ∙̂ a where
-- -- -- --     field
-- -- -- --       ⟰ : ∀ {m} → A m → A (⇑ m)
-- -- -- --   open Succ* ⦃ … ⦄

-- -- -- --   postulate
-- -- -- --     foottt : ∀ {x} {X : Ø x} ⦃ _ : Succ X ⦄ {a} (A : X → Ø a) ⦃ _ : Succ* A ⦄ → ∀ {m} (x : A m) → ⟰ x ≡ ⟰ x

-- -- -- -- --   record Foo {x} {X : Ø x} ⦃ _ : Succ X ⦄ {a} (A : X → Ø a) ⦃ _ : Succ* A ⦄ : Ø x ∙̂ a where
-- -- -- -- --     field
-- -- -- -- --       foo : ∀ {m} (x : A m) → ⟰ x ≡ ⟰ x

-- -- -- -- --   record ThickAndThin {x} {X : Ø x} ⦃ _ : Succ X ⦄ {a} (A : X → Ø a) ⦃ _ : Succ* A ⦄ {b} (B : X → Ø b) c : Ø x ∙̂ a ∙̂ ↑̂ b ∙̂ ↑̂ c where
-- -- -- -- --     field
-- -- -- -- --       Maybe : Ø b → Ø c
-- -- -- -- --       just : ∀ {x} → (y : B x) → Maybe (B x)
-- -- -- -- --       thin : ∀ {m} → A (⇑ m) → B m → B (⇑ m)
-- -- -- -- --       thin-injective : ∀ {m} (x : A (⇑ m)) {y₁ y₂ : B m} → thin x y₁ ≡ thin x y₂ → y₁ ≡ y₂
-- -- -- -- --       thick : ∀ {m} → B (⇑ m) → A m → B m
-- -- -- -- --       foo : ∀ {m} (x : A m) → ⟰ x ≡ ⟰ x
-- -- -- -- --       thick∘thin=id : ∀ {m} (x : A m) (y : B m) → thick (thin (⟰ x) y) x ≡ y
-- -- -- -- --       check : ∀ {m} → A (⇑ m) → B (⇑ m) → Maybe (B m)
-- -- -- -- --       thin-check-id : ∀ {m} (x : A (⇑ m)) y → ∀ y' → thin x y' ≡ y → check x y ≡ just y'

-- -- -- -- --   open ThickAndThin ⦃ … ⦄ public

-- -- -- -- -- --   module _
-- -- -- -- -- --     {x} {X : Ø x} {a} (A : X → Ø a) {b} (B : X → Ø b) c
-- -- -- -- -- --     ⦃ _ : Succ X ⦄
-- -- -- -- -- --     ⦃ _ : ThickAndThin A B c ⦄
-- -- -- -- -- --     where
-- -- -- -- -- --     test-thin : ∀ {m} → A (⇑ m) → B m → B (⇑ m)
-- -- -- -- -- --     test-thin = {!!}

-- -- -- -- -- -- -- {-
-- -- -- -- -- -- -- --open import Oscar.Data
-- -- -- -- -- -- --   record ThickAndThin {a} (A : ¶ → Set a) : Set a where
-- -- -- -- -- -- --     field
-- -- -- -- -- -- --       thin : ∀ {m} → Fin (↑ m) → A m → A (↑ m)
-- -- -- -- -- -- --       thin-injective : ∀ {m} (x : Fin (↑ m)) {y₁ y₂ : A m} → thin x y₁ ≡ thin x y₂ → y₁ ≡ y₂
-- -- -- -- -- -- --       thick : ∀ {m} → A (↑ m) → Fin m → A m
-- -- -- -- -- -- --       thick∘thin=id : ∀ {m} (x : Fin m) (y : A m) → thick (thin (↑ x) y) x ≡ y
-- -- -- -- -- -- --       check : ∀ {m} → Fin (↑ m) → A (↑ m) → Maybe (A m)
-- -- -- -- -- -- --       thin-check-id : ∀ {m} (x : Fin (↑ m)) y → ∀ y' → thin x y' ≡ y → check x y ≡ ↑ y'

-- -- -- -- -- -- --   open ThickAndThin ⦃ … ⦄ public
-- -- -- -- -- -- -- -}

-- -- -- -- -- -- --   module _
-- -- -- -- -- -- --     {a} {A : Ø a} {b}
-- -- -- -- -- -- --       (B : A → Ø b)
-- -- -- -- -- -- --     {c}
-- -- -- -- -- -- --       (C : (x : A) → B x → Ø c)
-- -- -- -- -- -- --     {d}
-- -- -- -- -- -- --       (D : (x : A) → (y : B x) → C x y → Ø d)
-- -- -- -- -- -- --     where
-- -- -- -- -- -- --     𝓽hin′ = ∀ {x : A} → (y : B x) → (z : C x y) → D x y z
-- -- -- -- -- -- --     record Thin′ : Ø a ∙̂ b ∙̂ c ∙̂ d where field thin : 𝓽hin′
-- -- -- -- -- -- --     open Thin′ ⦃ … ⦄ public

-- -- -- -- -- -- --   module _
-- -- -- -- -- -- --     {x} {X : Ø x} {a}
-- -- -- -- -- -- --       (A : X → Ø a)
-- -- -- -- -- -- --     {f}
-- -- -- -- -- -- --       (F : X → Ø f)
-- -- -- -- -- -- --       (s : X → X)
-- -- -- -- -- -- --     where
-- -- -- -- -- -- --     𝓽hin = 𝓽hin′ (F ∘ s) (λ m _ → A m) (λ m _ _ → (A (s m)))
-- -- -- -- -- -- --     Thin = Thin′ (F ∘ s) (λ m _ → A m) (λ m _ _ → (A (s m)))

-- -- -- -- -- -- --   open import Agda.Builtin.Equality

-- -- -- -- -- -- --   module _
-- -- -- -- -- -- --     {x} {X : Ø x} {a}
-- -- -- -- -- -- --       (A : X → Ø a)
-- -- -- -- -- -- --     {f}
-- -- -- -- -- -- --       (F : X → Ø f)
-- -- -- -- -- -- --       (s : X → X)
-- -- -- -- -- -- --       -- ⦃ _ : Thin A F s ⦄
-- -- -- -- -- -- --       ⦃ _ : Thin′ {A = X} (F ∘ s) (λ x _ → A x) (λ x _ _ → A (s x)) ⦄
-- -- -- -- -- -- --       ℓa
-- -- -- -- -- -- --       ⦃ _ : IndexedEquivalence A ℓa ⦄
-- -- -- -- -- -- --     where
-- -- -- -- -- -- --     thin-test : ∀ {m} (x : F (s m)) → A m → A (s m)
-- -- -- -- -- -- --     thin-test = thin

-- -- -- -- -- -- --     thin-test' : ∀ {m} (x : F (s m)) → {y₁ y₂ : A m} → thin x y₁ ≡ thin x y₂ → y₁ ≋ y₂
-- -- -- -- -- -- --     thin-test' = {!!}


-- -- -- -- -- -- --   open import Oscar.R

-- -- -- -- -- -- --   module _
-- -- -- -- -- -- --     {x} {X : Ø x} {a}
-- -- -- -- -- -- --       {A : X → Ø a}
-- -- -- -- -- -- --     {f}
-- -- -- -- -- -- --       {F : X → Ø f}
-- -- -- -- -- -- --       {s : X → X}
-- -- -- -- -- -- --       ⦃ _ : 𝓡₄,₁ X (F ∘ s) (λ x _ → A x) (λ x _ _ → A (s x)) ⦄
-- -- -- -- -- -- --     where
-- -- -- -- -- -- --     thin-R : ∀ {m} → F (s m) → A m → A (s m)
-- -- -- -- -- -- --     thin-R {m} x a = 𝓻₄,₁,₀ _ x a

-- -- -- -- -- -- --     module _
-- -- -- -- -- -- --         ℓa
-- -- -- -- -- -- --         ⦃ _ : IndexedEquivalence A ℓa ⦄
-- -- -- -- -- -- --       where
-- -- -- -- -- -- --       test-thin-R-1 : ∀ {m} (x : F (s m)) {y₁ y₂ : A m} → thin-R x y₁ ≋ 𝓻₄,₁,₀ _ x y₂ → y₁ ≋ y₂
-- -- -- -- -- -- --       test-thin-R-1 = {!!}

-- -- -- -- -- -- --   module _
-- -- -- -- -- -- --     {x} {X : Ø x} {a}
-- -- -- -- -- -- --       (A : X → Ø a)
-- -- -- -- -- -- --     {f}
-- -- -- -- -- -- --       (F : X → Ø f)
-- -- -- -- -- -- --       (s : X → X)
-- -- -- -- -- -- --       ⦃ iR : 𝓡₄,₁ X (F ∘ s) (λ x _ → A x) (λ x _ _ → A (s x)) ⦄
-- -- -- -- -- -- --       ℓa
-- -- -- -- -- -- --       ⦃ iE : IndexedEquivalence A ℓa ⦄
-- -- -- -- -- -- --     where
-- -- -- -- -- -- --     test-thin-R-2 : ∀ {m} (x : F (s m)) {y₁ y₂ : A m} → thin-R {F = {!!}} x y₁ ≋ 𝓻₄,₁,₀ _ x y₂ → y₁ ≋ y₂
-- -- -- -- -- -- --     test-thin-R-2 = {!!}





-- -- -- -- -- -- -- --     module _ ⦃ r6 : 𝓡₆,₁ X (F ∘ s) (λ x _ → A x) (λ x _ _ → A x) (λ x f y₁ y₂ → 𝓻₄,₁,₀ _ f y₁ ≋ thin-R f y₂) (λ _ _ y₁ y₂ _ → y₁ ≋ y₂) ⦄
-- -- -- -- -- -- -- --       where

-- -- -- -- -- -- -- --       thin-injective-R : ∀ {m} (x : F (s m)) {y₁ y₂ : A m} → thin-R x y₁ ≋ thin-R x y₂ → y₁ ≋ y₂
-- -- -- -- -- -- -- --       thin-injective-R {m} x {y₁} {y₂} teq = 𝓻₆,₁,₀ m x y₁ y₂ teq






-- -- -- -- -- -- -- -- --   record Successor {a} (A : Ø a) : Ø a where
-- -- -- -- -- -- -- -- --     field successor : A → A
-- -- -- -- -- -- -- -- --   open Successor ⦃ … ⦄ public
-- -- -- -- -- -- -- -- --   record IndexedSuccessor {a} (A : Ø a) b
-- -- -- -- -- -- -- -- --     : Ø a ∙̂ ↑̂ b where
-- -- -- -- -- -- -- -- --     field indexedSuccessor : (A → Ø b) → A → Ø b
-- -- -- -- -- -- -- -- --   open IndexedSuccessor ⦃ … ⦄ public
-- -- -- -- -- -- -- -- --   record Successor! {a} {A : Ø a} {b} (B : A → Ø b)
-- -- -- -- -- -- -- -- --     : Ø a ∙̂ ↑̂ b where
-- -- -- -- -- -- -- -- --     field successor! : (A → Ø b) → A → Ø b
-- -- -- -- -- -- -- -- --   open Successor! ⦃ … ⦄ public


-- -- -- -- -- -- -- -- --   module _
-- -- -- -- -- -- -- -- --     {a} {A : Ø a} {b}
-- -- -- -- -- -- -- -- --       (B : A → Ø b)
-- -- -- -- -- -- -- -- --     {c}
-- -- -- -- -- -- -- -- --       (C : A → Ø c)
-- -- -- -- -- -- -- -- --     {d}
-- -- -- -- -- -- -- -- --       (D : A → Ø d)
-- -- -- -- -- -- -- -- --     where
-- -- -- -- -- -- -- -- --     𝓽hin′ = ∀ {x : A} → B x → C x → D x
-- -- -- -- -- -- -- -- --     record Thin′ : Ø a ∙̂ b ∙̂ c ∙̂ d where field thin : 𝓽hin′
-- -- -- -- -- -- -- -- --     open Thin′ ⦃ … ⦄ public

-- -- -- -- -- -- -- -- --   module _
-- -- -- -- -- -- -- -- --     {x} {X : Ø x} {a}
-- -- -- -- -- -- -- -- --       (A : X → Ø a)
-- -- -- -- -- -- -- -- --     {f}
-- -- -- -- -- -- -- -- --       (F : X → Ø f)
-- -- -- -- -- -- -- -- --       (s : X → X)
-- -- -- -- -- -- -- -- --     where
-- -- -- -- -- -- -- -- --     𝓽hin = 𝓽hin′ (F ∘ s) A (A ∘ s)
-- -- -- -- -- -- -- -- --     Thin = Thin′ (F ∘ s) A (A ∘ s)

-- -- -- -- -- -- -- -- --   module _
-- -- -- -- -- -- -- -- --     {x} {X : Ø x} {a}
-- -- -- -- -- -- -- -- --       (A : X → Ø a)
-- -- -- -- -- -- -- -- --     {f}
-- -- -- -- -- -- -- -- --       (F : X → Ø f)
-- -- -- -- -- -- -- -- --       (s : X → X)
-- -- -- -- -- -- -- -- --       ⦃ _ : Thin A F s ⦄
-- -- -- -- -- -- -- -- --       ℓa
-- -- -- -- -- -- -- -- --       ⦃ iE : IndexedEquivalence A ℓa ⦄
-- -- -- -- -- -- -- -- --     where
-- -- -- -- -- -- -- -- --     thin-test : ∀ {m} (x : F (s m)) → A m → A (s m)
-- -- -- -- -- -- -- -- --     thin-test = thin
-- -- -- -- -- -- -- -- --     thin-test' : ∀ {m} (x : F (s m)) → {y₁ y₂ : A m} → _≋_ {A = A _} (thin x y₁) (thin x y₂) → y₁ ≋ y₂
-- -- -- -- -- -- -- -- --     thin-test' = {!!}
-- -- -- -- -- -- -- -- --     thin-test'' : ∀ {m} (x : F (s m)) → {y₁ y₂ : A m} → _≋_ (thin {D = (A ∘ _)} x y₁) (thin x y₂) → y₁ ≋ y₂
-- -- -- -- -- -- -- -- --     thin-test'' = {!!}

-- -- -- -- -- -- -- -- --   module _
-- -- -- -- -- -- -- -- --     {a} {A : Ø a} {b}
-- -- -- -- -- -- -- -- --       (B : A → Ø b)
-- -- -- -- -- -- -- -- --     {c}
-- -- -- -- -- -- -- -- --       (C : A → Ø c)
-- -- -- -- -- -- -- -- --       ⦃ _ : Successor A ⦄
-- -- -- -- -- -- -- -- --     where
-- -- -- -- -- -- -- -- --     𝓽hin! = ∀ {x : A} → B (successor x) → C x → C (successor x)
-- -- -- -- -- -- -- -- --     record Thin! : Ø a ∙̂ b ∙̂ c where field thin! : 𝓽hin!
-- -- -- -- -- -- -- -- --     open Thin! ⦃ … ⦄ public

-- -- -- -- -- -- -- -- --   module _
-- -- -- -- -- -- -- -- --     {x} {X : Ø x} {a}
-- -- -- -- -- -- -- -- --       (A : X → Ø a)
-- -- -- -- -- -- -- -- --     {f}
-- -- -- -- -- -- -- -- --       (F : X → Ø f)
-- -- -- -- -- -- -- -- --       (s : X → X)
-- -- -- -- -- -- -- -- --       ⦃ iS : Successor X ⦄
-- -- -- -- -- -- -- -- --       ⦃ iT : Thin! F A ⦄
-- -- -- -- -- -- -- -- --       ℓa
-- -- -- -- -- -- -- -- --       ⦃ iE : IndexedEquivalence A ℓa ⦄
-- -- -- -- -- -- -- -- --     where
-- -- -- -- -- -- -- -- --     thin-test! : ∀ {m} (x : F (successor m)) → A m → A (successor m)
-- -- -- -- -- -- -- -- --     thin-test! = thin! ⦃ iS ⦄


-- -- -- -- -- -- -- -- -- {-
-- -- -- -- -- -- -- -- --             record 𝓡₄,₁ : Ø 𝔬₀ ∙̂ 𝔬₁ ∙̂ 𝔬₂ ∙̂ 𝔬₃ where
-- -- -- -- -- -- -- -- --             field 𝓻₄,₁,₀ : 𝑹₃
-- -- -- -- -- -- -- -- -- -}

-- -- -- -- -- -- -- -- -- --     thin-test' : ∀ {m} (x : F (s m)) → {y₁ y₂ : A m} → _≋_ {A = A _} (thin x y₁) (thin x y₂) → y₁ ≋ y₂
-- -- -- -- -- -- -- -- -- --     thin-test' = {!!}
-- -- -- -- -- -- -- -- -- --     thin-test'' : ∀ {m} (x : F (s m)) → {y₁ y₂ : A m} → _≋_ (thin {D = (A ∘ _)} x y₁) (thin x y₂) → y₁ ≋ y₂
-- -- -- -- -- -- -- -- -- --     thin-test'' = {!!}



-- -- -- -- -- -- -- -- -- -- -- -- thin-injective : ∀ {m} (x : indexedSuccessor F m) {y₁ y₂ : A m} → thin x y₁ ≋ thin x y₂ → y₁ ≋ y₂
-- -- -- -- -- -- -- -- -- -- --   module _
-- -- -- -- -- -- -- -- -- -- --     {a} {A : Ø a} {b} (B : A → Ø b) {c} (C : A → Ø c) {d} (D : ∀ {w} → B w → C w → C w → Ø d) {e} (E : ∀ {w} → C w → C w → Ø e)
-- -- -- -- -- -- -- -- -- -- --     where
-- -- -- -- -- -- -- -- -- -- --     𝓽hin-injective′ = ∀ {w} (x : B w) {y₁ y₂ : C w} → D x y₁ y₂ → E y₁ y₂
-- -- -- -- -- -- -- -- -- -- --     record ThinInjective′ : Ø a ∙̂ b ∙̂ c ∙̂ d ∙̂ e where field thin-injective : 𝓽hin-injective′
-- -- -- -- -- -- -- -- -- -- --     open ThinInjective′ ⦃ … ⦄ public

-- -- -- -- -- -- -- -- -- -- --   module _
-- -- -- -- -- -- -- -- -- -- --     {x} {X : Ø x} {a}
-- -- -- -- -- -- -- -- -- -- --       (A : X → Ø a)
-- -- -- -- -- -- -- -- -- -- --     {f}
-- -- -- -- -- -- -- -- -- -- --       (F : X → Ø f)
-- -- -- -- -- -- -- -- -- -- --       (s : X → X)
-- -- -- -- -- -- -- -- -- -- --       ℓa
-- -- -- -- -- -- -- -- -- -- --       ⦃ _ : IndexedEquivalence A ℓa ⦄
-- -- -- -- -- -- -- -- -- -- --       ⦃ iThin : Thin A F s ⦄
-- -- -- -- -- -- -- -- -- -- --     where
-- -- -- -- -- -- -- -- -- -- --     𝓽hin-injective = 𝓽hin-injective′
-- -- -- -- -- -- -- -- -- -- --     ThinInjective = ThinInjective′ (F ∘ s) A (λ {_} x y₁ y₂ → thin ⦃ {!!} ⦄ x y₁ ≋ thin x y₂) _≋_


-- -- -- -- -- -- -- -- -- -- -- --   record ThinInjective
-- -- -- -- -- -- -- -- -- -- -- --     {x} {X : Ø x}
-- -- -- -- -- -- -- -- -- -- -- --     {a}
-- -- -- -- -- -- -- -- -- -- -- --       (A : X → Set a)
-- -- -- -- -- -- -- -- -- -- -- --         ⦃ _ : IndexedSuccessor X a ⦄
-- -- -- -- -- -- -- -- -- -- -- --     {f}
-- -- -- -- -- -- -- -- -- -- -- --       (F : X → Set f)
-- -- -- -- -- -- -- -- -- -- -- --         ⦃ _ : IndexedSuccessor X f ⦄
-- -- -- -- -- -- -- -- -- -- -- --         ⦃ iThin : Thin A F ⦄
-- -- -- -- -- -- -- -- -- -- -- --       ℓa
-- -- -- -- -- -- -- -- -- -- -- --         ⦃ _ : IndexedEquivalence A ℓa ⦄
-- -- -- -- -- -- -- -- -- -- -- --     : Ø x ∙̂ a ∙̂ f ∙̂ ℓa where
-- -- -- -- -- -- -- -- -- -- -- --     field
-- -- -- -- -- -- -- -- -- -- -- --       thin-injective : ∀ {m} (x : indexedSuccessor F m) {y₁ y₂ : A m} → thin x y₁ ≋ thin x y₂ → y₁ ≋ y₂

-- -- -- -- -- -- -- -- -- -- -- --   open ThinInjective ⦃ … ⦄ public





-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   record Successor {a} (A : Ø a) : Ø a where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     field successor : A → A
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   open Successor ⦃ … ⦄ public
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   record IndexedSuccessor {a} {A : Ø a} {b} (B : A → Ø b)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ⦃ _ : Successor A ⦄
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     : Ø a ∙̂ b where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     field indexedSuccessor : ∀ {x} → B x → B (successor x)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   open IndexedSuccessor ⦃ … ⦄ public

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- open import Oscar.Data using (Maybe)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   module _ where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     open Successor ⦃ … ⦄ renaming (successor to ↑_)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     open IndexedSuccessor ⦃ … ⦄ renaming (indexedSuccessor to ↑⋆_)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     record Thin
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --       {x} {X : Ø x}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --           ⦃ _ : Successor X ⦄
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --       {a}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --         (A : X → Set a)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --       {f}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --         (F : X → Set f)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --       : Ø x ∙̂ a ∙̂ f where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --       field
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --         thin : ∀ {m} → F (↑ m) → A m → A (↑ m)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     open Thin ⦃ … ⦄ public

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     record ThinInjective
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --       {x} {X : Ø x}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --           ⦃ iSuccessor : Successor X ⦄
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --       {a}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --         (A : X → Set a)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --       {f}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --         (F : X → Set f)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --           ⦃ iThin : Thin A F ⦄
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --         ℓa
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --           ⦃ _ : IndexedEquivalence A ℓa ⦄
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --       : Ø x ∙̂ a ∙̂ f ∙̂ ℓa where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --       field
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --         thin-injective : ∀ {m} (x : F (↑ m)) {y₁ y₂ : A m} → thin ⦃ iSuccessor ⦄ x y₁ ≋ thin ⦃ iSuccessor ⦄ x y₂ → y₁ ≋ y₂

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     open ThinInjective ⦃ … ⦄ public

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     record Thick
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       {x} {X : Ø x}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           ⦃ _ : Successor X ⦄
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       {a}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         (A : X → Set a)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       {f}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         (F : X → Set f)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       : Ø x ∙̂ a ∙̂ f where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       field
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         thick : ∀ {m} → A (↑ m) → F m → A m

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     open Thick ⦃ … ⦄ public

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     record Thick∘thin=id
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       {x} {X : Ø x}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           ⦃ _ : Successor X ⦄
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       {a}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         (A : X → Set a)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       {f}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         (F : X → Set f)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           ⦃ _ : Thin A F ⦄
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           ⦃ _ : Thick A F ⦄
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         ℓa
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           ⦃ _ : IndexedEquivalence A ℓa ⦄
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           ⦃ _ : IndexedSuccessor F ⦄
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       : Ø x ∙̂ a ∙̂ f ∙̂ ℓa where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       field
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         thick∘thin=id : ∀ {m} (x : F m) (y : A m) → thick (thin {!(indexedSuccessor x)!} y) x ≋ y

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     open Thick∘thin=id ⦃ … ⦄ public

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     record ThickAndThin3
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       {x} {X : Ø x} ⦃ _ : Successor X ⦄
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       {a} (A : X → Set a) a' ⦃ _ : IndexedEquivalence A a' ⦄
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       {f} (F : X → Set f)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       ⦃ _ : ThickAndThin1 A a' F ⦄
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       (Maybe : ∀ {i} → Ø i → Ø i) (just : ∀ {i} {I : Ø i} → I → Maybe I) m' ⦃ _ : ∀ {i} → IndexedEquivalence (Maybe {i}) m' ⦄
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       : Ø x ∙̂ a ∙̂ a' ∙̂ f ∙̂ m' where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       field
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         check : ∀ {m} → F (↑ m) → A (↑ m) → Maybe (A m)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         thin-check-id : ∀ {m} (x : F (↑ m)) y → ∀ y' → thin x y' ≋ y → check x y ≋ just y'

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     open ThickAndThin3 ⦃ … ⦄ public

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     test- : ∀
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       {x} {X : Ø x} ⦃ _ : Successor X ⦄
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       {a} {A : X → Set a} {a'} ⦃ _ : IndexedEquivalence A a' ⦄
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       {f} {F : X → Set f}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       ⦃ _ : ThickAndThin1 A a' F ⦄
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       {indexedSuccessor' : ∀ {x} → F x → F (successor x)}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       ⦃ _ : ThickAndThin2 A a' F indexedSuccessor' ⦄
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       → ∀ {m} (x : F m) (y : A m) → thick (thin (indexedSuccessor' x) y) x ≋ y
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     test- = thick∘thin=id

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     test-2 : ∀
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       {x} {X : Ø x} ⦃ _ : Successor X ⦄
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       {a} {A : X → Set a} {a'} ⦃ _ : IndexedEquivalence A a' ⦄
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       {f} {F : X → Set f}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       ⦃ _ : ThickAndThin1 A a' F ⦄
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       {indexedSuccessor' : ∀ {x} → F x → F (successor x)}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       {Maybe : ∀ {i} → Ø i → Ø i} {just : ∀ {i} {I : Ø i} → I → Maybe I} {m'} ⦃ _ : ∀ {i} → IndexedEquivalence (Maybe {i}) m' ⦄
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       ⦃ _ : ThickAndThin2 A a' F indexedSuccessor' ⦄
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       → ∀ {m} (x : F m) (y : A m) → thick (thin (indexedSuccessor' x) y) x ≋ y
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     test-2 = thick∘thin=id


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- test-thin : ∀
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --   {a} {A : ¶ → Set a} {f} {F : ¶ → Set f} ⦃ _ : Upper F ⦄
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --                       {f} {F' : ¶ → Set f} ⦃ _ : Upper F' ⦄
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --   ⦃ _ : ThickAndThin A F ⦄
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --   ⦃ _ : ThickAndThin A F' ⦄
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   --   → ∀ {m} → F (↑ m) → A m → A (↑ m)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -- test-thin = thin
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- {-

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     record ThickAndThin
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       {x} {X : Ø x} ⦃ _ : Successor X ⦄
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       {a} (A : X → Set a) a' ⦃ _ : IndexedEquivalence A a' ⦄
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       {f} (F : X → Set f)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       (indexedSuccessor' : ∀ {x} → F x → F (successor x))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       -- (Maybe : ∀ {i} → Ø i → Ø i) (just : ∀ {i} {I : Ø i} → I → Maybe I) m' ⦃ _ : ∀ {i} → IndexedEquivalence (Maybe {i}) m' ⦄
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       : Ø x ∙̂ a ∙̂ a' ∙̂ f {-∙̂ m'-} where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       field
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         thin : ∀ {m} → F (↑ m) → A m → A (↑ m)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         thin-injective : ∀ {m} (x : F (↑ m)) {y₁ y₂ : A m} → thin x y₁ ≋ thin x y₂ → y₁ ≋ y₂
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         thick : ∀ {m} → A (↑ m) → F m → A m
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         thick∘thin=id : ∀ {m} (x : F m) (y : A m) → thick (thin (indexedSuccessor' x) y) x ≋ y
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         --check : ∀ {m} → F (↑ m) → A (↑ m) → Maybe (A m)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --         --thin-check-id : ∀ {m} (x : F (↑ m)) y → ∀ y' → thin x y' ≋ y → check x y ≋ just y'

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     open ThickAndThin ⦃ … ⦄ public
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -}
