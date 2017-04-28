
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
  𝓽ransitivity = ∀ {x y} → B x y → ∀ {z} → B y z → B x z
  record Transitivity : Ø a ∙̂ b where field transitivity : 𝓽ransitivity

open Transitivity ⦃ … ⦄ public

infixr 9 _∙_
_∙_ : ∀ {a} {A : Set a}
        {b} {B : A → A → Set b}
      ⦃ _ : Transitivity B ⦄
      → ∀ {y z} → B y z → ∀ {x} → B x y → B x z
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
  infix 4 _≋_
  field
    _≋_ : A → A → Ø b
    ⦃ ⌶IsSetoid ⦄ : IsSetoid _≋_

open Equivalence ⦃ … ⦄ public

record Congruity
  a b {c} (C : ∀ {x} {X : Set x} → X → X → Set c)
  : Ø ↑̂ (a ∙̂ b ∙̂ c) where
  field congruity : ∀ {A : Set a} {B : Set b} (f : A → B) {x y} → C x y → C (f x) (f y)

open Congruity ⦃ … ⦄ public

record Congruity₂
  a b c {ℓ} (EQ : ∀ {x} {X : Set x} → X → X → Set ℓ)
  : Ø ↑̂ (a ∙̂ b ∙̂ c ∙̂ ℓ) where
  field congruity₂ : ∀ {A : Set a} {B : Set b} {C : Set c} (f : A → B → C) {x y} → EQ x y → ∀ {x' y'} → EQ x' y' → EQ (f x x') (f y y')

open Congruity₂ ⦃ … ⦄ public

record Ċongruity
  𝔬 𝔭 {c}
  (C : ∀ {𝔒 : Ø 𝔬} {𝔓 : 𝔒 → Ø 𝔭} → ((𝓞 : 𝔒) → 𝔓 𝓞) → ((𝓞 : 𝔒) → 𝔓 𝓞) → Ø c)
  : Ø ↑̂ (𝔬 ∙̂ 𝔭) ∙̂ c
  where
  field ċongruity : ∀ {𝔒 : Ø 𝔬} {𝔓 : 𝔒 → Ø 𝔭} (F : ∀ {𝓞 : 𝔒} → 𝔓 𝓞 → 𝔓 𝓞) {f g : (𝓞 : 𝔒) → 𝔓 𝓞} → C f g → C (F ∘ f) (F ∘ g)

open Ċongruity ⦃ … ⦄ public

module _
  {a} {A : Set a}
  {b} (B : A → A → Set b)
  {c} (C : A → A → Set c)
  where
  𝓶ap = ∀ {x y} → B x y → C x y
  record Map : Ø a ∙̂ b ∙̂ c where field map : 𝓶ap
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
  {a₁} {A₁ : Ø a₁} {b₁}
    (B₁ : A₁ → A₁ → Ø b₁)
      ⦃ _ : Reflexivity B₁ ⦄
  {a₂} {A₂ : Ø a₂} {b₂}
    (B₂ : A₂ → A₂ → Ø b₂)
      ⦃ _ : Reflexivity B₂ ⦄
    c₂
      ⦃ _ : ∀ {x y} → Equivalence (B₂ x y) c₂ ⦄
    (μ : A₁ → A₂)
      ⦃ _ : Map B₁ (B₂ on μ) ⦄
  where
  𝓲dentity = ∀ {x} → map (ε⟦ B₁ ⟧ {x = x}) ≋ ε⟦ B₂ ⟧ {x = μ x}
  record Identity : Ø a₁ ∙̂ c₂ where field identity : 𝓲dentity
  open Identity ⦃ … ⦄ public

record Equivalence₂
  {a} {A : Ø a} {b}
    (B : A → A → Ø b)
    c
  : Ø a ∙̂ b ∙̂ ↑̂ c where
    infix 4 _≈_
    field
      _≈_ : ∀ {x y} → B x y → B x y → Ø c
      ⦃ ⌶IsSetoid ⦄ : ∀ {x y} → IsSetoid (_≈_ {x} {y})

    instance ⌶Equivalence : ∀ {x y} → Equivalence (B x y) c
    ⌶Equivalence = record { _≋_ = _≈_ }

open Equivalence₂ ⦃ … ⦄ hiding (⌶Equivalence) public

module _
  {a} {A : Ø a} {b}
    (B : A → A → Ø b)
      ⦃ _ : Reflexivity B ⦄
      ⦃ _ : Transitivity B ⦄
    c
      ⦃ _ : Equivalence₂ B c ⦄
  where
  𝓵eft-identity = ∀ {x y} (f : B x y) → ε ∙ f ≋ f
  record LeftIdentity : Ø a ∙̂ b ∙̂ c where field left-identity : 𝓵eft-identity
  open LeftIdentity ⦃ … ⦄ public

  𝓻ight-identity = ∀ {x y} (f : B x y) → f ∙ ε ≋ f
  record RightIdentity : Ø a ∙̂ b ∙̂ c where field right-identity : 𝓻ight-identity
  open RightIdentity ⦃ … ⦄ public

module _
  {a₁} {A₁ : Ø a₁} {b₁}
    (B₁ : A₁ → A₁ → Ø b₁)
      ⦃ _ : Transitivity B₁ ⦄
  {a₂} {A₂ : Ø a₂} {b₂}
    (B₂ : A₂ → A₂ → Ø b₂)
      ⦃ _ : Transitivity B₂ ⦄
    c₂
      ⦃ _ : Equivalence₂ B₂ c₂ ⦄
    (μ : A₁ → A₂)
      ⦃ _ : Map B₁ (B₂ on μ) ⦄
  where
  𝓬ommutativity = ∀ {x y} (f : B₁ x y) {z} (g : B₁ y z) → map[ B₂ on μ ] (g ∙ f) ≋ map g ∙ map f
  record Commutativity : Ø a₁ ∙̂ b₁ ∙̂ c₂ where field commutativity : 𝓬ommutativity

open Commutativity ⦃ … ⦄ public

module _
  {a} {A : Ø a} {b}
    (B : A → A → Ø b)
      ⦃ _ : Transitivity B ⦄
    c
      ⦃ _ : Equivalence₂ B c ⦄
  where
  𝓪ssociativity = ∀ {w x} (f : B w x) {y} (g : B x y) {z} (h : B y z) → (h ∙ g) ∙ f ≋ h ∙ g ∙ f
  record Associativity : Ø a ∙̂ b ∙̂ c where field associativity : 𝓪ssociativity
  open Associativity ⦃ … ⦄ public

module _
  {a₁} {A₁ : Ø a₁} {b₁}
    (B₁ : A₁ → A₁ → Ø b₁)
    c₁
      ⦃ _ : Equivalence₂ B₁ c₁ ⦄
  {a₂} {A₂ : Ø a₂} {b₂}
    (B₂ : A₂ → A₂ → Ø b₂)
    c₂
      ⦃ _ : Equivalence₂ B₂ c₂ ⦄
    (μ : A₁ → A₂)
      ⦃ _ : Map B₁ (B₂ on μ) ⦄
  where
  𝓮xtensionality₁ = ∀ {x y} {f₁ f₂ : B₁ x y} → f₁ ≋ f₂ → map[ B₂ on μ ] f₁ ≋ map f₂
  record Extensionality₁ : Ø a₁ ∙̂ b₁ ∙̂ c₁ ∙̂ c₂ where field extensionality₁ : 𝓮xtensionality₁
  open Extensionality₁ ⦃ … ⦄ public

module _
  {a} {A : Ø a} {b}
    (B : A → A → Ø b)
      ⦃ _ : Transitivity B ⦄
    c
      ⦃ _ : Equivalence₂ B c ⦄
  where
  𝓮xtensionality₂ = ∀ {x y} {f₁ f₂ : B x y} → f₁ ≋ f₂ → ∀ {z} {g₁ g₂ : B y z} → g₁ ≋ g₂ → g₁ ∙ f₁ ≋ g₂ ∙ f₂
  record Extensionality₂ : Ø a ∙̂ b ∙̂ c where field extensionality₂ : 𝓮xtensionality₂
  open Extensionality₂ ⦃ … ⦄ public

private

  module Isis where

    record IsSemigroupoid
      {a} {A : Ø a} {b}
        (B : A → A → Ø b)
        c
          ⦃ _ : Equivalence₂ B c ⦄
      : Ø a ∙̂ b ∙̂ c where
      field
        ⦃ ⌶Transitivity ⦄ : Transitivity B
        ⦃ ⌶Extensionality₂ ⦄ : Extensionality₂ B c
        ⦃ ⌶Associativity ⦄ : Associativity B c

    record IsCategory
      {a} {A : Ø a} {b}
        (B : A → A → Ø b)
        c
          ⦃ _ : Equivalence₂ B c ⦄
      : Ø a ∙̂ b ∙̂ c where
      field
        ⦃ ⌶IsSemigroupoid ⦄ : IsSemigroupoid B c
        ⦃ ⌶Reflexivity ⦄ : Reflexivity B
        ⦃ ⌶LeftIdentity ⦄ : LeftIdentity B c
        ⦃ ⌶RightIdentity ⦄ : RightIdentity B c

    record IsSemifunctor
      {a₁} {A₁ : Ø a₁} {b₁}
        (B₁ : A₁ → A₁ → Ø b₁)
        c₁
          ⦃ _ : Equivalence₂ B₁ c₁ ⦄
      {a₂} {A₂ : Ø a₂} {b₂}
        (B₂ : A₂ → A₂ → Ø b₂)
        c₂
          ⦃ _ : Equivalence₂ B₂ c₂ ⦄
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
      {a₁} {A₁ : Ø a₁} {b₁}
        (B₁ : A₁ → A₁ → Ø b₁)
        c₁
          ⦃ _ : Equivalence₂ B₁ c₁ ⦄
      {a₂} {A₂ : Ø a₂} {b₂}
        (B₂ : A₂ → A₂ → Ø b₂)
        c₂
          ⦃ _ : Equivalence₂ B₂ c₂ ⦄
        (μ : A₁ → A₂)
      : Ø a₁ ∙̂ b₁ ∙̂ c₁ ∙̂ a₂ ∙̂ b₂ ∙̂ c₂
      where
      field
        ⦃ ⌶IsCategory₁ ⦄ : IsCategory B₁ c₁
        ⦃ ⌶IsCategory₂ ⦄ : IsCategory B₂ c₂
        ⦃ ⌶IsSemifunctor ⦄ : IsSemifunctor B₁ c₁ B₂ c₂ μ
        ⦃ ⌶Identity ⦄ : Identity B₁ B₂ c₂ μ

private

  module Category where
    open Isis

    record Setoid a b : Ø ↑̂ (a ∙̂ b) where
      field
        Obj : Ø a
        Eq : Obj → Obj → Ø b
        ⦃ ⌶IsSetoid ⦄ : IsSetoid Eq

    record Semigroupoid a b c : Ø ↑̂ (a ∙̂ b ∙̂ c) where
      field
        Obj : Ø a
        Hom : Obj → Obj → Ø b
        Eq : ∀ {x y} → Hom x y → Hom x y → Ø c
        ⦃ ⌶IsSetoid ⦄ : ∀ {x y} → IsSetoid (Eq {x} {y})

      instance ⌶Equivalence₂ : Equivalence₂ Hom c
      ⌶Equivalence₂ = record { _≈_ = Eq }

      field
        ⦃ ⌶IsSemigroupoid ⦄ : IsSemigroupoid Hom c

    record Category a b c : Ø ↑̂ (a ∙̂ b ∙̂ c) where
      field
        Obj : Ø a
        Hom : Obj → Obj → Ø b
        Eq : ∀ {x y} → Hom x y → Hom x y → Ø c
        ⦃ ⌶IsSetoid ⦄ : ∀ {x y} → IsSetoid (Eq {x} {y})

      instance ⌶Equivalence₂ : Equivalence₂ Hom c
      ⌶Equivalence₂ = record { _≈_ = Eq }

      field
        ⦃ ⌶IsCategory ⦄ : IsCategory Hom c

    record Semifunctor a b c d e f : Ø ↑̂ (a ∙̂ b ∙̂ c ∙̂ d ∙̂ e ∙̂ f) where
      field
        Obj₁ : Ø a
        Hom₁ : Obj₁ → Obj₁ → Ø b
        Eq₁ : ∀ {x y} → Hom₁ x y → Hom₁ x y → Ø c
        ⦃ ⌶IsSetoid₁ ⦄ : ∀ {x y} → IsSetoid (Eq₁ {x} {y})

      instance ⌶Equivalence₂₁ : Equivalence₂ Hom₁ c
      ⌶Equivalence₂₁ = record { _≈_ = Eq₁ }

      field
        Obj₂ : Ø d
        Hom₂ : Obj₂ → Obj₂ → Ø e
        Eq₂ : ∀ {x y} → Hom₂ x y → Hom₂ x y → Ø f
        ⦃ ⌶IsSetoid₂ ⦄ : ∀ {x y} → IsSetoid (Eq₂ {x} {y})

      instance ⌶Equivalence₂₂ : Equivalence₂ Hom₂ f
      ⌶Equivalence₂₂ = record { _≈_ = Eq₂ }

      field
        μ : Obj₁ → Obj₂
        ⦃ ⌶IsSemifunctor ⦄ : IsSemifunctor Hom₁ c Hom₂ f μ

    record Functor a b c d e f : Ø ↑̂ (a ∙̂ b ∙̂ c ∙̂ d ∙̂ e ∙̂ f) where
      field
        Obj₁ : Ø a
        Hom₁ : Obj₁ → Obj₁ → Ø b
        Eq₁ : ∀ {x y} → Hom₁ x y → Hom₁ x y → Ø c
        ⦃ ⌶IsSetoid₁ ⦄ : ∀ {x y} → IsSetoid (Eq₁ {x} {y})

      instance ⌶Equivalence₂₁ : Equivalence₂ Hom₁ c
      ⌶Equivalence₂₁ = record { _≈_ = Eq₁ }

      field
        Obj₂ : Ø d
        Hom₂ : Obj₂ → Obj₂ → Ø e
        Eq₂ : ∀ {x y} → Hom₂ x y → Hom₂ x y → Ø f
        ⦃ ⌶IsSetoid₂ ⦄ : ∀ {x y} → IsSetoid (Eq₂ {x} {y})

      instance ⌶Equivalence₂₂ : Equivalence₂ Hom₂ f
      ⌶Equivalence₂₂ = record { _≈_ = Eq₂ }

      field
        μ : Obj₁ → Obj₂
        ⦃ ⌶IsFunctor ⦄ : IsFunctor Hom₁ c Hom₂ f μ

open Isis public
open Category public
