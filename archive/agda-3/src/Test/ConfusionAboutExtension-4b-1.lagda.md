evidently, the choice of constraint makes no difference for transextensionality

```agda
open import Oscar.Class.Transitivity
open import Oscar.Data.Proposequality
open import Oscar.Data.Constraint
open import Oscar.Prelude
open import Oscar.Data.𝟙

module Test.ConfusionAboutExtension-4b-1 where

record InnerClass {ℓ} {𝔢} {CONSTRAINTS : Ø 𝔢} (constraints : CONSTRAINTS) (_ : Constraint constraints) (SET-METHOD : Ø ℓ) : Ø ℓ where
  field ⋆ : SET-METHOD

open InnerClass public

module Symoid
  {𝔬} {𝔒 : Ø 𝔬}
  {𝔯} (_∼_ : 𝔒 → 𝔒 → Ø 𝔯)
  where
  record Class : Ø 𝔬 ∙̂ 𝔯 where
    field _∙'_ : 𝔒 → 𝔒 → 𝔒
    field symoid : ∀ x y → (x ∙' y) ∼ (y ∙' x)

open Symoid.Class ⦃ … ⦄ using (symoid) public

module Symmetry
  {𝔬} {𝔒 : Ø 𝔬}
  {𝔯} (_∼_ : 𝔒 → 𝔒 → Ø 𝔯)
  (_∙_ : 𝔒 → 𝔒 → 𝔒)
  where

  type = ∀ x y → (x ∙ y) ∼ (y ∙ x)
  class = InnerClass
            -- _∙_
            -- _∼_ -- works
            -- ((λ x y → (x ∙ y) ∼ (y ∙ x)) ,, _∼_)
            -- (λ x y → (x ∙ y) ∼ (y ∙ x))
            -- (λ (x : 𝔒) y z → (y ∼ z) × ((x ∙ y) ∼ (y ∙ x)))
            -- (_∙_ ,, flip _∙_ ,, λ (x : 𝔒) y → ((x ∙ y) ∼ (y ∙ x)) ,, _∼_) -- works
            -- (flip _∼_) -- works
            -- (_∙_ ,, flip _∙_ ,, λ (x : 𝔒) y z → ((x ∙ y) ∼ z) ,, ∀ x y → x ∼ y) -- works
            -- (∀ x y → x ∼ y) -- works
            -- (∀ {x y} → x ∼ y) -- works
            -- type
            -- (∀ x y → (x ∙ y) ∼ y)
            -- (∀ y → ∃ λ x → x ∼ y) -- works
            -- (λ y → ∀ x → x ∼ y) -- works
            (∀ x y → x ∼ y) -- works
            -- 𝟙
            -- 𝔒
            ∅ type

  record Class : Ø 𝔬 ∙̂ 𝔯 where
    field method' : type

  method : ⦃ _ : class ⦄ → type
  method ⦃ ⌶ ⦄ = InnerClass.⋆ ⌶

  method' : ⦃ _ : Class ⦄ → type
  method' ⦃ ⌶ ⦄ = Class.method' ⌶

module Transextensionality
  {𝔬} {𝔒 : Ø 𝔬}
  {𝔯} (_∼_ : 𝔒 → 𝔒 → Ø 𝔯)
  {ℓ} (_∼̇_ : ∀ {x y} → x ∼ y → x ∼ y → Ø ℓ) (let infix 4 _∼̇_ ; _∼̇_ = _∼̇_)
  (transitivity : Transitivity.type _∼_)
  (let _∙_ : FlipTransitivity.type _∼_
       _∙_ g f = transitivity f g)
  where

  type : Ø ℓ ∙̂ (𝔯 ∙̂ 𝔬)
  type = ∀ {x z} y {f₁ f₂ : x ∼ y} {g₁ g₂ : y ∼ z} → f₁ ∼̇ f₂ → g₁ ∼̇ g₂ → g₁ ∙ f₁ ∼̇ g₂ ∙ f₂

  class : Ø ℓ ∙̂ (𝔯 ∙̂ 𝔬)
  class = InnerClass (𝔒 ,, _∼_ ,, (λ {x y} → _∼̇_ {x} {y}) ,, λ {x y z} → transitivity {x} {y} {z} ,, λ {x y z} {f₁ f₂ : x ∼ y} {g₁ g₂ : y ∼ z} → f₁ ∼̇ f₂ → g₁ ∼̇ g₂ → g₁ ∙ f₁ ∼̇ g₂ ∙ f₂)
                     -- 𝟙
                     -- (λ {x y} → _∼̇_ {x} {y})
                     -- (λ x y z (f₁ f₂ : x ∼ y) (g₁ g₂ : y ∼ z) → f₁ ∼̇ f₂)
                     ∅
                     type

  record Class : Ø ℓ ∙̂ (𝔯 ∙̂ 𝔬) where
    field method' : type

  method : ⦃ _ : class ⦄ → type
  method ⦃ ⌶ ⦄ = InnerClass.⋆ ⌶

  method' : ⦃ _ : Class ⦄ → type
  method' ⦃ ⌶ ⦄ = Class.method' ⌶

module _ {𝔬} {𝔒 : Ø 𝔬} where
  postulate
    transitivity' : Transitivity.type Proposequality⟦ 𝔒 ⟧

postulate X : Set
postulate t : X → X → X

Symoid--any : ∀
  {a} {A : Ø a}
  {m} {_⊸_ : A → A → Ø m}
  {transitivity : A → A → A}
  → Symoid.Class _⊸_
Symoid--any {transitivity = transitivity} .Symoid.Class._∙'_ = transitivity
Symoid--any .Symoid.Class.symoid x y = magic

Symoid--single : ∀
  {a} {A : Ø a}
  {transitivity : A → A → A}
  → Symoid.Class Proposequality⟦ A ⟧
Symoid--single {transitivity = transitivity} .Symoid.Class._∙'_ = transitivity
Symoid--single .Symoid.Class.symoid x y = magic

Symoid--one : Symoid.Class Proposequality⟦ X ⟧
Symoid--one .Symoid.Class._∙'_ = t
Symoid--one .Symoid.Class.symoid x y = magic

postulate

  Symmetry--any : ∀
    {a} {A : Ø a}
    {m} {_⊸_ : A → A → Ø m}
    {transitivity : A → A → A}
    → Symmetry.class _⊸_ transitivity

  Symmetry--single : ∀
    {a} {A : Ø a}
    {transitivity : A → A → A}
    → Symmetry.class Proposequality⟦ A ⟧ transitivity

  Symmetry--one : Symmetry.class Proposequality⟦ X ⟧ t

  Symmetry--any' : ∀
    {a} {A : Ø a}
    {m} {_⊸_ : A → A → Ø m}
    {transitivity : A → A → A}
    → Symmetry.Class _⊸_ transitivity

  Symmetry--single' : ∀
    {a} {A : Ø a}
    {transitivity : A → A → A}
    → Symmetry.Class Proposequality⟦ A ⟧ transitivity

  Symmetry--one' : Symmetry.Class Proposequality t

  Transextensionality--Morphism=Proposequality : ∀
    {a} {A : Ø a}
    {m} {_⊸_ : A → A → Ø m}
    {transitivity : Transitivity.type _⊸_}
    → Transextensionality.class _⊸_ Proposequality transitivity

  Transextensionality--Morphism=Proposequality' : ∀
    {a} {A : Ø a}
    {m} {_⊸_ : A → A → Ø m}
    {transitivity : Transitivity.type _⊸_}
    → Transextensionality.Class _⊸_ Proposequality transitivity

  T : X → X → Set
  trans : ∀ {x y z} → T x y → T y z → T x z
  T-Transextensionality--Proposequality-trans : Transextensionality.Class T Proposequality trans
  T-Transextensionality--Proposequality-trans' : Transextensionality.class T Proposequality trans

module _
  {a} {A : Ø a}
  where

  postulate
    Transextensionality--Object=Proposequality,Morphism=Proposequality : Transextensionality.class Proposequality⟦ A ⟧ Proposequality transitivity'
    Transextensionality--Object=Proposequality,Morphism=Proposequality' : Transextensionality.Class Proposequality⟦ A ⟧ Proposequality transitivity'

module Test-Symoid
  where

  TestClass = Symoid.Class Proposequality⟦ X ⟧
  TestType = Symmetry.type Proposequality t

  module Test--class--one where
    instance _ = Symoid--one
    _ = TestClass ∋ !
    _ = TestType ∋ symoid

  module Test--class--single where
    instance _ = Symoid--single
    _ = TestClass ∋ !
    _ = TestType ∋ symoid

  module Test--class--any where
    instance _ = Symoid--any
    _ = TestClass ∋ !
    _ = TestType ∋ symoid {_∼_ = Proposequality}
    _ = TestType ∋ symoid

module Test-Symmetry
  where

  TestClass = Symmetry.class Proposequality t
  TestClass' = Symmetry.Class Proposequality t
  TestType = Symmetry.type Proposequality t

  module Test--class--one where
    instance _ = Symmetry--one
    _ = TestClass ∋ !
    _ = TestType ∋ Symmetry.method _ _

  module Test--class--single where
    instance _ = Symmetry--single
    _ = TestClass ∋ !
    _ = TestType ∋ Symmetry.method _ _

  module Test--class--any where
    instance _ = Symmetry--any
    _ = TestClass ∋ !
    _ = TestType ∋ Symmetry.method Proposequality _
    _ = TestType ∋ Symmetry.method _ t

  module Test--Class--one where
    instance _ = Symmetry--one'
    _ = TestClass' ∋ !
    _ = TestType ∋ Symmetry.method' Proposequality _
    _ = TestType ∋ Symmetry.method' _ t
    _ = TestType ∋ Symmetry.method' _ _

  module Test--Class--single where
    instance _ = Symmetry--single'
    _ = TestClass' ∋ !
    _ = TestType ∋ Symmetry.method' Proposequality _
    _ = TestType ∋ Symmetry.method' _ t
    _ = TestType ∋ Symmetry.method' _ _

  module Test--Class--any where
    instance _ = Symmetry--any'
    _ = TestClass' ∋ !
    _ = TestType ∋ Symmetry.method' Proposequality _
    _ = TestType ∋ Symmetry.method' _ t

module Test-T-Transextensionality--Proposequality-trans
  {a} {A : Ø a}
  where

  TestClass = Transextensionality.class T Proposequality trans
  TestClass' = Transextensionality.Class T Proposequality trans
  TestType = Transextensionality.type T Proposequality trans

  module Test--T-Transextensionality--Proposequality-trans where
    instance _ = T-Transextensionality--Proposequality-trans'
    _ = TestClass ∋ !
    _ = TestType ∋ Transextensionality.method _ _ _

  module Test--T-Transextensionality--Proposequality-trans' where
    instance _ = T-Transextensionality--Proposequality-trans
    _ = TestClass' ∋ !
    _ = TestType ∋ Transextensionality.method' T Proposequality trans
    _ = TestType ∋ Transextensionality.method' _ _ _

module Test-Transextensionality
  {a} {A : Ø a}
  where

  TestClass = Transextensionality.class Proposequality⟦ A ⟧ Proposequality transitivity'
  TestClass' = Transextensionality.Class Proposequality⟦ A ⟧ Proposequality transitivity'
  TestType = Transextensionality.type Proposequality⟦ A ⟧ Proposequality transitivity'

  module Test--class--Object=Any where
    instance _ = Transextensionality--Morphism=Proposequality
    _ = TestClass ∋ !
    _ = TestType ∋ Transextensionality.method Proposequality⟦ _ ⟧ (λ {x y} → Proposequality⟦ Proposequality⟦ A ⟧ x y ⟧) transitivity'
    _ = TestType ∋ Transextensionality.method Proposequality⟦ _ ⟧ _ transitivity'
    _ = TestType ∋ Transextensionality.method _ Proposequality transitivity'
    _ = TestType ∋ Transextensionality.method Proposequality⟦ A ⟧ Proposequality _
    _ = TestType ∋ Transextensionality.method Proposequality⟦ A ⟧ (λ {x y} → Proposequality⟦ Proposequality⟦ A ⟧ x y ⟧) transitivity'


  module Test--Class--Object=Any where
    instance _ = Transextensionality--Morphism=Proposequality'
    _ = TestClass' ∋ !
    _ = TestType ∋ Transextensionality.method' Proposequality⟦ _ ⟧ Proposequality transitivity'
    _ = TestType ∋ Transextensionality.method' Proposequality⟦ A ⟧ _ transitivity'
    _ = TestType ∋ Transextensionality.method' Proposequality⟦ _ ⟧ _ transitivity'
    _ = TestType ∋ Transextensionality.method' Proposequality⟦ A ⟧ Proposequality _

  module Test--class--Object=Proposequality where
    instance _ = Transextensionality--Object=Proposequality,Morphism=Proposequality
    _ = TestClass ∋ !
    _ = TestType ∋ Transextensionality.method _ _ _

  module Test--Class--Object=Proposequality where
    instance _ = Transextensionality--Object=Proposequality,Morphism=Proposequality'
    _ = TestClass' ∋ !
    _ = TestType ∋ Transextensionality.method' _ Proposequality _
    _ = TestType ∋ Transextensionality.method' Proposequality⟦ A ⟧ _ transitivity'
    _ = TestType ∋ Transextensionality.method' Proposequality⟦ _ ⟧ _ transitivity'
    _ = TestType ∋ Transextensionality.method' Proposequality⟦ A ⟧ _ _

  module Test--class--both where
    instance _ = Transextensionality--Morphism=Proposequality
    instance _ = Transextensionality--Object=Proposequality,Morphism=Proposequality
    _ = TestClass ∋ !

  module Test--Class--both where
    instance _ = Transextensionality--Morphism=Proposequality'
    instance _ = Transextensionality--Object=Proposequality,Morphism=Proposequality'
    _ = TestClass' ∋ !

```

The choices for _∼̇_ are more arbitrary than I would intuitively expect: I would think that the given equivalence should somehow go-along with the morphism. If there are two or more equivalences that make sense for a given morphism, then either there should be a separate calling function (such as ≡-transextensionality) or there should be a parameter supplied by the user to distinguish which equivalence is to be used here.

```agda
-- FIXME incomplete (obviously)
-- record MorphismEquivalence
--   field
--     _∼̇_
```

Another idea is to try building-up Category theory wherein we take seriously the mathematician's notion of equality (rather than the agnostic type-theorist's fuzzier one). We'll then include alternative notions of equality (hopefully) in some "higher" category. Let's start by seeing whether we're going to run into trouble even for the smallest categorical concepts.
