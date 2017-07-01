
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

record Map'
  {a} {A : Set a}
  {b} (B : A → A → Set b)
  {c} (C : ∀ {x y} → B x y → Set c)
  : Ø a ∙̂ b ∙̂ c where
  field map' : ∀ {x y} → (f : B x y) → C f

open Map' ⦃ … ⦄ public

module _
  {a} {A : Set a}
  {b} (B : A → Set b)
  where
  𝓲dentity′ = ∀ {x} → B x
  record Identity′ : Ø a ∙̂ b where field identity : 𝓲dentity′

open Identity′ ⦃ … ⦄ public

module _
  {a₁} {A₁ : Ø a₁} {b₁} (B₁ : A₁ → A₁ → Ø b₁)
  {a₂} {A₂ : Ø a₂} {b₂} (B₂ : A₂ → A₂ → Ø b₂) {c₂} (_≋₂_ : ∀ {x y} → B₂ x y → B₂ x y → Ø c₂)
  (μ : A₁ → A₂)
  ⦃ _ : Reflexivity B₁ ⦄
  ⦃ _ : Reflexivity B₂ ⦄
  ⦃ _ : Map B₁ (B₂ on μ) ⦄
  where
  𝓲dentity = 𝓲dentity′ (λ x → map⟦ B₁ ⟧ (ε {x = x}) ≋₂ ε {x = μ x})
  Identity = Identity′ (λ x → map⟦ B₁ ⟧ (ε {x = x}) ≋₂ ε {x = μ x})

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
  {c}
    (_≋_ : ∀ {x y} → B x y → B x y → Ø c)
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
  {c}
    (_≋_ : ∀ {x y} → B x y → B x y → Ø c)
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
  {a₂} {A₂ : Ø a₂} {b₂} (B₂ : A₂ → A₂ → Ø b₂) {c₂} (_≋₂_ : ∀ {x y} → B₂ x y → B₂ x y → Ø c₂)
  (μ : A₁ → A₂)
  ⦃ _ : Transitivity B₁ ⦄
  ⦃ _ : Transitivity B₂ ⦄
  ⦃ _ : Map B₁ (B₂ on μ) ⦄
  where
  𝓬ommutativity = 𝓬ommutativity′ B₁ (λ f g → map (g ∙ f) ≋₂ (map g ∙ map f))
  Commutativity = Commutativity′ B₁ (λ f g → map (g ∙ f) ≋₂ (map g ∙ map f))

module _
  {a} {A : Set a}
  {b} (B : A → A → Set b)
  {c} (C : ∀ {w x} → B w x → ∀ {y} → B x y → ∀ {z} → B y z → Set c)
  where
  𝓪ssociativity′ = ∀ {w x} (f : B w x) {y} (g : B x y) {z} (h : B y z) → C f g h
  record Associativity′ : Ø a ∙̂ b ∙̂ c where field associativity : 𝓪ssociativity′

open Associativity′ ⦃ … ⦄ public

module _
  {a} {A : Ø a} {b}
    (B : A → A → Ø b)
  {c}
    (_≋_ : ∀ {x y} → B x y → B x y → Ø c)
    ⦃ _ : Transitivity B ⦄
  where
  𝓪ssociativity = 𝓪ssociativity′ B (λ f g h → ((h ∙ g) ∙ f) ≋ (h ∙ g ∙ f))
  Associativity = Associativity′ B (λ f g h → ((h ∙ g) ∙ f) ≋ (h ∙ (g ∙ f)))

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
  {a₁} {A₁ : Ø a₁} {b₁} (B₁ : A₁ → A₁ → Ø b₁) {c₁} (_≋₁_ : ∀ {x y} → B₁ x y → B₁ x y → Ø c₁)
  {a₂} {A₂ : Ø a₂} {b₂} (B₂ : A₂ → A₂ → Ø b₂) {c₂} (_≋₂_ : ∀ {x y} → B₂ x y → B₂ x y → Ø c₂)
  (μ : A₁ → A₂)
  ⦃ _ : Map B₁ (B₂ on μ) ⦄
  where
  Extensionality₁ = Extensionality₁′ B₁ _≋₁_ (λ f₁ f₂ → map f₁ ≋₂ map f₂)
  𝓮xtensionality₁ = 𝓮xtensionality₁′ B₁ _≋₁_ (λ f₁ f₂ → map f₁ ≋₂ map f₂)

module _
  {a} {A : Set a}
  {b} (B : A → A → Set b)
  {c} (C : ∀ {x y} → B x y → B x y → Set c)
  {d} (D : ∀ {x y} → B x y → B x y → ∀ {z} → B y z → B y z → Set d)
  where

  𝓮xtensionality₂′ = ∀ {x y} {f₁ f₂ : B x y} → C f₁ f₂ → ∀ {z} {g₁ g₂ : B y z} → C g₁ g₂ → D f₁ f₂ g₁ g₂
  record Extensionality₂′ : Ø a ∙̂ b ∙̂ c ∙̂ d where field extensionality₂ : 𝓮xtensionality₂′

open Extensionality₂′ ⦃ … ⦄ public

module _
  {a} {A : Ø a} {b} (B : A → A → Ø b) {c} (_≋_ : ∀ {x y} → B x y → B x y → Ø c)
  ⦃ _ : Transitivity B ⦄
  where
  𝓮xtensionality₂ = 𝓮xtensionality₂′ B _≋_ (λ f₁ f₂ g₁ g₂ → (g₁ ∙ f₁) ≋ (g₂ ∙ f₂))
  Extensionality₂ = Extensionality₂′ B _≋_ (λ f₁ f₂ g₁ g₂ → (g₁ ∙ f₁) ≋ (g₂ ∙ f₂))

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

record IsSemigroupoid {a} {A : Ø a} {b} (B : A → A → Ø b) {c} (_≋_ : ∀ {x y} → B x y → B x y → Ø c) : Ø a ∙̂ b ∙̂ c where
  field
    ⦃ ⌶IsSetoid ⦄ : ∀ {x y} → IsSetoid (_≋_ {x} {y})
    ⦃ ⌶Transitivity ⦄ : Transitivity B
    ⦃ ⌶Extensionality₂ ⦄ : Extensionality₂ B _≋_
    ⦃ ⌶Associativity ⦄ : Associativity B _≋_

record IsCategory
  {a} {A : Ø a} {b}
    (B : A → A → Ø b)
  {c}
    (_≋_ : ∀ {x y} → B x y → B x y → Ø c)
  : Ø a ∙̂ b ∙̂ c where
  field
    ⦃ ⌶IsSemigroupoid ⦄ : IsSemigroupoid B _≋_
    ⦃ ⌶Reflexivity ⦄ : Reflexivity B
    ⦃ ⌶LeftIdentity ⦄ : LeftIdentity B _≋_
    ⦃ ⌶RightIdentity ⦄ : RightIdentity B _≋_

record IsSemifunctor
  {a₁} {A₁ : Ø a₁} {b₁} (B₁ : A₁ → A₁ → Ø b₁) {c₁} (_≋₁_ : ∀ {x y} → B₁ x y → B₁ x y → Ø c₁)
  {a₂} {A₂ : Ø a₂} {b₂} (B₂ : A₂ → A₂ → Ø b₂) {c₂} (_≋₂_ : ∀ {x y} → B₂ x y → B₂ x y → Ø c₂)
  (μ : A₁ → A₂)
  : Ø a₁ ∙̂ b₁ ∙̂ c₁ ∙̂ a₂ ∙̂ b₂ ∙̂ c₂
  where
  field
    ⦃ ⌶IsSemigroupoid₁ ⦄ : IsSemigroupoid B₁ _≋₁_
    ⦃ ⌶IsSemigroupoid₂ ⦄ : IsSemigroupoid B₂ _≋₂_
    ⦃ ⌶Map ⦄ : Map B₁ (B₂ on μ)
    ⦃ ⌶Extensionality₁ ⦄ : Extensionality₁ B₁ _≋₁_ B₂ _≋₂_ μ
    ⦃ ⌶Commutativity ⦄ : Commutativity B₁ B₂ _≋₂_ μ

record IsFunctor
  {a₁} {A₁ : Ø a₁} {b₁} (B₁ : A₁ → A₁ → Ø b₁) {c₁} (_≋₁_ : ∀ {x y} → B₁ x y → B₁ x y → Ø c₁)
  {a₂} {A₂ : Ø a₂} {b₂} (B₂ : A₂ → A₂ → Ø b₂) {c₂} (_≋₂_ : ∀ {x y} → B₂ x y → B₂ x y → Ø c₂)
  (μ : A₁ → A₂)
  : Ø a₁ ∙̂ b₁ ∙̂ c₁ ∙̂ a₂ ∙̂ b₂ ∙̂ c₂
  where
  field
    ⦃ ⌶IsCategory₁ ⦄ : IsCategory B₁ _≋₁_
    ⦃ ⌶IsCategory₂ ⦄ : IsCategory B₂ _≋₂_
    ⦃ ⌶IsSemifunctor ⦄ : IsSemifunctor B₁ _≋₁_ B₂ _≋₂_ μ
    ⦃ ⌶Identity ⦄ : Identity B₁ B₂ _≋₂_ μ

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
    ⦃ ⌶IsSemigroupoid ⦄ : IsSemigroupoid Hom Eq

record Category a b c : Ø ↑̂ (a ∙̂ b ∙̂ c) where
  field
    Obj : Ø a
    Hom : Obj → Obj → Ø b
    Eq : ∀ {x y} → Hom x y → Hom x y → Ø c
    ⦃ ⌶IsCategory ⦄ : IsCategory Hom Eq

record Semifunctor a b c d e f : Ø ↑̂ (a ∙̂ b ∙̂ c ∙̂ d ∙̂ e ∙̂ f) where
  field
    Obj₁ : Ø a
    Hom₁ : Obj₁ → Obj₁ → Ø b
    Eq₁ : ∀ {x y} → Hom₁ x y → Hom₁ x y → Ø c
    Obj₂ : Ø d
    Hom₂ : Obj₂ → Obj₂ → Ø e
    Eq₂ : ∀ {x y} → Hom₂ x y → Hom₂ x y → Ø f
    μ : Obj₁ → Obj₂
    ⦃ ⌶IsSemifunctor ⦄ : IsSemifunctor Hom₁ Eq₁ Hom₂ Eq₂ μ

record Functor a b c d e f : Ø ↑̂ (a ∙̂ b ∙̂ c ∙̂ d ∙̂ e ∙̂ f) where
  field
    Obj₁ : Ø a
    Hom₁ : Obj₁ → Obj₁ → Ø b
    Eq₁ : ∀ {x y} → Hom₁ x y → Hom₁ x y → Ø c
    Obj₂ : Ø d
    Hom₂ : Obj₂ → Obj₂ → Ø e
    Eq₂ : ∀ {x y} → Hom₂ x y → Hom₂ x y → Ø f
    μ : Obj₁ → Obj₂
    ⦃ ⌶IsFunctor ⦄ : IsFunctor Hom₁ Eq₁ Hom₂ Eq₂ μ

{-
+ε⟦_⟧ : ∀ {a} {A : Set a}
+         {b} (B : A → A → Set b)
+       ⦃ _ : Reflexivity B ⦄
+       → ∀ {x} → B x x
+ε⟦ _ ⟧ = reflexivity
+
 record Symmetry
   {a} {A : Set a}
   {b} (B : A → A → Set b) : Ø a ∙̂ b where
@@ -39,6 +45,26 @@ _∙_ : ∀ {a} {A : Set a}
       → ∀ {y z} → B y z → ∀ {x} → B x y → B x z
 g ∙ f = transitivity f g

+record IsSetoid
+  {a} {A : Set a}
+  {b} (B : A → A → Set b) : Ø a ∙̂ b where
+  field
+    ⦃ ⌶Reflexivity ⦄ : Reflexivity B
+    ⦃ ⌶Symmetry ⦄ : Symmetry B
+    ⦃ ⌶Transitivity ⦄ : Transitivity B
+
+record Equivalence
+  {a}
+    (A : Set a)
+    b
+  : Ø a ∙̂ ↑̂ b where
+  infix 4 _≋_
+  field
+    _≋_ : A → A → Ø b
+    ⦃ ⌶IsSetoid ⦄ : IsSetoid _≋_
+
+open Equivalence ⦃ … ⦄ public
+
-}
