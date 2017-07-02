
module Oscar.Prelude where

module _ where -- Objectevel

  open import Agda.Primitive public
    using ()
    renaming ( Level to Ł
             ; lzero to ∅̂
             ; lsuc to ↑̂_
             ; _⊔_ to _∙̂_ )

  infix 0 Ø_
  Ø_ : ∀ 𝔬 → Set (↑̂ 𝔬)
  Ø_ 𝔬 = Set 𝔬

  Ø₀ = Ø ∅̂
  Ø₁ = Ø (↑̂ ∅̂)

postulate
  magic : ∀ {a} {A : Ø a} → A

module _ where -- Function

  infixr 9 _∘_
  _∘_ : ∀ {a b c}
          {A : Set a} {B : A → Set b} {C : {x : A} → B x → Set c} →
          (∀ {x} (y : B x) → C y) → (g : (x : A) → B x) →
          ((x : A) → C (g x))
  f ∘ g = λ x → f (g x)

  ¡ : ∀ {𝔬} {𝔒 : Ø 𝔬} → 𝔒 → 𝔒
  ¡ 𝓞 = 𝓞

  infixl -10 ¡
  syntax ¡ {𝔒 = A} x = x ofType A

  _∋_ : ∀ {a} (A : Set a) → A → A
  A ∋ x = x

  _∞ : ∀ {a} {A : Set a} → A → ∀ {b} {B : Set b} → B → A
  _∞ x = λ _ → x

  _∞⟦_⟧ : ∀ {a} {A : Set a} → A → ∀ {b} (B : Set b) → B → A
  x ∞⟦ B ⟧ = _∞ x {B = B}

  _∞₁ : ∀ ..{a} ..{A : Set a} → A → ∀ ..{b} ..{B : Set b} → ∀ ..{h} ..{H : Set h} → .(_ : B) .{_ : H} → A
  _∞₁ f _ = f

  _∞₃ : ∀ ..{a} ..{A : Set a} → A → ∀ ..{b} ..{B : Set b} → ∀ ..{h₁ h₂ h₃} ..{H₁ : Set h₁} ..{H₂ : Set h₂} ..{H₃ : Set h₃} → .(_ : B) .{_ : H₁} .{_ : H₂} .{_ : H₃} → A
  _∞₃ f _ = f

  hid : ∀ {a} {A : Set a} {x : A} → A
  hid {x = x} = x

  it : ∀ {a} {A : Set a} {{x : A}} → A
  it {{x}} = x
  {-# INLINE it #-}

  ! = it

  asInstance : ∀ {a b} {A : Set a} {B : A → Set b} (x : A) → (∀ {{x}} → B x) → B x
  asInstance x f = f {{x}}
  {-# INLINE asInstance #-}

  flip : ∀ {a b c} {A : Set a} {B : Set b} {C : A → B → Set c} → (∀ x y → C x y) → ∀ y x → C x y
  flip f x y = f y x
  {-# INLINE flip #-}

  infixr -20 _$_
  _$_ : ∀ {a b} {A : Set a} {B : A → Set b} → (∀ x → B x) → ∀ x → B x
  f $ x = f x

  -- The S combinator. (Written infix as in Conor McBride's paper
  -- "Outrageous but Meaningful Coincidences: Dependent type-safe syntax
  -- and evaluation".)

  _ˢ_ : ∀ {a b c}
          {A : Set a} {B : A → Set b} {C : (x : A) → B x → Set c} →
        ((x : A) (y : B x) → C x y) →
        (g : (x : A) → B x) →
        ((x : A) → C x (g x))
  f ˢ g = λ x → f x (g x)

  infixr 0 case_of_ case_return_of_

  case_of_ : ∀ {a b} {A : Set a} {B : Set b} → A → (A → B) → B
  case x of f = f x

  case_return_of_ : ∀ {a b} {A : Set a} (x : A) (B : A → Set b) → (∀ x → B x) → B x
  case x return B of f = f x

  infixl 8 _on_
  _on_ : ∀ {a b c} {A : Set a} {B : A → Set b} {C : ∀ x y → B x → B y → Set c} →
           (∀ {x y} (z : B x) (w : B y) → C x y z w) → (f : ∀ x → B x) → ∀ x y →
           C x y (f x) (f y)
  h on f = λ x y → h (f x) (f y)
  {-# INLINE _on_ #-}

Function : ∀ {a} (A B : Ø a) → Ø a
Function A B = A → B

Function⟦_⟧ : ∀ a (A B : Ø a) → Ø a
Function⟦ a ⟧ = Function {a = a}

module _ where

  Extension : ∀ {𝔬} {𝔒 : Ø 𝔬} {𝔭} (𝔓 : 𝔒 → Ø 𝔭) → 𝔒 → 𝔒 → Ø 𝔭
  Extension 𝔓 m n = 𝔓 m → 𝔓 n

module _ where

  _⟨_⟩→_ : ∀ {𝔬} {𝔒 : Ø 𝔬} → 𝔒 → ∀ {𝔭} → (𝔒 → Ø 𝔭) → 𝔒 → Ø 𝔭
  m ⟨ 𝔓 ⟩→ n = Extension 𝔓 m n

Arrow : ∀
  {𝔵} {𝔛 : Ø 𝔵}
  {𝔞} (𝔄 : 𝔛 → Ø 𝔞)
  {𝔟} (𝔅 : 𝔛 → Ø 𝔟)
  → 𝔛 → 𝔛
  → Ø 𝔞 ∙̂ 𝔟
Arrow 𝔄 𝔅 x y = 𝔄 x → 𝔅 y

Property : ∀
  {𝔵} (𝔛 : Ø 𝔵)
  ℓ
  → Ø 𝔵 ∙̂ ↑̂ ℓ
Property 𝔛 ℓ = 𝔛 → Ø ℓ

Relation : ∀
  {𝔞} (𝔄 : Ø 𝔞)
  ℓ → Ø 𝔞 ∙̂ ↑̂ ℓ
Relation 𝔄 ℓ = 𝔄 → Property 𝔄 ℓ

Dotter :
  (∀ {𝔞} (𝔄 : Ø 𝔞) ℓ → Ø 𝔞 ∙̂ ↑̂ ℓ)
  → ∀
      {𝔵} {𝔛 : Ø 𝔵}
      {𝔞} (𝔄 : 𝔛 → Ø 𝔞)
      ℓ → Ø 𝔵 ∙̂ 𝔞 ∙̂ ↑̂ ℓ
Dotter D 𝔄 ℓ = ∀ {x} → D (𝔄 x) ℓ

Ṙelation : ∀
  {𝔵} {𝔛 : Ø 𝔵}
  {𝔞} (𝔄 : 𝔛 → Ø 𝔞)
  ℓ → Ø 𝔵 ∙̂ 𝔞 ∙̂ ↑̂ ℓ
Ṙelation = Dotter Relation

Extended : ∀
    {𝔞} {𝔄 : Ø 𝔞}
    {𝔟} {𝔅 : Ø 𝔟}
    {ℓ} (_≈_ : 𝔅 → 𝔅 → Ø ℓ)
    → (𝔄 → 𝔅) → (𝔄 → 𝔅)
    → Ø 𝔞 ∙̂ ℓ
Extended _≈_ = λ f g → ∀ x → f x ≈ g x

Ṗroperty : ∀
  {𝔵} {𝔛 : Ø 𝔵}
  {𝔬} (𝔒 : Property 𝔛 𝔬)
  ℓ
  → Ø 𝔵 ∙̂ 𝔬 ∙̂ ↑̂ ℓ
Ṗroperty = Dotter Property

module _ where

  infixr 5 _,_
  record Σ {𝔬} (𝔒 : Ø 𝔬) {𝔭} (𝔓 : 𝔒 → Ø 𝔭) : Ø 𝔬 ∙̂ 𝔭 where
    constructor _,_
    field
      π₀ : 𝔒
      π₁ : 𝔓 π₀

  open Σ public

  _×_ : ∀ {𝔬₁} (𝔒₁ : Ø 𝔬₁) {𝔬₂} (𝔒₂ : Ø 𝔬₂) → Ø 𝔬₁ ∙̂ 𝔬₂
  _×_ O₁ O₂ = Σ O₁ (λ _ → O₂)

  ∃_ : ∀ {𝔬} {𝔒 : Ø 𝔬} {𝔭} (𝔓 : 𝔒 → Ø 𝔭) → Ø 𝔬 ∙̂ 𝔭
  ∃_ = Σ _

  uncurry : ∀ {a b c} {A : Set a} {B : A → Set b} {C : ∀ x → B x → Set c} →
              (∀ x (y : B x) → C x y) → (p : Σ A B) → C (π₀ p) (π₁ p)
  uncurry f (x , y) = f x y

ExtendedṖroperty : ∀
  {𝔵} {𝔛 : Ø 𝔵}
  {𝔬} (𝔒 : 𝔛 → Ø 𝔬)
  ℓ
  {ℓ̇} (_↦_ : ∀ {x} → 𝔒 x → 𝔒 x → Ø ℓ̇)
  → Ø 𝔵 ∙̂ 𝔬 ∙̂ ↑̂ ℓ ∙̂ ℓ̇
ExtendedṖroperty 𝔒 ℓ _↦_ = Σ (Ṗroperty 𝔒 ℓ) (λ P → ∀ {x} {f g : 𝔒 x} → f ↦ g → Extension P f g)

ArrowsourceṖroperty : ∀
  {𝔵} {𝔛 : Ø 𝔵}
  {𝔬₁} (𝔒₁ : 𝔛 → Ø 𝔬₁)
  {𝔬₂} (𝔒₂ : 𝔛 → Ø 𝔬₂)
  ℓ
  → 𝔛
  → Ø 𝔵 ∙̂ 𝔬₁ ∙̂ 𝔬₂ ∙̂ ↑̂ ℓ
ArrowsourceṖroperty 𝔒₁ 𝔒₂ ℓ x = Ṗroperty (Arrow 𝔒₁ 𝔒₂ x) ℓ

ArrowsourceExtendedṖroperty : ∀
  {𝔵} {𝔛 : Ø 𝔵}
  {𝔬₁} (𝔒₁ : 𝔛 → Ø 𝔬₁)
  {𝔬₂} (𝔒₂ : 𝔛 → Ø 𝔬₂)
  ℓ
  → (x : 𝔛) → ∀
    {ℓ̇} (_↦_ : ∀ {y} → Arrow 𝔒₁ 𝔒₂ x y → Arrow 𝔒₁ 𝔒₂ x y → Ø ℓ̇) → Ø 𝔵 ∙̂ 𝔬₁ ∙̂ 𝔬₂ ∙̂ ↑̂ ℓ ∙̂ ℓ̇
ArrowsourceExtendedṖroperty 𝔒₁ 𝔒₂ ℓ x _↦_ = ExtendedṖroperty (Arrow 𝔒₁ 𝔒₂ x) ℓ _↦_
