
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

Arrow : ∀ {𝔵} {𝔛 : Ø 𝔵} {𝔞} {𝔟} → (𝔛 → Ø 𝔞) → (𝔛 → Ø 𝔟) → 𝔛 → 𝔛 → Ø 𝔞 ∙̂ 𝔟
Arrow 𝔄 𝔅 x y = 𝔄 x → 𝔅 y

module _ where

  Extension : ∀ {𝔬} {𝔒 : Ø 𝔬} {𝔭} (𝔓 : 𝔒 → Ø 𝔭) → 𝔒 → 𝔒 → Ø 𝔭
  Extension 𝔓 = Arrow 𝔓 𝔓

module _ where

  _⟨_⟩→_ : ∀ {𝔬} {𝔒 : Ø 𝔬} → 𝔒 → ∀ {𝔭} → (𝔒 → Ø 𝔭) → 𝔒 → Ø 𝔭
  m ⟨ 𝔓 ⟩→ n = Extension 𝔓 m n

π̂ : ∀ {𝔵} ℓ (𝔛 : Ø 𝔵) → Ø 𝔵 ∙̂ ↑̂ ℓ
π̂ ℓ 𝔛 = 𝔛 → Ø ℓ

infixl 21 _←̂_
_←̂_ = π̂

π̇ : ∀ {𝔞 𝔟} (𝔄 : Ø 𝔞) (𝔅 : 𝔄 → Ø 𝔟) → Ø 𝔞 ∙̂ 𝔟
π̇ 𝔄 𝔅 = (𝓐 : 𝔄) → 𝔅 𝓐

infixl 20 π̇
syntax π̇ 𝔄 (λ 𝓐 → 𝔅𝓐) = 𝔅𝓐 ← 𝓐 ≔ 𝔄

π̇-hidden-quantifier-syntax = π̇
infixl 20 π̇-hidden-quantifier-syntax
syntax π̇-hidden-quantifier-syntax 𝔄 (λ _ → 𝔅𝓐) = 𝔅𝓐 ← 𝔄

π̂² : ∀ {𝔞} ℓ → Ø 𝔞 → Ø 𝔞 ∙̂ ↑̂ ℓ
π̂² ℓ 𝔄 = ℓ ←̂ 𝔄 ← 𝔄

_→̂²_ : ∀ {𝔞} → Ø 𝔞 → ∀ ℓ → Ø 𝔞 ∙̂ ↑̂ ℓ
_→̂²_ 𝔒 ℓ = π̂² ℓ 𝔒

∀̇ : ∀ {𝔵} {𝔛 : Ø 𝔵} {𝔞}
  → (∀ ℓ (𝔄 : Ø 𝔞) → Ø 𝔞 ∙̂ ↑̂ ℓ)
  → ∀ ℓ → (𝔛 → Ø 𝔞) → Ø 𝔵 ∙̂ 𝔞 ∙̂ ↑̂ ℓ
∀̇ Q ℓ 𝔄 = ∀ {x} → Q ℓ (𝔄 x)

Ṙelation : ∀ {𝔵} {𝔛 : Ø 𝔵} {𝔞} ℓ → (𝔞 ←̂ 𝔛) → Ø 𝔵 ∙̂ 𝔞 ∙̂ ↑̂ ℓ
Ṙelation = ∀̇ π̂²

Pointwise : ∀ {𝔞} {𝔄 : Ø 𝔞} {𝔟} {𝔅 : Ø 𝔟} {ℓ} → 𝔅 →̂² ℓ → (𝔅 ← 𝔄) → (𝔄 → 𝔅) → Ø 𝔞 ∙̂ ℓ
Pointwise _≈_ = λ f g → ∀ x → f x ≈ g x

Ṗroperty : ∀ {𝔵} {𝔛 : Ø 𝔵} {𝔬} ℓ → (𝔵 ∙̂ 𝔬 ∙̂ ↑̂ ℓ) ←̂ (𝔬 ←̂ 𝔛)
Ṗroperty = ∀̇ π̂

LeftṖroperty : ∀ {𝔵} {𝔛 : Ø 𝔵} {𝔶} {𝔜 : 𝔛 → Ø 𝔶} {𝔯} → ∀ ℓ → ((x : 𝔛) → 𝔜 x → Ø 𝔯) → 𝔛 → Ø 𝔶 ∙̂ 𝔯 ∙̂ ↑̂ ℓ
LeftṖroperty ℓ _↦_ = ∀̇ π̂ ℓ ∘ _↦_

ArrowṖroperty : ∀ {𝔵} {𝔛 : Ø 𝔵} {𝔭₁ 𝔭₂} → ∀ ℓ → (𝔛 → Ø 𝔭₁) → (𝔛 → Ø 𝔭₂) → 𝔛 → Ø 𝔵 ∙̂ 𝔭₁ ∙̂ 𝔭₂ ∙̂ ↑̂ ℓ
ArrowṖroperty ℓ 𝔒₁ 𝔒₂ = LeftṖroperty ℓ (Arrow 𝔒₁ 𝔒₂)

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

ExtensionṖroperty : ∀ {𝔵} {𝔛 : Ø 𝔵} {𝔬} {ℓ̇}
  ℓ (𝔒 : 𝔛 → Ø 𝔬) (_↦_ : ∀̇ π̂² ℓ̇ 𝔒)
  → Ø 𝔵 ∙̂ 𝔬 ∙̂ ↑̂ ℓ ∙̂ ℓ̇
ExtensionṖroperty ℓ 𝔒 _↦_ = Σ (∀̇ π̂ ℓ 𝔒) (λ P → ∀ {x} {f g : 𝔒 x} → f ↦ g → Extension P f g)

LeftExtensionṖroperty : ∀ {𝔶} {𝔜 : Ø 𝔶} {𝔵} {𝔛 : 𝔜 → Ø 𝔵} {𝔬} {ℓ̇}
  ℓ (𝔒 : (y : 𝔜) → 𝔛 y → Ø 𝔬) (_↦_ : ∀ {y} → ∀̇ π̂² ℓ̇ (𝔒 y))
  → 𝔜
  → Ø 𝔵 ∙̂ 𝔬 ∙̂ ↑̂ ℓ ∙̂ ℓ̇
LeftExtensionṖroperty ℓ 𝔒 _↦_ y = ExtensionṖroperty ℓ (𝔒 y) _↦_

ArrowExtensionṖroperty : ∀
  {𝔵} {𝔛 : Ø 𝔵}
  {𝔬₁} ℓ (𝔒₁ : 𝔛 → Ø 𝔬₁)
  {𝔬₂} (𝔒₂ : 𝔛 → Ø 𝔬₂)
  → ∀ {ℓ̇} (_↦_ : ∀̇ π̂² ℓ̇ 𝔒₂)
  → 𝔛
  → Ø 𝔵 ∙̂ 𝔬₁ ∙̂ 𝔬₂ ∙̂ ↑̂ ℓ ∙̂ ℓ̇
ArrowExtensionṖroperty ℓ 𝔒₁ 𝔒₂ _↦_ = LeftExtensionṖroperty ℓ (Arrow 𝔒₁ 𝔒₂) (Pointwise _↦_)
