
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
  {𝔞}
  {𝔟}
  (𝔄 : 𝔛 → Ø 𝔞)
  (𝔅 : 𝔛 → Ø 𝔟)
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
  → ∀ ℓ
      {𝔵} {𝔛 : Ø 𝔵}
      {𝔞} (𝔄 : 𝔛 → Ø 𝔞)
      → Ø 𝔵 ∙̂ 𝔞 ∙̂ ↑̂ ℓ
Dotter D ℓ 𝔄 = ∀ {x} → D (𝔄 x) ℓ

Ṙelation : ∀ ℓ
  {𝔵} {𝔛 : Ø 𝔵}
  {𝔞} (𝔄 : 𝔛 → Ø 𝔞)
  → Ø 𝔵 ∙̂ 𝔞 ∙̂ ↑̂ ℓ
Ṙelation = Dotter Relation

Extended : ∀
    {𝔞} {𝔄 : Ø 𝔞}
    {𝔟} {𝔅 : Ø 𝔟}
    {ℓ} (_≈_ : 𝔅 → 𝔅 → Ø ℓ)
    → (𝔄 → 𝔅) → (𝔄 → 𝔅)
    → Ø 𝔞 ∙̂ ℓ
Extended _≈_ = λ f g → ∀ x → f x ≈ g x

Ṗroperty :
  ∀ ℓ
  {𝔵} {𝔛 : Ø 𝔵}
  {𝔬} (𝔒 : Property 𝔛 𝔬)
  → Ø 𝔵 ∙̂ 𝔬 ∙̂ ↑̂ ℓ
Ṗroperty = Dotter Property

GIndexer : ∀
  {𝔵} {𝔛 : Ø 𝔵} {𝔬₁} {𝔬₂}
  (G : ∀
         (𝔛 : Ø 𝔵)
         ℓ
         → Ø 𝔵 ∙̂ ↑̂ ℓ)
  (I : ∀
    {𝔛 : Ø 𝔵}
    {𝔬} (𝔒 : G 𝔛 𝔬)
    ℓ
    → Ø 𝔵 ∙̂ 𝔬 ∙̂ ↑̂ ℓ)
  (F : ∀
    {𝔛 : Ø 𝔵}
    (𝔒₁ : 𝔛 → Ø 𝔬₁)
    (𝔒₂ : 𝔛 → Ø 𝔬₂)
    → 𝔛 → G 𝔛 (𝔬₁ ∙̂ 𝔬₂))
  (𝔒₁ : 𝔛 → Ø 𝔬₁)
  (𝔒₂ : 𝔛 → Ø 𝔬₂)
  ℓ
  → 𝔛
  → Ø 𝔵 ∙̂ 𝔬₁ ∙̂ 𝔬₂ ∙̂ ↑̂ ℓ
GIndexer _ I F 𝔒₁ 𝔒₂ ℓ x = I (F 𝔒₁ 𝔒₂ x) ℓ

IndexerṖroperty : ∀ {𝔵} {𝔛 : Ø 𝔵} {𝔬₁ 𝔬₂}
  (F : ∀
    (𝔒₁ : 𝔛 → Ø 𝔬₁)
    (𝔒₂ : 𝔛 → Ø 𝔬₂)
    → 𝔛 → 𝔛 → Ø 𝔬₁ ∙̂ 𝔬₂)
  (𝔒₁ : 𝔛 → Ø 𝔬₁)
  (𝔒₂ : 𝔛 → Ø 𝔬₂)
  ℓ
  → 𝔛
  → Ø 𝔵 ∙̂ 𝔬₁ ∙̂ 𝔬₂ ∙̂ ↑̂ ℓ
IndexerṖroperty F 𝔒₁ 𝔒₂ ℓ x = Ṗroperty ℓ (F 𝔒₁ 𝔒₂ x)
-- F 𝔒₁ 𝔒₂ ℓ x = Ṗroperty (F 𝔒₁ 𝔒₂ x) ℓ

IXR : ∀ {𝔵} {𝔛 : Ø 𝔵} {𝔬₁ 𝔬₂}
  (IX : (𝔛 → Set (𝔬₂ ∙̂ 𝔬₁)) → ∀ ℓ → Set ((↑̂ ℓ) ∙̂ (𝔬₂ ∙̂ (𝔬₁ ∙̂ 𝔵))))
  (F : ∀
    (𝔒₁ : 𝔛 → Ø 𝔬₁)
    (𝔒₂ : 𝔛 → Ø 𝔬₂)
    → 𝔛 → 𝔛 → Ø 𝔬₁ ∙̂ 𝔬₂)
  (𝔒₁ : 𝔛 → Ø 𝔬₁)
  (𝔒₂ : 𝔛 → Ø 𝔬₂)
  ℓ
  → 𝔛
  → Ø 𝔵 ∙̂ 𝔬₁ ∙̂ 𝔬₂ ∙̂ ↑̂ ℓ
IXR IX F 𝔒₁ 𝔒₂ ℓ x = IX (F 𝔒₁ 𝔒₂ x) ℓ

IXR' : ∀ {𝔵} {𝔛 : Ø 𝔵} {𝔬₁ 𝔬₂}
  {FOO : Set (𝔵 ∙̂ ↑̂ (𝔬₂ ∙̂ 𝔬₁))}
  (IX : FOO → ∀ ℓ → Set ((↑̂ ℓ) ∙̂ (𝔬₂ ∙̂ (𝔬₁ ∙̂ 𝔵))))
  (F : ∀
    (𝔒₁ : 𝔛 → Ø 𝔬₁)
    (𝔒₂ : 𝔛 → Ø 𝔬₂)
    → 𝔛 → FOO)
  (𝔒₁ : 𝔛 → Ø 𝔬₁)
  (𝔒₂ : 𝔛 → Ø 𝔬₂)
  ℓ
  → 𝔛
  → Ø 𝔵 ∙̂ 𝔬₁ ∙̂ 𝔬₂ ∙̂ ↑̂ ℓ
IXR' IX F 𝔒₁ 𝔒₂ ℓ x = IX (F 𝔒₁ 𝔒₂ x) ℓ

IXR'' : ∀ {𝔵} {𝔛 : Ø 𝔵} {𝔬₁ 𝔬₂}
  {FOO : Ø 𝔵 ∙̂ ↑̂ (𝔬₁ ∙̂ 𝔬₂)}
  {XO1 : Ø 𝔵 ∙̂ ↑̂ 𝔬₁}
  {XO2 : Ø 𝔵 ∙̂ ↑̂ 𝔬₂}
  (IX : FOO → ∀ ℓ → Ø 𝔵 ∙̂ 𝔬₁ ∙̂ 𝔬₂ ∙̂ ↑̂ ℓ)
  (F : XO1 → XO2 → 𝔛 → FOO)
  (𝔒₁ : XO1)
  (𝔒₂ : XO2)
  ℓ
  → 𝔛
  → Ø 𝔵 ∙̂ 𝔬₁ ∙̂ 𝔬₂ ∙̂ ↑̂ ℓ
IXR'' IX F 𝔒₁ 𝔒₂ ℓ x = IX (F 𝔒₁ 𝔒₂ x) ℓ

IXR''' : ∀ {𝔵} {𝔛 : Ø 𝔵} {𝔬₁ 𝔬₂}
  {FOO : Ø 𝔵 ∙̂ ↑̂ (𝔬₁ ∙̂ 𝔬₂)}
  {XO1 : Ø 𝔵 ∙̂ ↑̂ 𝔬₁}
  {XO2 : Ø 𝔵 ∙̂ ↑̂ 𝔬₂}
  (IX : FOO → ∀ ℓ → Ø 𝔵 ∙̂ 𝔬₁ ∙̂ 𝔬₂ ∙̂ ↑̂ ℓ)
  (F : XO1 → XO2 → 𝔛 → FOO)
  (𝔒₁ : XO1)
  (𝔒₂ : XO2)
  (ℓ : Ł)
  → 𝔛
  → Ø 𝔵 ∙̂ 𝔬₁ ∙̂ 𝔬₂ ∙̂ ↑̂ ℓ
IXR''' IX F 𝔒₁ 𝔒₂ ℓ x = IX (F 𝔒₁ 𝔒₂ x) ℓ

{-
_ : ∀ l1 l2 (A : Ø ↑̂ l1 ∙̂ l2) (B : Ø ↑̂ {!l1!} ∙̂ l2) (_≈_ : ∀ {l} {X Y : Ø l} → X → Y → Ø₀) → Set
_ = λ l1 l2 A B _≈_ → A ≈ B

_ : ∀ l1 (A : Ø ↑̂ l1) (B : Ø ↑̂ {!l1!}) (_≈_ : ∀ {l} {X Y : Ø l} → X → Y → Ø₀) → Set
_ = λ l1 A B _≈_ → A ≈ B
-}

IXR'''' : ∀ {𝔵} {𝔛 : Ø 𝔵} {𝔬₁ 𝔬₂}
  {FOO : Ø 𝔵 ∙̂ ↑̂ (𝔬₁ ∙̂ 𝔬₂)}
  {XO1 : Ø 𝔵 ∙̂ ↑̂ 𝔬₁}
  {XO2 : Ø 𝔵 ∙̂ ↑̂ 𝔬₂}
  (F : XO1 → XO2 → 𝔛 → FOO)
  (𝔒₁ : XO1)
  (𝔒₂ : XO2)
  (ℓ : Ł)
  (IX : FOO → Ø 𝔵 ∙̂ 𝔬₁ ∙̂ 𝔬₂ ∙̂ ↑̂ ℓ)
  → 𝔛
  → Ø 𝔵 ∙̂ 𝔬₁ ∙̂ 𝔬₂ ∙̂ ↑̂ ℓ
IXR'''' F 𝔒₁ 𝔒₂ ℓ IX x = IX (F 𝔒₁ 𝔒₂ x)

IXR5 : ∀ {𝔵} {𝔛 : Ø 𝔵} {𝔬₁ 𝔬₂}
  {FOO : Ø 𝔵 ∙̂ ↑̂ (𝔬₁ ∙̂ 𝔬₂)}
  {XO1 : Ø 𝔵 ∙̂ ↑̂ 𝔬₁}
  {XO2 : Ø 𝔵 ∙̂ ↑̂ 𝔬₂}
  (F : XO1 → XO2 → 𝔛 → FOO)
  (𝔒₁ : XO1)
  (𝔒₂ : XO2)
  (ℓ : Ł)
  (IX : FOO → Ø 𝔵 ∙̂ 𝔬₁ ∙̂ 𝔬₂ ∙̂ ↑̂ ℓ)
  → 𝔛
  → Ø 𝔵 ∙̂ 𝔬₁ ∙̂ 𝔬₂ ∙̂ ↑̂ ℓ
IXR5 F 𝔒₁ 𝔒₂ ℓ IX x = IX (F 𝔒₁ 𝔒₂ x)

IXR6 : ∀ {𝔵} {𝔛 : Ø 𝔵} {𝔬₁ 𝔬₂}
  {FOO : Ø 𝔵 ∙̂ ↑̂ (𝔬₁ ∙̂ 𝔬₂)}
  (F : 𝔛 → FOO)
  (ℓ : Ł)
  (IX : FOO → Ø 𝔵 ∙̂ 𝔬₁ ∙̂ 𝔬₂ ∙̂ ↑̂ ℓ)
  → 𝔛
  → Ø 𝔵 ∙̂ 𝔬₁ ∙̂ 𝔬₂ ∙̂ ↑̂ ℓ
IXR6 F𝔒₁𝔒₂ ℓ IX x = IX (F𝔒₁𝔒₂ x)

IXR7 : ∀ {𝔵} {𝔛 : Ø 𝔵} {𝔬₁𝔬₂}
  {FOO : Ø 𝔵 ∙̂ ↑̂ (𝔬₁𝔬₂)}
  (F : 𝔛 → FOO)
  (ℓ : Ł)
  (IX : FOO → Ø 𝔵 ∙̂ 𝔬₁𝔬₂ ∙̂ ↑̂ ℓ)
  → 𝔛
  → Ø 𝔵 ∙̂ 𝔬₁𝔬₂ ∙̂ ↑̂ ℓ
IXR7 F𝔒₁𝔒₂ ℓ IX x = IX (F𝔒₁𝔒₂ x)

IXR8 : ∀ {𝔵} {𝔛 : Ø 𝔵} {x+𝔬₁𝔬₂ x+𝔬₁𝔬₂+l}
  {FOO : Ø x+𝔬₁𝔬₂}
  (F : 𝔛 → FOO)
  (IX : FOO → Ø x+𝔬₁𝔬₂+l)
  → 𝔛
  → Ø x+𝔬₁𝔬₂+l
IXR8 F𝔒₁𝔒₂ IX x = IX (F𝔒₁𝔒₂ x)

ArrowsourceṖroperty : ∀ {𝔵} {𝔛 : Ø 𝔵} {𝔬₁} {𝔬₂} → (𝔛 → Ø 𝔬₁) → (𝔛 → Ø 𝔬₂) → ∀ ℓ → 𝔛 → Ø 𝔵 ∙̂ 𝔬₁ ∙̂ 𝔬₂ ∙̂ ↑̂ ℓ
ArrowsourceṖroperty O1 O2 ℓ x = IXR8 (Arrow O1 O2) (Dotter Property ℓ) x
--ArrowsourceṖroperty {𝔵} {𝔛} {𝔬₁} {𝔬₂} O1 O2 ℓ x = IXR8 (Arrow O1 O2) (Dotter Property ℓ) x
--ArrowsourceṖroperty {𝔵} {𝔛} {𝔬₁} {𝔬₂} O1 O2 ℓ x = IXR8 (Arrow O1 O2) (λ foo → Dotter Property foo ℓ) x
--ArrowsourceṖroperty {𝔵} {𝔛} {𝔬₁} {𝔬₂} O1 O2 ℓ x = IXR7 (Arrow O1 O2) ℓ (λ foo → Dotter Property foo _) x
--ArrowsourceṖroperty {𝔵} {𝔛} {𝔬₁} {𝔬₂} = IXR' (Dotter Property) Arrow
--ArrowsourceṖroperty {𝔵} {𝔛} {𝔬₁} {𝔬₂} = IXR'' {𝔬₁ = 𝔬₁} {𝔬₂ = 𝔬₂ ∙̂ {!𝔬₁!}} (Dotter Property) Arrow
--ArrowsourceṖroperty {𝔵} {𝔛} {𝔬₁} {𝔬₂} = IXR'' {𝔬₁ = 𝔬₁} {𝔬₂ = 𝔬₂} (Dotter Property) Arrow
--ArrowsourceṖroperty {𝔵} {𝔛} {𝔬₁} {𝔬₂} O1 O2 ℓ x = IXR''' (Dotter Property) Arrow O1 O2 ℓ x
--ArrowsourceṖroperty {𝔵} {𝔛} {𝔬₁} {𝔬₂} O1 O2 ℓ x = IXR'''' {𝔬₁ = 𝔬₁} {𝔬₂ = 𝔬₂} Arrow O1 O2 ℓ (λ foo → Dotter Property foo _) x
--ArrowsourceṖroperty {𝔵} {𝔛} {𝔬₁} {𝔬₂} O1 O2 ℓ x = IXR5 {𝔬₁ = 𝔬₁} {𝔬₂ = 𝔬₂} Arrow O1 O2 ℓ (λ foo → Dotter Property foo _) x
--ArrowsourceṖroperty {𝔵} {𝔛} {𝔬₁} {𝔬₂} O1 O2 ℓ x = IXR6 (Arrow O1 O2) ℓ (λ foo → Dotter Property foo _) x

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
  {ℓ̇} (_↦_ : Dotter Relation ℓ̇ 𝔒)
  → Ø 𝔵 ∙̂ 𝔬 ∙̂ ↑̂ ℓ ∙̂ ℓ̇
ExtendedṖroperty 𝔒 ℓ _↦_ = Σ (Dotter Property ℓ 𝔒) (λ P → ∀ {x} {f g : 𝔒 x} → f ↦ g → Extension P f g)
--ExtendedṖroperty 𝔒 ℓ _↦_ = Σ (Ṗroperty ℓ 𝔒) (λ P → ∀ {x} {f g : 𝔒 x} → f ↦ g → Extension P f g)

ArrowsourceExtendedṖroperty : ∀
  {𝔵} {𝔛 : Ø 𝔵}
  {𝔬₁} (𝔒₁ : 𝔛 → Ø 𝔬₁)
  {𝔬₂} (𝔒₂ : 𝔛 → Ø 𝔬₂)
  ℓ
  → (x : 𝔛)
--  → ∀ {ℓ̇} (_↦_ : ∀ {y} → Arrow 𝔒₁ 𝔒₂ x y → Arrow 𝔒₁ 𝔒₂ x y → Ø ℓ̇)
  → ∀ {ℓ̇} (_↦_ : Dotter Relation ℓ̇ (Arrow 𝔒₁ 𝔒₂ x))
  → Ø 𝔵 ∙̂ 𝔬₁ ∙̂ 𝔬₂ ∙̂ ↑̂ ℓ ∙̂ ℓ̇
ArrowsourceExtendedṖroperty 𝔒₁ 𝔒₂ ℓ x _↦_ = ExtendedṖroperty (Arrow 𝔒₁ 𝔒₂ x) ℓ _↦_
