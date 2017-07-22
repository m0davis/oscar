{-# OPTIONS --show-implicit #-}
{-# OPTIONS --postfix-projections #-}
{-# OPTIONS --rewriting #-}
module Oscar.Class where

open import Oscar.Prelude
open import Oscar.Data using (_≡_; Proposequality; ∅)
open import Oscar.Class.Reflexivity public
open import Oscar.Class.Transitivity public
open import Oscar.Class.Congruity public
open import Oscar.Class.Symmetrical public
open import Oscar.Class.Symmetry public
open import Oscar.Class.IsEquivalence public
open import Oscar.Class.Setoid public
open import Oscar.Class.Transextensionality public
open import Oscar.Class.Transassociativity public
open import Oscar.Class.IsPrecategory public
open import Oscar.Class.Precategory public
open import Oscar.Class.Surjection public
open import Oscar.Class.Surjectextensivity public
open import Oscar.Class.Surjectivity public
open import Oscar.Class.Surjectextensivity.SurjectivityExtension public
open import Oscar.Class.Surjtranscommutativity public
open import Oscar.Class.Surjextensionality public
open import Oscar.Class.IsPrefunctor public
open import Oscar.Class.Prefunctor public
open import Oscar.Class.Transleftidentity public
open import Oscar.Class.Transrightidentity public
open import Oscar.Class.IsCategory public
open import Oscar.Class.Category public
open import Oscar.Class.Surjidentity public
open import Oscar.Class.IsFunctor public
open import Oscar.Class.Functor public
open import Oscar.Class.Injectivity public
open import Oscar.Class.Successor₀ public
open import Oscar.Class.Successor₁ public
open import Oscar.Class.Map public
open import Oscar.Class.Fmap public
open import Oscar.Class.Apply public

module _ where

  module _
    {𝔬 𝔣}
    (𝔉 : Ø 𝔬 → Ø 𝔣)
    where
    𝓹ure = ∀ {𝔒 : Ø 𝔬} → 𝔒 → 𝔉 𝔒
    record 𝓟ure : Ø 𝔣 ∙̂ ↑̂ 𝔬 where
      field pure : 𝓹ure
  open 𝓟ure ⦃ … ⦄ public

  module _
    (𝔉 : ∀ {𝔣} → Ø 𝔣 → Ø 𝔣)
    𝔬₁ 𝔬₂
    where
    𝓫ind = ∀ {𝔒₁ : Ø 𝔬₁} {𝔒₂ : Ø 𝔬₂} → 𝔉 𝔒₁ → (𝔒₁ → 𝔉 𝔒₂) → 𝔉 𝔒₂
    record 𝓑ind : Ø ↑̂ (𝔬₁ ∙̂ 𝔬₂) where
      infixl 6 bind
      field bind : 𝓫ind
      syntax bind m f = f =<< m
    open 𝓑ind ⦃ … ⦄ public

  module _
    {x} {X : Ø x} {a} (A : X → Ø a) {b} (B : X → Ø b)
    where
    record [𝓣hin] : Ø₀ where
      no-eta-equality
      constructor ∁
    module _
      ⦃ _ : 𝓢uccessor₀ X ⦄
      where
      𝔱hin : ∀ (m : X) → A (⇑₀ m) → B m → Ø b
      𝔱hin m = λ _ _ → B (⇑₀ m)
      𝓽hin = ∀ {m : X} → A (⇑₀ m) → B m → B (⇑₀ m)
      record 𝓣hin ⦃ _ : [𝓣hin] ⦄ : Ø x ∙̂ a ∙̂ b where
        field
          thin : 𝓽hin
        instance `𝓘njection₂ : ∀ {m} → 𝓘njection₂ (𝔱hin m)
        `𝓘njection₂ = ∁ thin
  open 𝓣hin ⦃ … ⦄ public

  module _
    {x} {X : Ø x} {a} (A : X → Ø a) {b} (B : X → Ø b)
    where
    record [𝓣hick] : Ø₀ where
      no-eta-equality
      constructor ∁
    module _
      ⦃ _ : 𝓢uccessor₀ X ⦄
      where
      𝓽hick = ∀ {m} → A m → B (⇑₀ m) → B m
      record 𝓣hick ⦃ _ : [𝓣hick] ⦄ : Ø x ∙̂ a ∙̂ b where field thick : 𝓽hick
  open 𝓣hick ⦃ … ⦄ public

  module _
    {x} {X : Ø x}
    {a} (A : X → Ø a)
    {b} (B : X → Ø b)
    {ℓ} (_≈_ : ∀ {x} → B x → B x → Ø ℓ)
    where
    record [𝓣hick/thin=1] : Ø₀ where
      no-eta-equality
      constructor ∁
    module _
      ⦃ _ : 𝓢uccessor₀ X ⦄
      ⦃ _ : [𝓢uccessor₁] A ⦄
      ⦃ _ : 𝓢uccessor₁ A ⦄
      ⦃ _ : [𝓣hin] A B ⦄
      ⦃ _ : 𝓣hin A B ⦄
      ⦃ _ : [𝓣hick] A B ⦄
      ⦃ _ : 𝓣hick A B ⦄
      where
      𝓽hick/thin=1 = ∀ {m} (x : A m) (y : B m) → thick x (thin (⇑₁ x) y) ≈ y
      record 𝓣hick/thin=1 : Ø x ∙̂ a ∙̂ b ∙̂ ℓ where field thick/thin=1 : 𝓽hick/thin=1
  open 𝓣hick/thin=1 ⦃ … ⦄ public

  module _
    {x} {X : Ø x}
    {a} (A : X → Ø a)
    {b} (B : X → Ø b)
    {c} (C : Ø b → Ø c)
    where
    record [𝓒heck] : Ø₀ where
      no-eta-equality
      constructor ∁
    module _
      ⦃ _ : 𝓢uccessor₀ X ⦄
      where
      𝓬heck = ∀ {m} → A (⇑₀ m) → B (⇑₀ m) → C (B m)
      record 𝓒heck ⦃ _ : [𝓒heck] ⦄ : Ø x ∙̂ a ∙̂ b ∙̂ c where field check : 𝓬heck
  open 𝓒heck ⦃ … ⦄ public

  check[_] : ∀
    {x} {X : Ø x}
    {a} {A : X → Ø a}
    {b} {B : X → Ø b}
    {c} (C : Ø b → Ø c)
    ⦃ _ : [𝓒heck] A B C ⦄
    ⦃ _ : 𝓢uccessor₀ X ⦄
    ⦃ _ : 𝓒heck A B C ⦄
    → 𝓬heck A B C
  check[ _ ] = check

  module _
    {x} {X : Ø x}
    {a} (A : X → Ø a)
    {b} (B : X → Ø b)
    {c} (C : Ø b → Ø c)
    {ℓ} (_≈_ : ∀ {x} → C (B x) → C (B x) → Ø ℓ)
    where
    record [𝓒heck/thin=1] : Ø₀ where
      no-eta-equality
      constructor ∁
    module _
      ⦃ _ : 𝓢uccessor₀ X ⦄
      ⦃ _ : [𝓣hin] A B ⦄
      ⦃ _ : 𝓣hin A B ⦄
      ⦃ _ : [𝓒heck] A B C ⦄
      ⦃ _ : 𝓒heck A B C ⦄
      ⦃ _ : 𝓟ure C ⦄
      where
      𝓬heck/thin=1 = ∀ {n} (x : A (⇑₀ n)) (y : B n) → check x (thin x y) ≈ pure y
      record 𝓒heck/thin=1 ⦃ _ : [𝓒heck/thin=1] ⦄ : Ø x ∙̂ a ∙̂ b ∙̂ c ∙̂ ℓ where field check/thin=1 : 𝓬heck/thin=1
  open 𝓒heck/thin=1 ⦃ … ⦄ public

  check/thin=1[_] : ∀
    {x} {X : Ø x}
    {a} {A : X → Ø a}
    {b} {B : X → Ø b}
    {c} {C : Ø b → Ø c}
    {ℓ} (_≈_ : ∀ {x} → C (B x) → C (B x) → Ø ℓ)
    ⦃ _ : 𝓢uccessor₀ X ⦄
    ⦃ _ : [𝓣hin] A B ⦄
    ⦃ _ : 𝓣hin A B ⦄
    ⦃ _ : [𝓒heck] A B C ⦄
    ⦃ _ : 𝓒heck A B C ⦄
    ⦃ _ : 𝓟ure C ⦄
    ⦃ _ : [𝓒heck/thin=1] A B C _≈_ ⦄
    ⦃ _ : 𝓒heck/thin=1 A B C _≈_ ⦄
    → 𝓬heck/thin=1 A B C _≈_
  check/thin=1[ _ ] = check/thin=1

  record IsThickandthin
    {x a b c ℓb ℓc}
    {X : Ø x}
    (A : X → Ø a)
    (B : X → Ø b)
    (_≈B_ : ∀ {x} → B x → B x → Ø ℓb)
    (C : Ø b → Ø c)
    (_≈C_ : ∀ {x} → C (B x) → C (B x) → Ø ℓc)
    : Ø x ∙̂ a ∙̂ ↑̂ b ∙̂ ℓb ∙̂ c ∙̂ ℓc where
    constructor ∁
    field
      overlap ⦃ `𝓢uccessor₀ ⦄ : 𝓢uccessor₀ X
      overlap ⦃ `[𝓢uccessor₁] ⦄ : [𝓢uccessor₁] A
      overlap ⦃ `𝓢uccessor₁ ⦄ : 𝓢uccessor₁ A
      overlap ⦃ `[𝓣hick] ⦄ : [𝓣hick] A B
      overlap ⦃ `𝓣hick ⦄ : 𝓣hick A B
      overlap ⦃ `[𝓣hin] ⦄ : [𝓣hin] A B
      overlap ⦃ `𝓣hin ⦄ : 𝓣hin A B
      overlap ⦃ `[𝓘njectivity₂,₁] ⦄ : ∀ {m} → [𝓘njectivity₂,₁] (𝔱hin A B m) _≈B_ _≈B_
      overlap ⦃ `𝓘njectivity₂,₁ ⦄   : ∀ {m} → 𝓘njectivity₂,₁ (𝔱hin A B m) _≈B_ _≈B_
      overlap ⦃ `[𝓒heck] ⦄ : [𝓒heck] A B C
      overlap ⦃ `𝓒heck ⦄ : 𝓒heck A B C
      overlap ⦃ `[𝓣hick/thin=1] ⦄ : [𝓣hick/thin=1] A B _≈B_
      overlap ⦃ `𝓣hick/thin=1 ⦄ : 𝓣hick/thin=1 A B _≈B_
      overlap ⦃ `[𝓒heck/thin=1] ⦄ : [𝓒heck/thin=1] A B C _≈C_
      overlap ⦃ `𝓟ure ⦄ : 𝓟ure C
      overlap ⦃ `𝓒heck/thin=1 ⦄ : 𝓒heck/thin=1 A B C _≈C_

  record Thickandthin x a b ℓb c ℓc : Ø ↑̂ (x ∙̂ a ∙̂ b ∙̂ ℓb ∙̂ c ∙̂ ℓc) where
    constructor ∁
    field
      {X} : Ø x
      A : X → Ø a
      B : X → Ø b
      _≈B_ : ∀ {x} → B x → B x → Ø ℓb
      C : Ø b → Ø c
      _≈C_ : ∀ {x} → C (B x) → C (B x) → Ø ℓc
      ⦃ `IsThickandthin ⦄ : IsThickandthin A B _≈B_ C _≈C_

  module Test-Thickandthin {x a b ℓb c ℓc} ⦃ _ : Thickandthin x a b ℓb c ℓc ⦄ where
    open Thickandthin ⦃ … ⦄

    test-thin : 𝓽hin A B
    test-thin = thin

    test-check/thin=1 : 𝓬heck/thin=1 A B C _≈C_
    test-check/thin=1 = check/thin=1

    test-injectivity : ∀ {m : X} {x : A (⇑₀ m)} → 𝓶ap (_≈B_ on thin x) _≈B_
    test-injectivity {x = x} = injectivity₂,₁ x

module _ where

  record HasEquivalence {𝔬} (𝔒 : Ø 𝔬) ℓ : Ø 𝔬 ∙̂ ↑̂ ℓ where
    constructor ∁

    field
      Equivalence : 𝔒 → 𝔒 → Ø ℓ
      ⦃ ⌶IsEquivalence ⦄ : IsEquivalence Equivalence
    infix 4 Equivalence

  open HasEquivalence ⦃ … ⦄ public
  open HasEquivalence ⦃ … ⦄ public using () renaming (Equivalence to _≈_)

  module _ where

    infix 4 ≈-syntax
    ≈-syntax : ∀ {𝔬} (𝔒 : Ø 𝔬) {ℓ} ⦃ _ : HasEquivalence 𝔒 ℓ ⦄ → 𝔒 → 𝔒 → Ø ℓ
    ≈-syntax _ = _≈_
    syntax ≈-syntax 𝔒 x y = x ≈[ 𝔒 ] y

module _ where

  open import Oscar.Data

  record IsDecidable {𝔬} (𝔒 : Ø 𝔬) : Ø 𝔬 where
    infix 4 _≟_
    field
      _≟_ : (x y : 𝔒) → Decidable (x ≡ y)

  open IsDecidable ⦃ … ⦄ public

module _ where

  record Properthing {𝔬} ℓ (𝔒 : Ø 𝔬) : Ø 𝔬 ∙̂ ↑̂ ℓ where
    infixr 15 _∧_
    field
      ➊ : 𝔒
      _∧_ : 𝔒 → 𝔒 → 𝔒
      ⦃ ⌶HasEquivalence ⦄ : HasEquivalence 𝔒 ℓ
      Nothing : 𝔒 → Ø ℓ
      fact2 : ∀ {P Q} → P ≈ Q → Nothing P → Nothing Q
      ∧-leftIdentity : ∀ P → ➊ ∧ P ≈ P

  open Properthing ⦃ … ⦄ public

module _ where

  record Exotransitivity
    {𝔵} {𝔛 : Ø 𝔵}
    {𝔞} (𝔄 : 𝔛 → Ø 𝔞)
    {𝔟} (𝔅 : 𝔛 → 𝔛 → Ø 𝔟)
    : Ø 𝔵 ∙̂ 𝔞 ∙̂ 𝔟
    where
    field
      exotransitivity : ∀ {x y} → 𝔅 x y → 𝔄 x → 𝔄 y

module _ where

  module _
    {𝔵} {𝔛 : Ø 𝔵}
    {𝔞} (𝔄 : 𝔛 → Ø 𝔞)
    {𝔟} (𝔅 : 𝔛 → Ø 𝔟)
    (let _∼_ = Arrow 𝔄 𝔅) (let infix 4 _∼_ ; _∼_ = _∼_)
    {ℓ̇} (_∼̇_ : ∀ {x y} → x ∼ y → x ∼ y → Ø ℓ̇)
    ⦃ _ : 𝓣ransitivity _∼_ ⦄
    ⦃ _ : 𝓡eflexivity _∼_ ⦄
    ℓ
    where
    𝓹rop-id = ∀ {m n} {f : m ∼ n} (P : LeftExtensionṖroperty ℓ _∼_ _∼̇_ m)
              (let P₀ = π₀ (π₀ P)) → P₀ f → P₀ (ε ∙ f)
    record PropId : Ø 𝔵 ∙̂ 𝔞 ∙̂ 𝔟 ∙̂ ℓ̇ ∙̂ ↑̂ ℓ where field prop-id : 𝓹rop-id

  open PropId ⦃ … ⦄ public

module _ where

  record Amgu {𝔵} {X : Ø 𝔵} {𝔱} (T : X → Ø 𝔱) {𝔞} (A : X → Ø 𝔞) {𝔪} (M : Ø 𝔞 → Ø 𝔪) : Ø 𝔵 ∙̂ 𝔱 ∙̂ 𝔞 ∙̂ 𝔪 where
    field amgu : ∀ {x} → T x → T x → A x → M (A x)

  open Amgu ⦃ … ⦄ public

module _ where

  record [IsExtensionB]
    {a} {A : Ø a}
    {b} (B : A → Ø b)
    : Ø₀ where
    constructor ∁
    no-eta-equality

module _ where

  record [ExtensibleType]
      {𝔵} {𝔛 : Ø 𝔵}
      {𝔟} {𝔒₂ : 𝔛 → Ø 𝔟}
      {ℓ̇} (_↦_ : ∀ {x} → 𝔒₂ x → 𝔒₂ x → Ø ℓ̇)
      : Ø₀ where
    constructor ∁
    no-eta-equality

module _ where

  record [𝓢urjectextenscongruity]
    {𝔬} {𝔒 : Ø 𝔬}
    {𝔯} (_∼ᵣ_ : π̂² 𝔯 𝔒)
    {𝔭} (𝔓 : π̂ 𝔭 𝔒)
    {ℓ} (_∼ₚ_ : ∀̇ π̂² ℓ 𝔓)
    : Ø₀ where
    no-eta-equality
    constructor ∁

  record 𝓢urjectextenscongruity
    {𝔬} {𝔒 : Ø 𝔬}
    {𝔯} (_∼ᵣ_ : π̂² 𝔯 𝔒)
    {𝔭} (𝔓 : π̂ 𝔭 𝔒)
    {ℓ} (_∼ₚ_ : ∀̇ π̂² ℓ 𝔓)
    ⦃ _ : [𝓢urjectextenscongruity] _∼ᵣ_ 𝔓 _∼ₚ_ ⦄
    ⦃ _ : 𝓢urjectextensivity _∼ᵣ_ 𝔓 ⦄
    : Ø 𝔬 ∙̂ 𝔭 ∙̂ 𝔯 ∙̂ ℓ where
    field
      surjectextenscongruity : ∀
        {m n} {P Q : 𝔓 m} (f : m ∼ᵣ n) → P ∼ₚ Q → (f ◃ P) ∼ₚ (f ◃ Q)

  open 𝓢urjectextenscongruity ⦃ … ⦄ public

module _ where

  Refl4 : ∀ {𝔞} ℓ → Ø 𝔞 → Ø 𝔞 ∙̂ ↑̂ ℓ
  Refl4 ℓ 𝔄 = 𝔄 → 𝔄 → 𝔄 → 𝔄 → Ø ℓ

  𝓅roperfact1 : ∀ {𝔞} {𝔄 : Ø 𝔞} {ℓ} → Refl4 ℓ 𝔄 → Ø 𝔞 ∙̂ ℓ
  𝓅roperfact1 refl4 = ∀ s1 s2 t1 t2 → refl4 s1 s2 t1 t2

  [𝓹roperfact1] : ∀ {𝔞} {𝔄 : Ø 𝔞} {𝔟} {𝔅 : Ø 𝔟} {ℓ} ⦃ _ : Properthing ℓ 𝔅 ⦄ (_∼_ : 𝔄 → 𝔄 → 𝔅) (_⊛_ : 𝔄 → 𝔄 → 𝔄) → Refl4 ℓ 𝔄
  [𝓹roperfact1] _∼_ _⊛_ s1 s2 t1 t2 = let _∼_ = _∼_ ; infix 18 _∼_ in
    s1 ⊛ s2 ∼ t1 ⊛ t2 ≈ s1 ∼ t1 ∧ s2 ∼ t2

  module _
    {𝔞} {𝔄 : Ø 𝔞} ℓ (refl4 : Refl4 ℓ 𝔄)
    where
    record [𝒫roperfact1] 𝔟 : Ø 𝔞 ∙̂ ↑̂ 𝔟 ∙̂ ↑̂ ℓ where
      constructor ∁
      infix 18 _∼_
      field
        𝔅 : Ø 𝔟
        _∼_ : 𝔄 → 𝔄 → 𝔅
        ⦃ ⌶Properthing ⦄ : Properthing ℓ 𝔅
        _⊛_ : 𝔄 → 𝔄 → 𝔄
        ⦃ ⌶CorrectProp ⦄ : [𝓹roperfact1] _∼_ _⊛_ ≡ refl4

    record 𝒫roperfact1 {𝔟} ⦃ _ : [𝒫roperfact1] 𝔟 ⦄ : Ø 𝔞 ∙̂ ℓ where
      field properfact1 : 𝓅roperfact1 refl4

  open 𝒫roperfact1 ⦃ … ⦄ public

  module _
    {𝔞} {𝔄 : Ø 𝔞} {𝔟} {𝔅 : Ø 𝔟} (_∼_ : 𝔄 → 𝔄 → 𝔅) {ℓ} ⦃ _ : Properthing ℓ 𝔅 ⦄ (_⊛_ : 𝔄 → 𝔄 → 𝔄)
    where
    𝓹roperfact1 = 𝓅roperfact1 ([𝓹roperfact1] _∼_ _⊛_)
    [𝓟roperfact1] = [𝒫roperfact1] _ ([𝓹roperfact1] _∼_ _⊛_) 𝔟
    𝓟roperfact1 = 𝒫roperfact1 _ ([𝓹roperfact1] _∼_ _⊛_)

module _ where

  TYPE : ∀ {𝔞} {𝔄 : Ø 𝔞} {𝔟} ℓ → (𝔄 → Ø 𝔟) → Ø 𝔞 ∙̂ 𝔟 ∙̂ ↑̂ ℓ
  TYPE ℓ 𝔅 = ∀ {a} (B : 𝔅 a) → Ø ℓ

  𝒻actsurj3 : ∀ {𝔞} {𝔄 : Ø 𝔞} {𝔟} {𝔅 : 𝔄 → Ø 𝔟} {ℓ} → TYPE ℓ 𝔅 → Ø 𝔞 ∙̂ 𝔟 ∙̂ ℓ
  𝒻actsurj3 {𝔅 = B} C = ∀ {a} {b : B a} → C b

  [𝓯actsurj3] : ∀ {𝔞} {𝔄 : Ø 𝔞} {𝔯} {𝔟} {ℓ} (_∼ᵣ_ : π̂² 𝔯 𝔄) (B : π̂ 𝔟 𝔄) ⦃ _ : 𝓡eflexivity _∼ᵣ_ ⦄ ⦃ _ : 𝓢urjectextensivity _∼ᵣ_ B ⦄ ⦃ _ : ∀ {x} → HasEquivalence (B x) ℓ ⦄ → TYPE ℓ B
  [𝓯actsurj3] _∼ᵣ_ 𝔅 B = B ≈ ε[ _∼ᵣ_ ] ◃ B

  module _
    {ℓ} {𝔞} {𝔄 : Ø 𝔞} {𝔟} {𝔅 : 𝔄 → Ø 𝔟}
    (type : TYPE ℓ 𝔅)
    where
    record [𝐹actsurj3] 𝔯 : Ø 𝔞 ∙̂ 𝔟 ∙̂ ↑̂ 𝔯 ∙̂ ↑̂ ℓ where
      constructor ∁
      field
        _∼ᵣ_ : π̂² 𝔯 𝔄
        ⦃ ⌶Reflexivity ⦄ : 𝓡eflexivity _∼ᵣ_
        ⦃ ⌶Surjectextensivity ⦄ : 𝓢urjectextensivity _∼ᵣ_ 𝔅
        ⦃ ⌶HasEquivalence ⦄ : ∀ {x} → HasEquivalence (𝔅 x) ℓ
        ⦃ ⌶CorrectFactsurj3 ⦄ : (λ {a} → [𝓯actsurj3] _∼ᵣ_ 𝔅 {a}) ≡ type

    record 𝐹actsurj3 {𝔯} ⦃ _ : [𝐹actsurj3] 𝔯 ⦄ : Ø 𝔞 ∙̂ 𝔟 ∙̂ ℓ where
      field factsurj3 : 𝒻actsurj3 (λ {x} → type {x})

  open 𝐹actsurj3 ⦃ … ⦄ public

  module _
    {ℓ} {𝔞} {𝔄 : Ø 𝔞} {𝔟} (𝔅 : 𝔄 → Ø 𝔟)
    {𝔯} (_∼ᵣ_ : π̂² 𝔯 𝔄)
    ⦃ _ : 𝓡eflexivity _∼ᵣ_ ⦄
    ⦃ _ : 𝓢urjectextensivity _∼ᵣ_ 𝔅 ⦄
    ⦃ _ : ∀ {x} → HasEquivalence (𝔅 x) ℓ ⦄
    where
    𝓯actsurj3 = 𝒻actsurj3 (λ {x} → [𝓯actsurj3] _∼ᵣ_ 𝔅 {x})
    [𝓕actsurj3] = [𝐹actsurj3] (λ {x} → [𝓯actsurj3] _∼ᵣ_ 𝔅 {x})
    𝓕actsurj3 = 𝐹actsurj3 (λ {x} → [𝓯actsurj3] _∼ᵣ_ 𝔅 {x})

module _ where

  module _
    {𝔞} {𝔄 : Ø 𝔞}
    {𝔟} (𝔅 : 𝔄 → Ø 𝔟)
    {𝔠} (ℭ : 𝔄 → 𝔄 → Ø 𝔠)
    where
    𝓯actsurj4-act = ∀ {a₁ a₂} → ℭ a₁ a₂ → 𝔅 a₁ → 𝔅 a₂
    module _
      {𝔡} (𝔇 : ∀ {a} → 𝔅 a → Ø 𝔡)
      where
      record [𝓕actsurj4] : Ø 𝔞 ∙̂ 𝔠 ∙̂ 𝔟 where
        constructor ∁
        field
          act : 𝓯actsurj4-act
      module _
        (act : 𝓯actsurj4-act)
        where
        𝓯actsurj4 = ∀ {a₁ a₂} {b : 𝔅 a₁} (c : ℭ a₁ a₂) → 𝔇 b → 𝔇 (act c b)
      module _
        ⦃ ⌶[𝓕actsurj4] : [𝓕actsurj4] ⦄
        where
        open [𝓕actsurj4] ⌶[𝓕actsurj4]
        record 𝓕actsurj4 : Ø 𝔞 ∙̂ 𝔟 ∙̂ 𝔠 ∙̂ 𝔡 where
          field factsurj4 : 𝓯actsurj4 act

  open 𝓕actsurj4 ⦃ … ⦄ public

module _ where

  module _
    {𝔬} {𝔒 : Ø 𝔬}
    {𝔭} (𝔓 : 𝔒 → Ø 𝔭)
    {𝔯} (_∼_ : 𝔒 → 𝔒 → Ø 𝔯)
    {ℓ∼} (_≈̈_ : ∀ {x y} → x ∼ y → x ∼ y → Ø ℓ∼) (let _≈̈_ = _≈̈_ ; infix 4 _≈̈_)
    {ℓ𝔭} (_≈̇_ : ∀ {x} → 𝔓 x → 𝔓 x → Ø ℓ𝔭) (let _≈̇_ = _≈̇_ ; infix 4 _≈̇_)
    where
    record [𝓕actsurj6] : Ø₀ where
      no-eta-equality
      constructor ∁
    module _
      ⦃ _ : 𝓢urjectextensivity _∼_ 𝔓 ⦄
      where
      record 𝓕actsurj6 ⦃ _ : [𝓕actsurj6] ⦄ : Ø 𝔬 ∙̂ 𝔭 ∙̂ 𝔯 ∙̂ ℓ∼ ∙̂ ℓ𝔭 where
        field factsurj6 : ∀ {m n} {f g : m ∼ n} (P : 𝔓 m) → f ≈̈ g → f ◃ P ≈̇ g ◃ P

  open 𝓕actsurj6 ⦃ … ⦄ public

open import Oscar.Data

instance

  [ExtensibleType]Proposequality : ∀ {a} {b} {A : Set a} {B : A → Set b} → [ExtensibleType] (λ {w} → Proposequality⟦ B w ⟧)
  [ExtensibleType]Proposequality = ∁

  [𝓢urjectivity]ArrowE : ∀ {ℓ} {a} {f} {t} {¶ : Set a} {Fin : ¶ → Set f} {Term : ¶ → Set t} → [𝓢urjectivity] (Arrow Fin Term) (Extension $ LeftExtensionṖroperty ℓ (Arrow Fin Term) _≡̇_)
  [𝓢urjectivity]ArrowE = ∁

  [𝓢urjectivity]LeftṖroperty : ∀ {ℓ} {a} {f} {¶ : Set a} {_↦_ : ¶ → ¶ → Set f} → [𝓢urjectivity] _↦_ (Extension $ LeftṖroperty ℓ _↦_)
  [𝓢urjectivity]LeftṖroperty = ∁

instance

  𝓢ymmetrical𝓢ymmetry : ∀
    {𝔬} {𝔒 : Ø 𝔬}
    {ℓ} {_∼_ : 𝔒 → 𝔒 → Ø ℓ}
    ⦃ _ : 𝓢ymmetry _∼_ ⦄
    → 𝓢ymmetrical 𝔒 (λ s t t' s' → s ∼ t → t' ∼ s')
  𝓢ymmetrical𝓢ymmetry .𝓢ymmetrical.symmetrical x y = symmetry

module _
  {𝔬} {𝔒 : Ø 𝔬}
  where
  instance
    𝓢urjectionIdentity : 𝓢urjection 𝔒 𝔒
    𝓢urjectionIdentity .𝓢urjection.surjection = ¡

instance

  ExtensionṖropertySurjectivity : ∀
    {𝔵} {𝔛 : Ø 𝔵}
    {𝔞} {𝔒₁ : 𝔛 → Ø 𝔞}
    {𝔟} {𝔒₂ : 𝔛 → Ø 𝔟}
    (let _∼_ = Arrow 𝔒₁ 𝔒₂)
    {ℓ}
    {ℓ̇} {_↦_ : ∀̇ π̂² ℓ̇ 𝔒₂}
    ⦃ _ : [ExtensibleType] (λ {x} → _↦_ {x}) ⦄
    ⦃ _ : [𝓢urjectivity] _∼_ (Extension 𝔒₂) ⦄
    ⦃ _ : 𝓢urjectivity _∼_ (Extension 𝔒₂) ⦄
    ⦃ _ : [𝓢urjextensionality] _∼_ (Pointwise _↦_) (Extension 𝔒₂) (Pointwise _↦_) ⦄
    ⦃ _ : 𝓢urjextensionality _∼_ (Pointwise _↦_) (Extension 𝔒₂) (Pointwise _↦_) ⦄
    ⦃ _ : [𝓢urjectivity] _∼_ (Extension $ LeftExtensionṖroperty ℓ _∼_ (Pointwise _↦_)) ⦄
    → 𝓢urjectivity _∼_ (Extension $ LeftExtensionṖroperty ℓ _∼_ (Pointwise _↦_))
  ExtensionṖropertySurjectivity .𝓢urjectivity.surjectivity f P = ∁ (λ g → π₀ (π₀ P) (surjectivity g ∘ f)) , (λ f≐g Pf'◇f → π₁ P (surjextensionality f≐g ∘ f) Pf'◇f)
