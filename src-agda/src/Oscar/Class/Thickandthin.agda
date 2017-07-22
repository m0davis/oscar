
open import Oscar.Prelude
open import Oscar.Class.Successor₀
open import Oscar.Class.Successor₁
open import Oscar.Class.Injectivity
open import Oscar.Class.Pure

module Oscar.Class.Thickandthin where

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
