
module Oscar where

open import Oscar.Prelude

module _ where

  record Reflexivity
    {a} {A : Ø a}
    {b} (_⊸_ : A → A → Ø b)
    : Ø a ∙̂ b where
    field reflexivity : ∀ {x} → x ⊸ x

  open Reflexivity ⦃ … ⦄ public

module _ where

  record Symmetry
    {a} {A : Ø a}
    {b} (_⊸_ : A → A → Ø b)
    : Ø a ∙̂ b where
    field symmetry : ∀ {x y} → x ⊸ y → y ⊸ x

  open Symmetry ⦃ … ⦄ public

module _ where

  record Transitivity
    {a} {A : Ø a}
    {b} (_⊸_ : A → A → Ø b)
    : Ø a ∙̂ b where
    field transitivity : ∀ {x y z} → x ⊸ y → y ⊸ z → x ⊸ z

  open Transitivity ⦃ … ⦄ public

module _ where

  record IsEquality
    {a} {A : Ø a}
    {b} (⊸ : A → A → Ø b)
    : Ø a ∙̂ b where
    field
      instance ⦃ ⌶Reflexivity ⦄ : Reflexivity ⊸
      instance ⦃ ⌶Symmetry ⦄ : Symmetry ⊸
      instance ⦃ ⌶Transitivity ⦄ : Transitivity ⊸

open import Oscar.Data

record Equality {a} (A : Set a) ℓ : Ø a ∙̂ ↑̂ ℓ where
  infix 4 _≋_
  field
    _≋_ : A → A → Ø ℓ
    ⦃ ⌶IsEquality ⦄ : IsEquality _≋_

open Equality ⦃ … ⦄ public using (_≋_)

record QuasiEquality {a} (A : Set a) ℓ {ℓ'} ⦃ _ : Equality A ℓ' ⦄ : Ø a ∙̂ ↑̂ ℓ ∙̂ ℓ' where
  infix 4 _≈_
  field
    _≈_ : A → A → Ø ℓ
    ⦃ ⌶IsEquality ⦄ : IsEquality _≈_
--    ⦃ ⌶EqualityProp ⦄ : Equality A ℓ'
    extensionFromEquality : ∀ {x y} → x ≋ y → x ≈ y

open QuasiEquality ⦃ … ⦄ public using (_≈_)

instance PropositionalEquality : ∀ {a} {A : Ø a} → Equality A ∅̂
Equality._≋_ PropositionalEquality = _≡_
Equality.⌶IsEquality PropositionalEquality = {!!}

instance ExtensionalEquality : ∀ {a} {A : Ø a} {b} {B : A → Ø b} → Equality ((x : A) → B x) _
Equality._≋_ ExtensionalEquality = _≡̇_
Equality.⌶IsEquality ExtensionalEquality = {!!}

postulate
  A : Set
  B : A → Set
  f : (x : A) → B x
  A' : Set
  f'1 : A → A'
  f'2 : A → A'

foo : ∀ x → f'1 x ≋ f'2 x
foo = {!!}

bar : f'1 ≋ f'2
bar = {!!}
