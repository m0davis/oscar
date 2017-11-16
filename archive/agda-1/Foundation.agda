
module Foundation where

infix -65536 ℞_
℞_ : ∀ ℓ → Set _
℞_ ℓ = Set ℓ

id : ∀ {ℓ} {A : ℞ ℓ} → A → A
id x = x

Op₀ : ∀ {ℓ} → ℞ ℓ → ℞ ℓ
Op₀ = id

Op₁ : ∀ {a} → ℞ a → ℞ a
Op₁ A = A → Op₀ A

Op₂ : ∀ {a} (A : ℞ a) → ℞ a
Op₂ A = A → Op₁ A

record ♩Op₀ {a} (A : ℞ a) : ℞ a where field 𝟘 : Op₀ A

record ♩Op₁ {a} (A : ℞ a) : ℞ a where
  infixr 65536 ¡_
  field ¡_ : Op₁ A

record ♩Op₂ {a} (A : ℞ a) : ℞ a where
  infixl 0 _∙_
  field _∙_ : Op₂ A

open ♩Op₀ ⦃ … ⦄ public
open ♩Op₁ ⦃ … ⦄ public
open ♩Op₂ ⦃ … ⦄ public

instance Set₀♩Op₀=Level : ♩Op₀ Set₀
Set₀♩Op₀=Level = record { 𝟘 = Level } where open import Agda.Primitive

instance Set₀♩Op₀=Nat : ♩Op₀ _
♩Op₀.𝟘 Set₀♩Op₀=Nat = Nat where open import Agda.Builtin.Nat

instance Nat♩Op₁=successor : ♩Op₁ 𝟘
♩Op₁.¡_ Nat♩Op₁=successor = suc where open import Agda.Builtin.Nat

instance zero♩Op₀Nat : ♩Op₀ 𝟘
♩Op₀.𝟘 zero♩Op₀Nat = zero where open import Agda.Builtin.Nat

instance Level♩Op₀ : ♩Op₀ 𝟘
♩Op₀.𝟘 Level♩Op₀ = lzero where open import Agda.Primitive

instance Level♩Op₁ : ♩Op₁ _
♩Op₁.¡_ Level♩Op₁ = lsuc where open import Agda.Primitive

instance Level♩Op₂ : ♩Op₂ 𝟘
♩Op₂._∙_ Level♩Op₂ = _⊔_ where open import Agda.Primitive

_℞_ : ∀ {a} (A : ℞ a) → ∀ ℓ → ℞ _
_℞_ A ℓ = A → ℞ ℓ

_₂℞_ : ∀ {a} (A : ℞ a) → ∀ ℓ → ℞ _
_₂℞_ A ℓ = A → A ℞ ℓ

record IsReflexive {a} {A : ℞ a} {ℓ} (_∼_ : A ₂℞ ℓ) : ℞ a ∙ ℓ where
  field
    reflexive : ∀ {x} → x ∼ x

open IsReflexive ⦃ … ⦄

record IsSymmetric {a} {A : ℞ a} {ℓ} (_∼_ : A ₂℞ ℓ) : ℞ a ∙ ℓ where
  field
    symmetric : ∀ {x} {y} → x ∼ y → y ∼ x

open IsSymmetric ⦃ … ⦄

record IsTransitive {a} {A : ℞ a} {ℓ} (_∼_ : A ₂℞ ℓ) : ℞ a ∙ ℓ where
  field
    transitive : ∀ {x} {y} {z} → x ∼ y → y ∼ z → x ∼ z

open IsTransitive ⦃ … ⦄

record IsEquivalence {a} {A : ℞ a} {ℓ} (_≈_ : A ₂℞ ℓ) : ℞ a ∙ ℓ where
  field
    overlap ⦃ reflexive ⦄ : IsReflexive _≈_
    overlap ⦃ symmetric ⦄ : IsSymmetric _≈_
    overlap ⦃ transitive ⦄ : IsTransitive _≈_

open IsEquivalence ⦃ … ⦄
open import Agda.Primitive

record Equivalence {a} (A : ℞ a) ℓ : ℞ (a ∙ ¡ ℓ) where
  infix 4 _≈_
  field
    _≈_ : A ₂℞ ℓ
    isEquivalence : IsEquivalence _≈_

open Equivalence ⦃ … ⦄

record IsAssociative {a} {A : ℞ a} (_∘_ : Op₂ A) {ℓ} (_≈_ : A ₂℞ ℓ) : ℞ a ∙ ¡ ℓ where
  field
    associative : ∀ x y z → (x ∘ (y ∘ z)) ≈ ((x ∘ y) ∘ z)

open IsAssociative ⦃ … ⦄

import Relation.Binary.Core as R

record ⟦_Preserves₂_⟶_⟶_⟧
       {a b c ℓ₁ ℓ₂ ℓ₃} {A : ℞ a} {B : ℞ b} {C : ℞ c}
       (_+_ : A → B → C) (P : R.Rel A ℓ₁) (Q : R.Rel B ℓ₂) (R : R.Rel C ℓ₃)
       : ℞ a ∙ b ∙ ℓ₁ ∙ ℓ₂ ∙ ℓ₃ where
  field
    _⟶_ : ∀ {x y u v} → P x y → Q u v → R (x + u) (y + v)

open ⟦_Preserves₂_⟶_⟶_⟧ ⦃ … ⦄

record Cong₂
       a b c
       (P : ∀ {x} {X : Set x} → X → X → Set (a ∙ x))
       : ℞ ¡ a ∙ ¡ b ∙ ¡ c where
  field
    cong₂ : {A : ℞ a} {B : ℞ b} {C : ℞ c} (_+_ : A → B → C) → ∀ {x y u v} → P x y → P u v → P (x + u) (y + v)

open Cong₂ ⦃ … ⦄

open import Prelude.Function using (_∘_; _∘′_)
open import Level

--instance Cong₂≡ : ∀ {a b c} → Cong₂ a b c (λ x₁ x₂ → Lift (x₁ R.≡ x₂)) -- R._≡_
--Cong₂≡ = {!!}
--Cong₂.cong₂ Cong₂≡ _+_ R.refl R.refl = R.refl

record Semigroup {a} (A : ℞ a) ℓ : ℞ a ∙ ¡ ℓ where
  field
    _⁀_ : Op₂ A
    overlap ⦃ equivalence ⦄ : Equivalence A ℓ
    ⦃ isAssociative ⦄ : IsAssociative _⁀_ _≈_
    ⦃ ∙-cong ⦄ : ⟦ _⁀_ Preserves₂ _≈_ ⟶ _≈_ ⟶ _≈_ ⟧

open Semigroup ⦃ … ⦄

record IdentityElement {a} (A : ℞ a) : ℞ a where
  field
    ε : A

open IdentityElement ⦃ … ⦄

record IsLeftIdentity {a} {A : ℞ a} ℓ (ε : A) (_∘_ : Op₂ A) : ℞ ¡ ℓ ∙ a where
  field
    overlap ⦃ equivalence ⦄ : Equivalence A ℓ
    left-identity : ∀ x → ε ∘ x ≈ x

open IsLeftIdentity ⦃ … ⦄

record IsRightIdentity {a} {A : ℞ a} ℓ (ε : A) (_∘_ : Op₂ A) : ℞ ¡ ℓ ∙ a where
  field
    overlap ⦃ equivalence ⦄ : Equivalence A ℓ
    right-identity : ∀ x → x ∘ ε ≈ x

open IsRightIdentity ⦃ … ⦄

record IsIdentity {a} {A : ℞ a} ℓ (ε : A) (_∘_ : Op₂ A) : ℞ ¡ ℓ ∙ a where
  field
    ⦃ isLeftIdentity ⦄ : IsLeftIdentity ℓ ε _∘_
    ⦃ isRightIdentity ⦄ : IsRightIdentity ℓ ε _∘_

open IsIdentity ⦃ … ⦄

record IsMonoid {a} (A : ℞ a) (ε : A) ℓ
  : ℞ a ∙ ¡ ℓ where
  field
    ⦃ semigroup ⦄ : Semigroup A ℓ
    ⦃ isIdentity ⦄ : IsIdentity ℓ ε _⁀_

open IsMonoid ⦃ … ⦄

record Monoid {a} (A : ℞ a) ℓ : ℞ a ∙ ¡ ℓ where
  field
    ⦃ identityElement ⦄ : IdentityElement A
    ⦃ isMonoid ⦄ : IsMonoid A ε ℓ

open Monoid ⦃ … ⦄

foo : (A : Set) ⦃ _ : Monoid A Level.zero ⦄ → (x : A) → (x ⁀ ε) ≈ x
foo A ⦃ m ⦄ x₁ = right-identity {zero} {{!!}}  {{!!}}  {{!!}} {{!!}} ⦃ isRightIdentity {{!!}} {{!!}} {{!!}} {{!!}} {{!!}} ⦄ x₁
