
module Oscar.Data.Equality where

open import Agda.Builtin.Equality public using (_≡_; refl) public
open import Relation.Binary.PropositionalEquality public using (_≢_) public
open import Relation.Binary.PropositionalEquality public using (cong; cong₂; cong-app; subst; subst₂; sym; trans) public

open import Oscar.Level
open import Oscar.Function
open import Oscar.Relation

infix 4 _≡̇_
_≡̇_ : ∀ {a} {A : Set a} {b} {B : A → Set b} → ((x : A) → B x) → ((x : A) → B x) → Set (a ⊔ b)
f ≡̇ g = ∀ x → f x ≡ g x

≡̇-refl : ∀ {a} {A : Set a} {b} {B : A → Set b} (f : (x : A) → B x) → f ≡̇ f
≡̇-refl _ _ = refl

≡̇-sym : ∀ {a} {A : Set a} {b} {B : A → Set b} {f g : (x : A) → B x} → f ≡̇ g → g ≡̇ f
≡̇-sym f≡̇g = sym ∘ f≡̇g

≡̇-trans : ∀ {a} {A : Set a} {b} {B : A → Set b} {f g : (x : A) → B x} → f ≡̇ g → {h : (x : A) → B x} → g ⟨ _≡̇ h ⟩→ f
≡̇-trans f≡̇g g≡̇h x = trans (f≡̇g x) (g≡̇h x)

open import Oscar.Category

≡-setoid : ∀ {a} (A : Set a) → Setoid A a
Setoid._≋_ (≡-setoid A) = _≡_
Setoid.≋-reflexivity (≡-setoid A) = refl
Setoid.≋-symmetry (≡-setoid A) = sym
Setoid.≋-transitivity (≡-setoid A) x≡y = trans x≡y

≡̇-setoid : ∀ {a} {A : Set a} {b} (B : A → Set b) → Setoid ((x : A) → B x) (a ⊔ b)
Setoid._≋_ (≡̇-setoid B) = _≡̇_
Setoid.≋-reflexivity (≡̇-setoid B) = ≡̇-refl _
Setoid.≋-symmetry (≡̇-setoid B) = ≡̇-sym
Setoid.≋-transitivity (≡̇-setoid B) = ≡̇-trans
