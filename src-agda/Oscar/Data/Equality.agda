
module Oscar.Data.Equality where

open import Agda.Builtin.Equality public using (_≡_; refl) public
open import Relation.Binary.PropositionalEquality public using (_≢_) public

open import Oscar.Level

infix 4 _≡̇_
_≡̇_ : ∀ {a} {A : Set a} {b} {B : A → Set b} → ((x : A) → B x) → ((x : A) → B x) → Set (a ⊔ b)
f ≡̇ g = ∀ x → f x ≡ g x
