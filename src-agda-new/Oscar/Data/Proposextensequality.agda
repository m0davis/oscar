
module Oscar.Data.Proposextensequality where

open import Oscar.Data.Proposequality using (_≡_)
open import Oscar.Level

infix 4 _≡̇_
_≡̇_ : ∀ {a} {A : Set a} {b} {B : A → Set b} → ((x : A) → B x) → ((x : A) → B x) → Set (a ⊔ b)
f ≡̇ g = ∀ x → f x ≡ g x
