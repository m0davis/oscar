
module DecidableMembership where

open import OscarPrelude
open import Membership
open import Successor

record DecidableMembership {ℓ} (m : Set ℓ) (M : Set ℓ) ⦃ _ : Membership m M ⦄ : Set (⊹ ℓ)
 where
  field _∈?_ : (x : m) → (X : M) → Dec $ x ∈ X
  field _∉?_ : (x : m) → (X : M) → Dec $ x ∉ X

open DecidableMembership ⦃ … ⦄ public

instance DecidableMembershipList : ∀ {ℓ} {A : Set ℓ} ⦃ _ : Eq A ⦄ → DecidableMembership A $ List A
DecidableMembership._∈?_ (DecidableMembershipList {ℓ} {A}) = _∈List?_
 where
  _∈List?_ : (a : A) → (xs : List A) → Dec (a ∈ xs)
  a ∈List? [] = no λ ()
  a ∈List? (x ∷ xs) with a ≟ x
  … | yes a≡x rewrite a≡x = yes zero
  … | no a≢x with a ∈List? xs
  … | yes a∈xs = yes (⊹ a∈xs)
  … | no a∉xs = no (λ {zero → a≢x refl ; (suc a∈xs) → a∉xs a∈xs})
DecidableMembership._∉?_ (DecidableMembershipList {ℓ} {A}) x X with x ∈? X
DecidableMembership._∉?_ (DecidableMembershipList {ℓ} {A}) x X | yes x∈X = no (λ x∉X → x∉X x∈X)
DecidableMembership._∉?_ (DecidableMembershipList {ℓ} {A}) x X | no x∉X = yes x∉X
