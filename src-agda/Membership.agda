
module Membership where

open import OscarPrelude
open import Successor

record Membership {ℓ} (m : Set ℓ) (M : Set ℓ) : Set (⊹ ℓ)
 where
  field
    _∈_ : m → M → Set ℓ
    _∉_ : m → M → Set ℓ
    xor-membership : ∀ {x : m} {X : M} → x ∈ X ←⊗→ x ∉ X

open Membership ⦃ … ⦄ public

data _∈List_ {ℓ} {A : Set ℓ} (a : A) : List A → Set ℓ
 where
  zero : {as : List A} → a ∈List (a ∷ as)
  suc : {x : A} {as : List A} → a ∈List as → a ∈List (x ∷ as)

instance MembershipList : ∀ {ℓ} {A : Set ℓ} → Membership A $ List A
Membership._∈_ MembershipList = _∈List_
Membership._∉_ MembershipList x X = ¬ x ∈ X
Membership.xor-membership MembershipList = (λ x x₁ → x₁ x) , (λ x x₁ → x x₁)

instance SuccessorMembershipList : ∀ {ℓ} {A : Set ℓ} {a : A} {x : A} {as : List A} → Successor (a ∈ as) $ a ∈ (x List.∷ as)
Successor.⊹ SuccessorMembershipList = suc

_⊆_ : ∀ {ℓ} {m M : Set ℓ} ⦃ _ : Membership m M ⦄ → M → M → Set ℓ
_⊆_ {m = m} M₁ M₂ = ∀ {x : m} → x ∈ M₁ → x ∈ M₂
