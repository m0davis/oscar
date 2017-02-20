open import Level using ( _⊔_ ; Level )
open import Relation.Binary
open import List
open import Data.List.Base
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Nat.Base using (ℕ)
open import Control.Monad.Free
open import Data.Unit.Base
open import Data.Bool.Base
open import Relation.Nullary
open import Data.Product

module TreeTest where



module Match
  { 𝑼⟨a⟩ 𝑼⟨<ᵃ⟩ 𝑼⟨≡ᶠ⟩ : Level }
  { a : Set 𝑼⟨a⟩ }
  { _<ᵃ_ : Rel a 𝑼⟨<ᵃ⟩ }
  { _≡ᶠ_ : Rel ( Free List a ) 𝑼⟨≡ᶠ⟩ }
  ( isDecEquivalenceᶠ : IsDecEquivalence _≡ᶠ_ )
  ( isStrictTotalOrderᵃ : IsStrictTotalOrder _≡_ _<ᵃ_ )
  where

  


data Map ( key : Set ) ( value : Set ) : Set
  map : tree → Map key value

module T
  { 𝑼⟨a⟩ 𝑼⟨<ᵃ⟩ 𝑼⟨≡ᶠ⟩ : Level }
  ( a : Set 𝑼⟨a⟩ )
  { _<ᵃ_ : Rel a 𝑼⟨<ᵃ⟩ }
  {{ isStrictTotalOrderᵃ : IsStrictTotalOrder _≡_ _<ᵃ_ }}
  where

  reverseMap : ∀  Tree → Tree
  reverseMap = fromList ∘ Data.List.Base.map swap ∘ toList


