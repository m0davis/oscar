open import Data.Empty
open import Data.Product
open import Level
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as P using (_≡_)
open import Relation.Nullary

open import Data.Nat
open import Data.Nat.Properties

module Data.AVL.TestProperties where

open import Data.AVL.Properties
  (λ _ → ℕ)
  (StrictTotalOrder.isStrictTotalOrder strictTotalOrder)

import Data.AVL (λ _ → ℕ) (StrictTotalOrder.isStrictTotalOrder strictTotalOrder) as AVL
-- open Extended-key                       public
-- open Height-invariants                  public
-- open Indexed                            public


un-tree : AVL.Tree → ∃ λ h → Indexed.Tree ⊥⁺ ⊤⁺ h
un-tree (AVL.tree t) = , t

test : Indexed.Tree _ _ _
test = proj₂ (un-tree
  (AVL.insert 5 55 (AVL.insert 7 77 (AVL.insert 4 44 AVL.empty))))

Extract : ∀ {p} {P : Set p} → Dec P → Set _
Extract {P = P} (yes _) = P
Extract {P = P} (no  _) = ¬ P

extract : ∀ {p} {P : Set p} (d : Dec P) → Extract d
extract (yes p) = p
extract (no ¬p) = ¬p

∈-test₁ : ¬ (2 ∈ test)
∈-test₁ = extract (find 2 test)

∈-test₂ : 4 ∈ test
∈-test₂ = extract (find 4 test)
