
------------------------------------------------------------------------
-- The Agda standard library
--
-- Some examples showing how the AVL tree module can be used
------------------------------------------------------------------------

module AVL where

open import Data.Product as Prod
open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (_≡_)

module A
  {i k v ℓ}
  {Index : Set i} {Key : Index → Set k} (Value : Index → Set v)
  {_<_ : Rel (∃ Key) ℓ}
  (isStrictTotalOrder : IsStrictTotalOrder _≡_ _<_)
  where
  open import Data.AVL.IndexedMap Value isStrictTotalOrder

  open import Data.Maybe.Base
  import Data.AVL

  private
    open module AVL =
      Data.AVL (λ ik → Value (proj₁ ik)) isStrictTotalOrder
      public using () renaming (Tree to Map2)

  private
    open module AVLE =
      Data.AVL.Extended-key (λ ik → Value (proj₁ ik)) isStrictTotalOrder

  open import Data.Bool.Base using (Bool)
  import Data.DifferenceList as DiffList
  open import Data.Empty
  open import Data.List.Base as List using (List)
  open import Data.Maybe.Base hiding (map)
  open import Data.Nat.Base hiding (_<_; _⊔_)
  open import Data.Product hiding (map)
  open import Data.Unit
  open import Function
  open import Level using (_⊔_; Lift; lift)

  insertSuccess : ∀ (map : Map) (myI : Index) (myK : Key myI) (myV : Value myI) → (lookup myK (insert myK myV map) ≡ just myV)
  insertSuccess (Data.AVL.tree (Data.AVL.Indexed.leaf (lift tt))) myI myK myV = {!!}
  insertSuccess (Data.AVL.tree (Data.AVL.Indexed.node k₁ x x₁ bal)) myI myK myV = {!!}

------------------------------------------------------------------------
-- Setup

-- AVL trees are defined in Data.AVL.

import Data.AVL
import Data.AVL.IndexedMap

-- This module is parametrised by keys, which have to form a (strict)
-- total order, and values, which are indexed by keys. Let us use
-- natural numbers as keys and vectors of strings as values.

import Data.Nat.Properties as ℕ
open import Data.String using (String)
open import Data.Vec using (Vec; _∷_; [])
open import Relation.Binary using (module StrictTotalOrder)

open import Data.Product as Prod

open import Data.Bool.Base

--open Data.AVL (Vec String)
--              (StrictTotalOrder.isStrictTotalOrder ℕ.strictTotalOrder)

open Data.AVL (Vec String)
              (StrictTotalOrder.isStrictTotalOrder ℕ.strictTotalOrder)

------------------------------------------------------------------------
-- Construction of trees

-- Some values.

v₁  = "cepa" ∷ []
v₁′ = "depa" ∷ []
v₂  = "apa" ∷ "bepa" ∷ []

-- Empty and singleton trees.

--t₀' : MyTree String
--t₀' = MYT empty

t₀ : Tree
t₀ = empty

t₁ : Tree
t₁ = singleton 2 v₂

-- Insertion of a key-value pair into a tree.

t₂ = insert 1 v₁ t₁

-- If you insert a key-value pair and the key already exists in the
-- tree, then the old value is thrown away.

t₂′ = insert 1 v₁′ t₂

-- Deletion of the mapping for a certain key.

t₃ = delete 2 t₂

-- Conversion of a list of key-value mappings to a tree.

open import Data.List using (_∷_; [])
open import Data.Product as Prod using (_,_; _,′_)

t₄ = fromList ((2 , v₂) ∷ (1 , v₁) ∷ [])

------------------------------------------------------------------------
-- Queries

-- Let us formulate queries as unit tests.

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- Searching for a key.

open import Data.Bool.Base using (true; false)
open import Data.Maybe.Base as Maybe using (just; nothing)

q₀ : lookup 2 t₂ ≡ just v₂
q₀ = refl

q₁ : lookup 2 t₃ ≡ nothing
q₁ = refl

q₂ : (3 ∈? t₂) ≡ false
q₂ = refl

q₃ : (1 ∈? t₄) ≡ true
q₃ = refl

-- Turning a tree into a sorted list of key-value pairs.

q₄ : toList t₁ ≡ (2 , v₂) ∷ []
q₄ = refl

q₅ : toList t₂ ≡ (1 , v₁) ∷ (2 , v₂) ∷ []
q₅ = refl

q₅′ : toList t₂′ ≡ (1 , v₁′) ∷ (2 , v₂) ∷ []
q₅′ = refl

------------------------------------------------------------------------
-- Views

-- Partitioning a tree into the smallest element plus the rest, or the
-- largest element plus the rest.

open import Function using (id)

v₆ : headTail t₀ ≡ nothing
v₆ = refl

v₇ : Maybe.map (Prod.map id toList) (headTail t₂) ≡
     just ((1 , v₁) , ((2 , v₂) ∷ []))
v₇ = refl

v₈ : initLast t₀ ≡ nothing
v₈ = refl

v₉ : Maybe.map (Prod.map toList id) (initLast t₄) ≡
     just (((1 , v₁) ∷ []) ,′ (2 , v₂))
v₉ = refl

------------------------------------------------------------------------
-- Further reading

-- Variations of the AVL tree module are available:

-- • Finite maps with indexed keys and values.

import Data.AVL.IndexedMap

-- • Finite sets.

import Data.AVL.Sets
