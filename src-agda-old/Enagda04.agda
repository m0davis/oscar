{- showing stuff that can be done with Free -}

open import Level using (_⊔_; lift)
open import Relation.Binary
open import Data.List.Base
open import Relation.Binary.PropositionalEquality using (_≡_)
-- import Data.AVL
-- open Data.AVL.Indexed
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Nat.Base using (ℕ)

data FreeList { α } ( a : Set α ) : Set α where
  pure : a → FreeList a
  free : List (FreeList a) → FreeList a

module FreeListExamples where
  ex0 : FreeList ℕ
  ex0 = pure 0
 
  ex1 : FreeList ℕ
  ex1 = pure 1
 
  ex2 : FreeList ℕ
  ex2 = free (ex0 ∷ ex1 ∷ [])

data Free { α φ } ( f : Set α → Set φ ) ( a : Set α ) : Set ( Level.suc ( α ⊔ φ ) ) where
  pure : a → Free f a
  free : ∀ { x : Set α } → ( x → Free f a ) → f x → Free f a

data Free'' { α φ } ( f : Set α → Set φ ) ( a : Set α ) : Set ( Level.suc ( α ⊔ φ ) ) where
  pure : a → Free'' f a
  free : ∀ ℕ → ( ℕ → Free'' f a ) → f ℕ → Free'' f a



SumOfFreeListℕ : Free List ℕ → ℕ
SumOfFreeListℕ (pure n) = n
SumOfFreeListℕ (free xffa []) = 0
SumOfFreeListℕ (free xffa (x₁ ∷ fx)) = SumOfFreeListℕ (xffa x₁) Data.Nat.Base.+ SumOfFreeListℕ {!free xffa fx!}

open import Data.Bool.Base

weirdFreeList : Free List ℕ
weirdFreeList = free depFn (false ∷ true ∷ []) where
  depFn : Bool → Free List ℕ
  depFn false = pure 0
  depFn true = pure 1

weirdFreeList' : Free List ℕ
weirdFreeList' = free depFn (0 ∷ 1 ∷ []) where
  depFn : ℕ → Free List ℕ
  depFn 0 = pure 0
  depFn 1 = pure 1
  depFn _ = pure 42

module GeneralFree { α φ } ( a : Set α )  ( f : Set (α ⊔ φ) → Set φ ) where
  data Free' : ℕ → Set ( Level.suc (α ⊔ φ) ) where
    pure : a → Free' 0
    free : ∀ x { h } → (x → (Free' h)) → f x  → Free' (ℕ.suc h)
    


simpleFree : Free List ℕ
simpleFree = free { x = List ℕ }  (λ x → free (λ x₁ → pure 2) (1 ∷ [])) [] 

{-
match : ∀ { ℓ α }
        ( a : Set (Level.suc α) )
        ( _<_ : Rel a ℓ ) →
        ( isStrictTotalOrder : IsStrictTotalOrder P._≡_ _<_ ) →
        Free { φ₁ = α ⊔ ℓ } { φ₂ = α ⊔ ℓ } List a →
        Free { φ₁ = ℓ } List a →
        List a →
        Tree {Key = a} (Free { α = α } {φ₁ = α } { φ₂ = α } (List {a = α})) isStrictTotalOrder
match = {!!}
-}
