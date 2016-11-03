{- This uses Agda and agda-stdlib 2.4.2.3 -}

{- In the below, lemJoinˡ⁺IsCorrect, I am trying to prove that if a key is in the left-hand tree given to Data.AVL.Indexed.joinˡ⁺ then it will still be present in the joined tree. Unforunately, I have only been successful in about half of the cases. Would someone be so kind as to clue me in as to what might be going wrong? -}

open import Relation.Binary
open import Relation.Binary.PropositionalEquality as P using (_≡_)

module Enagda03
  {k v ℓ}
  {Key : Set k} (Value : Key → Set v)
  {_<_ : Rel Key ℓ}
  (isStrictTotalOrder : IsStrictTotalOrder P._≡_ _<_) where

open import Data.Product
open import Level using (_⊔_)
open import Data.AVL Value isStrictTotalOrder using (KV; module Extended-key; module Height-invariants; module Indexed)
open Extended-key
open Height-invariants
open Indexed

open IsStrictTotalOrder isStrictTotalOrder

data _∈_ {lb ub} (key : Key) : ∀ {n} → Tree lb ub n → Set (k ⊔ v ⊔ ℓ) where
  here : ∀ {hˡ hʳ h v}
    {lk : Tree lb [ key ] hˡ}
    {ku : Tree [ key ]  ub hʳ}
    {bal : hˡ ∼ hʳ ⊔ h} →
    key ∈ node (key , v) lk ku bal
  left : ∀ {hˡ hʳ h k′} {v′ : Value k′}
    {lk′ : Tree lb [ k′ ] hˡ}
    {k′u : Tree [ k′ ] ub hʳ}
    {bal : hˡ ∼ hʳ ⊔ h} →
    key ∈ lk′ →
    key ∈ node (k′ , v′) lk′ k′u bal
  right : ∀ {hˡ hʳ h k′} {v′ : Value k′}
    {lk′ : Tree lb [ k′ ] hˡ}
    {k′u : Tree [ k′ ] ub hʳ}
    {bal : hˡ ∼ hʳ ⊔ h} →
    key ∈ k′u →
    key ∈ node (k′ , v′) lk′ k′u bal

open import Data.Nat.Base

lemJoinˡ⁺IsCorrect : ∀ { l r hˡ hʳ h }
    { k′ : Key }
    { v′ : Value k′ }
    ( tˡ⁺ : ∃ λ i → Tree l [ k′ ] ( i ⊕ hˡ ) )
    ( tʳ : Tree [ k′ ] r hʳ )
    ( bal : hˡ ∼ hʳ ⊔ h )
    { key : Key }
    ( k∈tˡ : key ∈ proj₂ tˡ⁺ ) →
    key ∈ proj₂ ( joinˡ⁺ ( k′ , v′ ) tˡ⁺ tʳ bal )
lemJoinˡ⁺IsCorrect ( 1# , node _ _ ( node _ _ _ _ ) ∼+ ) _ ∼- here = left here
lemJoinˡ⁺IsCorrect ( 1# , node _ _ ( node _ _ _ _ ) ∼+ ) _ ∼- ( left k∈tˡ ) = left ( left k∈tˡ )
lemJoinˡ⁺IsCorrect ( 1# , node _ _ ( node _ _ _ _ ) ∼+ ) _ ∼- ( right here ) = here
lemJoinˡ⁺IsCorrect ( 1# , node _ _ ( node _ _ _ _ ) ∼+ ) _ ∼- ( right ( left k∈tʳˡ ) ) = left ( right k∈tʳˡ )
lemJoinˡ⁺IsCorrect ( 1# , node _ _ ( node _ _ _ _ ) ∼+ ) _ ∼- ( right ( right k∈tʳʳ ) ) = right ( left k∈tʳʳ )
{- This is the first case that doesn't work. -}
lemJoinˡ⁺IsCorrect ( 1# , node _ _ _ ∼- ) _ ∼- here = {!here!}
{- 
   If I fill-out the term as follows 

      lemJoinˡ⁺IsCorrect ( 1# , node _ _ _ ∼- ) _ ∼- here = here

   then I get the following error:

      suc (_h_217 Value isStrictTotalOrder .k .lk .ku .tʳ)
      !=
      proj₁ (joinˡ⁺ (.k′ , .v′) (1# , node .k .lk .ku ∼-) .tʳ ∼-) ⊕ (1 + suc .hʳ)
      of type ℕ
      when checking that the expression here has type
      proj₁ .k ∈ proj₂ (joinˡ⁺ (.k′ , .v′) (1# , node .k .lk .ku ∼-) .tʳ ∼-)

   Thinking it would help, I tried to get around the above error by specifying the implicit variable h:

      lemJoinˡ⁺IsCorrect { hʳ = hʳ } ( 1# , node _ _ _ ∼- ) _ ∼- here = here { h = suc hʳ }

   But that just results in a different error:

      suc (suc hʳ) !=
      proj₁ (joinˡ⁺ (.k′ , .v′) (1# , node .k .lk .ku ∼-) .tʳ ∼-) ⊕ (1 + suc hʳ)
      of type ℕ
      when checking that the expression here {h = suc hʳ} has type
      proj₁ .k ∈ proj₂ (joinˡ⁺ (.k′ , .v′) (1# , node .k .lk .ku ∼-) .tʳ ∼-)

   Notice that, from the definition of joinˡ⁺, the first and second lines in the above-reported error are actually equivalent. So, what's going on? Is it not "eta reducing"? And how would I get it to reduce?
-}
lemJoinˡ⁺IsCorrect ( 1# , node _ _ _ ∼- ) _ ∼- ( left k∈tˡˡ ) = {!left k∈tˡˡ!}
lemJoinˡ⁺IsCorrect ( 1# , node _ _ _ ∼- ) _ ∼- ( right k∈tˡʳ ) = {!right ( left ( k∈tˡʳ ) )!}
lemJoinˡ⁺IsCorrect ( 1# , node _ _ _ ∼0 ) _ ∼- here = {!here!}
lemJoinˡ⁺IsCorrect ( 1# , node _ _ _ ∼0 ) _ ∼- ( left k∈tˡˡ ) = {!left k∈tˡˡ!}
lemJoinˡ⁺IsCorrect ( 1# , node _ _ _ ∼0 ) _ ∼- ( right k∈tˡʳ ) = {!right ( left ( k∈tˡʳ ) )!}
lemJoinˡ⁺IsCorrect ( 1# , _ ) _ ∼0 k∈tˡ = {!left k∈tˡ!}
lemJoinˡ⁺IsCorrect ( 1# , _ ) _ ∼+ k∈tˡ = {!left k∈tˡ!}
lemJoinˡ⁺IsCorrect ( 0# , _ ) _ _ k∈tˡ = left k∈tˡ
