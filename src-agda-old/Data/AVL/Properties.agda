open import Level using ( Level )
open import Relation.Binary using ( Rel ; IsStrictTotalOrder ; module IsStrictTotalOrder )
open import Relation.Binary.PropositionalEquality using ( _≡_ )

module Data.AVL.Properties
  { 𝑼⟨Key⟩ 𝑼⟨Value⟩ 𝑼⟨<⟩ : Level }
  { Key : Set 𝑼⟨Key⟩ }
  ( Value : Key → Set 𝑼⟨Value⟩ )
  { _<_ : Rel Key 𝑼⟨<⟩ }
  ( isStrictTotalOrder : IsStrictTotalOrder _≡_ _<_ ) where

open import Data.Empty
open import Data.Product
open import Level using ( _⊔_ )
open import Relation.Nullary
open IsStrictTotalOrder isStrictTotalOrder

open import Relation.Binary.PropositionalEquality using ( refl )
open import Relation.Nullary.Negation using ( contradiction )

open import Data.Maybe
open import Relation.Binary
import Data.Nat.Base as ℕ
open import Relation.Binary.HeterogeneousEquality.Core using ( _≅_ )
 
module Indexed where

  open import Data.AVL Value isStrictTotalOrder using ( KV ; module Extended-key ; module Height-invariants ; module Indexed )
  open Extended-key
  open Height-invariants using ( _∼_⊔_ ; _⊕_ ; ∼- ; ∼+ ; ∼0 ; 1# ; 0# ; ℕ₂ )
  open Indexed
  

  data _∈_ { k⃖ k⃗ } ( k : Key ) : ∀ { h } → Tree k⃖ k⃗ h → Set ( 𝑼⟨Key⟩ ⊔ 𝑼⟨Value⟩ ⊔ 𝑼⟨<⟩ ) where
   
    here : ∀
           { h⃖ h⃗ h v }
           { t⃖ : Tree k⃖ [ k ] h⃖ }
           { t⃗ : Tree [ k ]  k⃗ h⃗ }
           { bal : h⃖ ∼ h⃗ ⊔ h }
           → k ∈ node ( k , v ) t⃖ t⃗ bal
      
    left : ∀
           { h⃖ h⃗ h k′ } { v′ : Value k′ }
           { t⃖ : Tree k⃖ [ k′ ] h⃖ }
           { t⃗ : Tree [ k′ ]  k⃗ h⃗ }
           { bal : h⃖ ∼ h⃗ ⊔ h }
           → k ∈ t⃖
           → k ∈ node ( k′ , v′ ) t⃖ t⃗ bal
      
    right : ∀
            { h⃖ h⃗ h k′ } { v′ : Value k′ }
            { t⃖ : Tree k⃖ [ k′ ] h⃖ }
            { t⃗ : Tree [ k′ ] k⃗ h⃗ }
            { bal : h⃖ ∼ h⃗ ⊔ h }
            → k ∈ t⃗
            → k ∈ node ( k′ , v′ ) t⃖ t⃗ bal


  module 1-1 where
   
    1-1 : ∀
          { l u h }
          → Tree l u h
          → Set ( 𝑼⟨Key⟩ ⊔ 𝑼⟨Value⟩ ⊔ 𝑼⟨<⟩ )
    1-1 t = ∀
            { k k′ v v′ }
            → k ∈ t
            → k′ ∈ t
            → { _ : lookup k t ≡ just v }
            → { _ : lookup k′ t ≡ just v′ }
            → { _ : v ≅ v′ }
            → k ≡ k′
   
    𝒍𝒆𝒎𝒎𝒂∶empty⋐1-1 : ∀
                        { l u }
                        { l<⁺u : l <⁺ u }
                        → 1-1 { l = l } ( empty l<⁺u )
    𝒍𝒆𝒎𝒎𝒂∶empty⋐1-1 ()
    
    𝒍𝒆𝒎𝒎𝒂∶singleton⋐1-1 : ∀
                            { l u }
                            { k }
                            { l<k<u : l < k < u }
                            { v }
                            → 1-1 { l = l } { u = u } ( singleton k v l<k<u )
    𝒍𝒆𝒎𝒎𝒂∶singleton⋐1-1 here here = Relation.Binary.PropositionalEquality.refl
    𝒍𝒆𝒎𝒎𝒂∶singleton⋐1-1 here (left ())
    𝒍𝒆𝒎𝒎𝒂∶singleton⋐1-1 here (right ())
    𝒍𝒆𝒎𝒎𝒂∶singleton⋐1-1 (left ())
    𝒍𝒆𝒎𝒎𝒂∶singleton⋐1-1 (right ())

  𝒍𝒆𝒎𝒎𝒂∶joinˡ⁺Is∈Invariant : ∀ { l r hˡ hʳ h }
                                 { k′ : Key }
                                 { v′ : Value k′ }
                                 ( tˡ⁺ : ∃ λ i → Tree l [ k′ ] ( i ⊕ hˡ ) )
                                 ( tʳ : Tree [ k′ ] r hʳ )
                                 ( bal : hˡ ∼ hʳ ⊔ h )
                                 { key : Key }
                                 ( k∈tˡ : key ∈ proj₂ tˡ⁺ )
                                 → key ∈ proj₂ ( joinˡ⁺ ( k′ , v′ ) tˡ⁺ tʳ bal )
  𝒍𝒆𝒎𝒎𝒂∶joinˡ⁺Is∈Invariant ( 1# , node _ _ ( node _ _ _ _ ) ∼+ ) _ ∼- here                      = left here
  𝒍𝒆𝒎𝒎𝒂∶joinˡ⁺Is∈Invariant ( 1# , node _ _ ( node _ _ _ _ ) ∼+ ) _ ∼- ( left k∈tˡ )             = left ( left k∈tˡ )
  𝒍𝒆𝒎𝒎𝒂∶joinˡ⁺Is∈Invariant ( 1# , node _ _ ( node _ _ _ _ ) ∼+ ) _ ∼- ( right here )            = here
  𝒍𝒆𝒎𝒎𝒂∶joinˡ⁺Is∈Invariant ( 1# , node _ _ ( node _ _ _ _ ) ∼+ ) _ ∼- ( right ( left k∈tʳˡ ) )  = left ( right k∈tʳˡ )
  𝒍𝒆𝒎𝒎𝒂∶joinˡ⁺Is∈Invariant ( 1# , node _ _ ( node _ _ _ _ ) ∼+ ) _ ∼- ( right ( right k∈tʳʳ ) ) = right ( left k∈tʳʳ )
  𝒍𝒆𝒎𝒎𝒂∶joinˡ⁺Is∈Invariant ( 1# , node _ _ ( leaf _       ) ∼- ) _ ∼- here                      = here
  𝒍𝒆𝒎𝒎𝒂∶joinˡ⁺Is∈Invariant ( 1# , node _ _ ( node _ _ _ _ ) ∼- ) _ ∼- here                      = here
  𝒍𝒆𝒎𝒎𝒂∶joinˡ⁺Is∈Invariant ( 1# , node _ _ ( leaf _       ) ∼- ) _ ∼- ( left k∈tˡˡ )            = left k∈tˡˡ
  𝒍𝒆𝒎𝒎𝒂∶joinˡ⁺Is∈Invariant ( 1# , node _ _ ( node _ _ _ _ ) ∼- ) _ ∼- ( left k∈tˡˡ )            = left k∈tˡˡ
  𝒍𝒆𝒎𝒎𝒂∶joinˡ⁺Is∈Invariant ( 1# , node _ _ ( leaf _       ) ∼- ) _ ∼- ( right k∈tˡʳ )           = right (left k∈tˡʳ)
  𝒍𝒆𝒎𝒎𝒂∶joinˡ⁺Is∈Invariant ( 1# , node _ _ ( node _ _ _ _ ) ∼- ) _ ∼- ( right k∈tˡʳ )           = right (left k∈tˡʳ)
  𝒍𝒆𝒎𝒎𝒂∶joinˡ⁺Is∈Invariant ( 1# , node _ _ ( node _ _ _ _ ) ∼0 ) _ ∼- here                      = here
  𝒍𝒆𝒎𝒎𝒂∶joinˡ⁺Is∈Invariant ( 1# , node _ _ ( node _ _ _ _ ) ∼0 ) _ ∼- ( left k∈tˡˡ )            = left k∈tˡˡ
  𝒍𝒆𝒎𝒎𝒂∶joinˡ⁺Is∈Invariant ( 1# , node _ _ ( node _ _ _ _ ) ∼0 ) _ ∼- ( right k∈tˡʳ )           = right (left k∈tˡʳ)
  𝒍𝒆𝒎𝒎𝒂∶joinˡ⁺Is∈Invariant ( 1# , node _ _ ( node _ _ _ _ ) ∼+ ) _ ∼0 k∈tˡ                      = left k∈tˡ
  𝒍𝒆𝒎𝒎𝒂∶joinˡ⁺Is∈Invariant ( 1# , node _ _ ( node _ _ _ _ ) ∼- ) _ ∼0 k∈tˡ                      = left k∈tˡ
  𝒍𝒆𝒎𝒎𝒂∶joinˡ⁺Is∈Invariant ( 1# , node _ _ ( node _ _ _ _ ) ∼0 ) _ ∼0 k∈tˡ                      = left k∈tˡ
  𝒍𝒆𝒎𝒎𝒂∶joinˡ⁺Is∈Invariant ( 1# , node _ _ ( leaf _       ) ∼- ) _ ∼0 k∈tˡ                      = left k∈tˡ
  𝒍𝒆𝒎𝒎𝒂∶joinˡ⁺Is∈Invariant ( 1# , node _ _ ( leaf _       ) ∼0 ) _ ∼0 k∈tˡ                      = left k∈tˡ
  𝒍𝒆𝒎𝒎𝒂∶joinˡ⁺Is∈Invariant ( 1# , node _ _ ( node _ _ _ _ ) ∼+ ) _ ∼+ k∈tˡ                      = left k∈tˡ
  𝒍𝒆𝒎𝒎𝒂∶joinˡ⁺Is∈Invariant ( 1# , node _ _ ( node _ _ _ _ ) ∼- ) _ ∼+ k∈tˡ                      = left k∈tˡ
  𝒍𝒆𝒎𝒎𝒂∶joinˡ⁺Is∈Invariant ( 1# , node _ _ ( node _ _ _ _ ) ∼0 ) _ ∼+ k∈tˡ                      = left k∈tˡ
  𝒍𝒆𝒎𝒎𝒂∶joinˡ⁺Is∈Invariant ( 1# , node _ _ ( leaf _       ) ∼- ) _ ∼+ k∈tˡ                      = left k∈tˡ
  𝒍𝒆𝒎𝒎𝒂∶joinˡ⁺Is∈Invariant ( 1# , node _ _ ( leaf _       ) ∼0 ) _ ∼+ k∈tˡ                      = left k∈tˡ
  𝒍𝒆𝒎𝒎𝒂∶joinˡ⁺Is∈Invariant ( 0# , _                            ) _ _  k∈tˡ                      = left k∈tˡ
   
  𝒍𝒆𝒎𝒎𝒂∶joinʳ⁺Is∈Invariant : ∀ { l r hˡ hʳ h }
                                 { k′ : Key }
                                 { v′ : Value k′ }
                                 ( tˡ : Tree l [ k′ ] hˡ )
                                 ( tʳ⁺ : ∃ λ i → Tree [ k′ ] r ( i ⊕ hʳ ) )
                                 ( bal : hˡ ∼ hʳ ⊔ h )
                                 { key : Key }
                                 ( k∈tʳ : key ∈ proj₂ tʳ⁺ )
                                 → key ∈ proj₂ ( joinʳ⁺ ( k′ , v′ ) tˡ tʳ⁺ bal )
  𝒍𝒆𝒎𝒎𝒂∶joinʳ⁺Is∈Invariant _ ( 1# , node _ ( node _ _ _ _ ) _ ∼- ) ∼+ here                      = right here
  𝒍𝒆𝒎𝒎𝒂∶joinʳ⁺Is∈Invariant _ ( 1# , node _ ( node _ _ _ _ ) _ ∼- ) ∼+ ( right k∈tʳ )            = right ( right k∈tʳ )
  𝒍𝒆𝒎𝒎𝒂∶joinʳ⁺Is∈Invariant _ ( 1# , node _ ( node _ _ _ _ ) _ ∼- ) ∼+ ( left here )             = here
  𝒍𝒆𝒎𝒎𝒂∶joinʳ⁺Is∈Invariant _ ( 1# , node _ ( node _ _ _ _ ) _ ∼- ) ∼+ ( left ( left k∈tʳˡ ) )   = left ( right k∈tʳˡ )
  𝒍𝒆𝒎𝒎𝒂∶joinʳ⁺Is∈Invariant _ ( 1# , node _ ( node _ _ _ _ ) _ ∼- ) ∼+ ( left ( right k∈tʳʳ ) )  = right ( left k∈tʳʳ )
  𝒍𝒆𝒎𝒎𝒂∶joinʳ⁺Is∈Invariant _ ( 1# , node _ ( leaf _       ) _ ∼+ ) ∼+ here                      = here
  𝒍𝒆𝒎𝒎𝒂∶joinʳ⁺Is∈Invariant _ ( 1# , node _ ( node _ _ _ _ ) _ ∼+ ) ∼+ here                      = here
  𝒍𝒆𝒎𝒎𝒂∶joinʳ⁺Is∈Invariant _ ( 1# , node _ ( leaf _       ) _ ∼+ ) ∼+ ( left k∈tʳˡ )            = left ( right k∈tʳˡ )
  𝒍𝒆𝒎𝒎𝒂∶joinʳ⁺Is∈Invariant _ ( 1# , node _ ( node _ _ _ _ ) _ ∼+ ) ∼+ ( left k∈tʳˡ )            = left ( right k∈tʳˡ )
  𝒍𝒆𝒎𝒎𝒂∶joinʳ⁺Is∈Invariant _ ( 1# , node _ ( leaf _       ) _ ∼+ ) ∼+ ( right k∈tʳʳ )           = right k∈tʳʳ
  𝒍𝒆𝒎𝒎𝒂∶joinʳ⁺Is∈Invariant _ ( 1# , node _ ( node _ _ _ _ ) _ ∼+ ) ∼+ ( right k∈tʳʳ )           = right k∈tʳʳ
  𝒍𝒆𝒎𝒎𝒂∶joinʳ⁺Is∈Invariant _ ( 1# , node _ ( node _ _ _ _ ) _ ∼0 ) ∼+ here                      = here
  𝒍𝒆𝒎𝒎𝒂∶joinʳ⁺Is∈Invariant _ ( 1# , node _ ( node _ _ _ _ ) _ ∼0 ) ∼+ ( left k∈tʳˡ )            = left (right k∈tʳˡ)
  𝒍𝒆𝒎𝒎𝒂∶joinʳ⁺Is∈Invariant _ ( 1# , node _ ( node _ _ _ _ ) _ ∼0 ) ∼+ ( right k∈tʳʳ )           = right k∈tʳʳ
  𝒍𝒆𝒎𝒎𝒂∶joinʳ⁺Is∈Invariant _ ( 1# , node _ ( node _ _ _ _ ) _ ∼- ) ∼0 k∈tʳ                      = right k∈tʳ
  𝒍𝒆𝒎𝒎𝒂∶joinʳ⁺Is∈Invariant _ ( 1# , node _ ( node _ _ _ _ ) _ ∼+ ) ∼0 k∈tʳ                      = right k∈tʳ
  𝒍𝒆𝒎𝒎𝒂∶joinʳ⁺Is∈Invariant _ ( 1# , node _ ( node _ _ _ _ ) _ ∼0 ) ∼0 k∈tʳ                      = right k∈tʳ
  𝒍𝒆𝒎𝒎𝒂∶joinʳ⁺Is∈Invariant _ ( 1# , node _ ( leaf _       ) _ ∼+ ) ∼0 k∈tʳ                      = right k∈tʳ
  𝒍𝒆𝒎𝒎𝒂∶joinʳ⁺Is∈Invariant _ ( 1# , node _ ( leaf _       ) _ ∼0 ) ∼0 k∈tʳ                      = right k∈tʳ
  𝒍𝒆𝒎𝒎𝒂∶joinʳ⁺Is∈Invariant _ ( 1# , node _ ( node _ _ _ _ ) _ ∼- ) ∼- k∈tʳ                      = right k∈tʳ
  𝒍𝒆𝒎𝒎𝒂∶joinʳ⁺Is∈Invariant _ ( 1# , node _ ( node _ _ _ _ ) _ ∼+ ) ∼- k∈tʳ                      = right k∈tʳ
  𝒍𝒆𝒎𝒎𝒂∶joinʳ⁺Is∈Invariant _ ( 1# , node _ ( node _ _ _ _ ) _ ∼0 ) ∼- k∈tʳ                      = right k∈tʳ
  𝒍𝒆𝒎𝒎𝒂∶joinʳ⁺Is∈Invariant _ ( 1# , node _ ( leaf _       ) _ ∼+ ) ∼- k∈tʳ                      = right k∈tʳ
  𝒍𝒆𝒎𝒎𝒂∶joinʳ⁺Is∈Invariant _ ( 1# , node _ ( leaf _       ) _ ∼0 ) ∼- k∈tʳ                      = right k∈tʳ
  𝒍𝒆𝒎𝒎𝒂∶joinʳ⁺Is∈Invariant _ ( 0# , _                            ) _  k∈tʳ                      = right k∈tʳ
   
  𝒍𝒆𝒎𝒎𝒂∶Tree<⁺ : ∀ { k⃖ k⃗ h } → Tree k⃖ k⃗ h → k⃖ <⁺ k⃗
  𝒍𝒆𝒎𝒎𝒂∶Tree<⁺ ( leaf k⃖<k⃗ ) = k⃖<k⃗
  𝒍𝒆𝒎𝒎𝒂∶Tree<⁺ { k⃖ = k⃖ } ( node _ t⃖ t⃗ _ ) = trans⁺ k⃖ ( 𝒍𝒆𝒎𝒎𝒂∶Tree<⁺ t⃖ ) ( 𝒍𝒆𝒎𝒎𝒂∶Tree<⁺ t⃗ )

  𝒍𝒆𝒎𝒎𝒂∶∈⟶<< : ∀ { l u h } { t : Tree l u h } { k : Key } → k ∈ t → l < k < u
  𝒍𝒆𝒎𝒎𝒂∶∈⟶<< ( here { t⃖ = t⃖ } { t⃗ = t⃗ } ) = 𝒍𝒆𝒎𝒎𝒂∶Tree<⁺ t⃖ , 𝒍𝒆𝒎𝒎𝒂∶Tree<⁺ t⃗
  𝒍𝒆𝒎𝒎𝒂∶∈⟶<< { l = l } { u = u } { k = k } ( left { k′ = k′ } { t⃗ = t⃗ } k∈tˡ ) = l<k , k<u where
   
    l<k<k′ : l < k < [ k′ ]
    l<k<k′ = 𝒍𝒆𝒎𝒎𝒂∶∈⟶<< k∈tˡ
   
    l<k : l <⁺ [ k ]
    l<k = proj₁ l<k<k′
   
    k<k′ : [ k ] <⁺ [ k′ ]
    k<k′ = proj₂ l<k<k′
   
    k′<u : [ k′ ] <⁺ u
    k′<u = 𝒍𝒆𝒎𝒎𝒂∶Tree<⁺ t⃗
   
    k<u : [ k ] <⁺ u
    k<u = trans⁺ [ k ] { m = [ k′ ] } { u = u } k<k′ k′<u
   
  𝒍𝒆𝒎𝒎𝒂∶∈⟶<< { l = l } { u = u } { k = k } ( right { k′ = k′ } { t⃖ = lk′ } k∈tʳ ) = l<k , k<u where
   
    k′<k<u : [ k′ ] < k < u
    k′<k<u = 𝒍𝒆𝒎𝒎𝒂∶∈⟶<< k∈tʳ
   
    k<u : [ k ] <⁺ u
    k<u = proj₂ k′<k<u
   
    k′<k : [ k′ ] <⁺ [ k ] 
    k′<k = proj₁ k′<k<u
   
    l<k′ : l <⁺ [ k′ ]
    l<k′ = 𝒍𝒆𝒎𝒎𝒂∶Tree<⁺ lk′
   
    l<k : l <⁺ [ k ]
    l<k = trans⁺ l { m = [ k′ ] } { u = [ k ] } l<k′ k′<k
   
  𝒍𝒆𝒎𝒎𝒂∶lookup⟶∈ : ∀ { l u h } ( k : Key ) ( t : Tree l u h ) → ( ∃ λ v → lookup k t ≡ just v ) → k ∈ t
  𝒍𝒆𝒎𝒎𝒂∶lookup⟶∈ _ ( leaf _ ) ( _ , () )
  𝒍𝒆𝒎𝒎𝒂∶lookup⟶∈ k ( node ( kₜ , vₜ ) tₗ tᵤ _ ) lookup⟶ with compare k kₜ
  ... | tri< k<kₜ _ _              = left  ( 𝒍𝒆𝒎𝒎𝒂∶lookup⟶∈ k tₗ lookup⟶ )
  ... | tri> _ _ kₜ<k              = right ( 𝒍𝒆𝒎𝒎𝒂∶lookup⟶∈ k tᵤ lookup⟶ )
  ... | tri≈ _ k≡kₜ _ rewrite k≡kₜ = here
 
  𝒍𝒆𝒎𝒎𝒂∶∈⟶lookup : ∀ { l u h } ( k : Key ) ( t : Tree l u h ) → k ∈ t → ∃ λ v → lookup k t ≡ just v
  𝒍𝒆𝒎𝒎𝒂∶∈⟶lookup _ ( leaf _ ) ()
  𝒍𝒆𝒎𝒎𝒂∶∈⟶lookup k ( node ._ _ _ ._ ) here with compare k k
  ... | tri< _ k≢k _ = contradiction refl k≢k
  ... | tri≈ _ refl _ = , refl
  ... | tri> _ k≢k _ = contradiction refl k≢k
  𝒍𝒆𝒎𝒎𝒂∶∈⟶lookup k ( node ( k' , _ ) tₗ _ ._ ) ( left k∈tₗ ) with compare k k'
  ... | tri< _ _ _ = 𝒍𝒆𝒎𝒎𝒂∶∈⟶lookup k tₗ k∈tₗ
  ... | tri≈ k≮k' _ _ = contradiction k<k' k≮k'
    where k<k' = proj₂ (𝒍𝒆𝒎𝒎𝒂∶∈⟶<< k∈tₗ)
  ... | tri> k≮k' _ _ = contradiction k<k' k≮k'
    where k<k' = proj₂ (𝒍𝒆𝒎𝒎𝒂∶∈⟶<< k∈tₗ)
  𝒍𝒆𝒎𝒎𝒂∶∈⟶lookup k ( node ( k' , _ ) _ tᵣ ._ ) ( right k∈tᵣ ) with compare k k'
  ... | tri< _ _ k≯k' = contradiction k'<k k≯k'
    where k'<k = proj₁ (𝒍𝒆𝒎𝒎𝒂∶∈⟶<< k∈tᵣ)
  ... | tri≈ _ _ k≯k' = contradiction k'<k k≯k'
    where k'<k = proj₁ (𝒍𝒆𝒎𝒎𝒂∶∈⟶<< k∈tᵣ)
  ... | tri> _ _ _ = 𝒍𝒆𝒎𝒎𝒂∶∈⟶lookup k tᵣ k∈tᵣ
 
  𝒍𝒆𝒎𝒎𝒂∶insertWith⟶∈ : ∀
                       { l u h }
                       ( k : Key )
                       ( v : Value k )
                       ( f : Value k → Value k → Value k )
                       ( t : Tree l u h )
                       ( l<k<u : l < k < u )
                       → k ∈ proj₂ (insertWith k v f t l<k<u)
  𝒍𝒆𝒎𝒎𝒂∶insertWith⟶∈ _ v _ (leaf _) _ = here
  𝒍𝒆𝒎𝒎𝒂∶insertWith⟶∈ k v f (node (kₜ , vₜ) tₗ tᵣ bal) (l<k , k<u) with compare k kₜ
  ... | tri< k<kₜ _ _ = 𝒍𝒆𝒎𝒎𝒂∶joinˡ⁺Is∈Invariant (insertWith k v f tₗ (l<k , k<kₜ))
                                           tᵣ
                                           bal
                                           (𝒍𝒆𝒎𝒎𝒂∶insertWith⟶∈ k v f tₗ (l<k , k<kₜ))
  ... | tri> _ _ kₜ<k = 𝒍𝒆𝒎𝒎𝒂∶joinʳ⁺Is∈Invariant tₗ
                                           (insertWith k v f tᵣ (kₜ<k , k<u))
                                           bal
                                           (𝒍𝒆𝒎𝒎𝒂∶insertWith⟶∈ k v f tᵣ (kₜ<k , k<u))
  ... | tri≈ _ k≡kₜ _ rewrite k≡kₜ = here
   
  {-
    lem : ∀ {lb ub hˡ hʳ h K′ n} {V : Value K′}
        {l : Tree lb [ K′ ] hˡ}
        {r : Tree [ K′ ] ub hʳ}
        {b : hˡ ∼ hʳ ⊔ h} →
        n ∈ node (K′ , V) l r b →
        (n ≯ K′ → n ≢ K′ → n ∈ l) × (n ≮ K′ → n ≢ K′ → n ∈ r)
    lem (here    V) = (λ _ eq → ⊥-elim (eq P.refl)) , (λ _ eq → ⊥-elim (eq P.refl))
    lem (left  x p) = (λ _ _ → p) , (λ ≮ _ → ⊥-elim (≮ x))
    lem (right x p) = (λ ≯ _ → ⊥-elim (≯ x)) , (λ _ _ → p)
   
    find : ∀ {h lb ub} n (m : Tree lb ub h) → Dec (n ∈ m)
    find n (leaf _) = no λ ()
    find n (node (k , v) l r _) with compare n k
    find n (node (k , v) l r _) | tri< a ¬b ¬c with find n l
    ... | yes p = yes (left a p)
    ... | no ¬p = no λ ¬∈l → ¬p (proj₁ (lem ¬∈l) ¬c ¬b)
    find n (node (k , v) l r _) | tri≈ ¬a b ¬c rewrite (P.sym b) = yes (here v)
    find n (node (k , v) l r _) | tri> ¬a ¬b c with find n r
    ... | yes p = yes (right c p)
    ... | no ¬p = no λ ¬∈r → ¬p (proj₂ (lem ¬∈r) ¬a ¬b)
  -}

  


  _∈?_ : ∀ { k⃖ k⃗ : Key⁺ } { h : ℕ.ℕ } ( k : Key ) ( t : Tree k⃖ k⃗ h ) → Dec ( k ∈ t )
  k ∈? leaf l<u = no {!!}
  k ∈? node k₁ t t₁ bal = {!!}

                     
  data _∼_∈̃_ { k⃖ k⃗ : Key⁺ } ( k : Key ) ( v : Value k ) {- ( k' : Key ) ⦃ _ : k ≡ k' ⦄ -} : ∀ { h : ℕ.ℕ } → Tree k⃖ k⃗ h → Set ( 𝑼⟨Key⟩ ⊔ 𝑼⟨Value⟩ ⊔ 𝑼⟨<⟩ ) where
  
    here : ∀
           { h⃖ h⃗ h }
           { t⃖ : Tree k⃖ [ k ] h⃖ }
           { t⃗ : Tree [ k ]  k⃗ h⃗ }
           { bal : h⃖ ∼ h⃗ ⊔ h }
           → k ∼ v ∈̃ node ( k , v ) t⃖ t⃗ bal
      
    left : ∀
           { h⃖ h⃗ h k′ } { v′ : Value k′ }
           { t⃖ : Tree k⃖ [ k′ ] h⃖ }
           { t⃗ : Tree [ k′ ]  k⃗ h⃗ }
           { bal : h⃖ ∼ h⃗ ⊔ h }
           → k ∼ v ∈̃ t⃖
           → k ∼ v ∈̃ node ( k′ , v′ ) t⃖ t⃗ bal
      
    right : ∀
            { h⃖ h⃗ h k′ } { v′ : Value k′ }
            { t⃖ : Tree k⃖ [ k′ ] h⃖ }
            { t⃗ : Tree [ k′ ] k⃗ h⃗ }
            { bal : h⃖ ∼ h⃗ ⊔ h }
            → k ∼ v ∈̃ t⃗
            → k ∼ v ∈̃ node ( k′ , v′ ) t⃖ t⃗ bal

  ∈→∼∈̃ : ∀ { k⃖ k⃗ } { k : Key } { h } { t : Tree k⃖ k⃗ h } → k ∈ t → ∃ λ ( v : Value k ) → k ∼ v ∈̃ t
  ∈→∼∈̃ ( here { v = v } ) = v , here
  ∈→∼∈̃ ( left k∈t⃖ ) = ( proj₁ ( ∈→∼∈̃ k∈t⃖ ) ) , left ( proj₂ ( ∈→∼∈̃ k∈t⃖ ) )
  ∈→∼∈̃ ( right k∈t⃗ ) = ( proj₁ ( ∈→∼∈̃ k∈t⃗ ) ) , right ( proj₂ ( ∈→∼∈̃ k∈t⃗ ) )

  ∼∈̃→∈ : ∀ { k⃖ k⃗ } { k : Key } { h } { t : Tree k⃖ k⃗ h } → { v : Value k } → k ∼ v ∈̃ t → k ∈ t
  ∼∈̃→∈ here = here
  ∼∈̃→∈ ( left k∼v∈̃t⃖ ) = left ( ∼∈̃→∈ k∼v∈̃t⃖ )
  ∼∈̃→∈ ( right k∼v∈̃t⃗ ) = right ( ∼∈̃→∈ k∼v∈̃t⃗ )

  open import Relation.Binary.PropositionalEquality

  _∈̃?_ : ∀ {l u h} → (k : Key) → ( t : Tree l u h ) → Dec ( ∃ λ ( v : Value k ) → k ∼ v ∈̃ t )
  _∈̃?_ k (leaf _)                  = no (λ x → {!!})
  _∈̃?_ k (node (k′ , v) lk′ k′u _) with compare k k′
  _∈̃?_ k (node (k′ , v) lk′ k′u _) | tri< _ _  _ with k ∈̃? lk′
  k ∈̃? node (k′ , v) lk′ k′u bal | tri< _ _ _ | yes p = yes {!!}
  k ∈̃? node (k′ , v) lk′ k′u bal | tri< _ _ _ | no ¬p = {!!}
  _∈̃?_ k (node (k′ , v) lk′ k′u _) | tri> _ _  _ = {!!}
  _∈̃?_ k (node (k′ , v) lk′ k′u _) | tri≈ _ eq _ rewrite eq = {!!}

{-
  _∈̃?_ : ∀ { k⃖ k⃗ : Key⁺ } { h : ℕ.ℕ } ( k : Key ) ( t : Tree k⃖ k⃗ h ) → Dec ( ∃ λ ( v : Value k ) → k ∼ v ∈̃ t )
  k ∈̃? t with lookup k t | inspect (lookup k) t
  k ∈̃? t | just x | [ e ] = yes ( x , proj₂ {!!}  ) -- proj₂ ( ∈→∼∈̃ ( 𝒍𝒆𝒎𝒎𝒂∶lookup⟶∈ k t ( x , e ) ) )
  k ∈̃? t | nothing | e = {!!}
-}
{-
  data theValueOfKey_is_inTheTree_ ( key : Key ) → ( value : Value key ) → ( tree : Tree k⃖ k⃗ h ) : Set where      
  ∀ { k⃖ k⃗ : Key⁺ } { h : ℕ.ℕ } { k : Key } { t : Tree k⃖ k⃗ h } → Dec ( k ∈ t ) → Maybe ( Value k )
-}

  [[_]] : ∀ { k⃖ k⃗ : Key⁺ } { h : ℕ.ℕ } { k : Key } { t : Tree k⃖ k⃗ h } → Dec ( k ∈ t ) → Maybe ( Value k )
  [[ yes k∈t ]] = just ( proj₁ ( ∈→∼∈̃ k∈t ) )
  [[ no k∉t ]] = nothing


open import Data.AVL Value isStrictTotalOrder
open import Data.Maybe
open import Relation.Binary

data _∈_ ( k : Key ) : Tree → Set ( 𝑼⟨Key⟩ ⊔ 𝑼⟨Value⟩ ⊔ 𝑼⟨<⟩ ) where

  _∈ᵢ_ : ∀ { h } → ( t : Indexed.Tree Extended-key.⊥⁺ Extended-key.⊤⁺ h ) → k Indexed.∈ t → k ∈ ( tree t )

_∈′_ : ( k : Key ) → Tree → Set ( 𝑼⟨Key⟩ ⊔ 𝑼⟨Value⟩ ⊔ 𝑼⟨<⟩ )
k ∈′ t = ∀ { h } → ( t : Indexed.Tree Extended-key.⊥⁺ Extended-key.⊤⁺ h ) → k Indexed.∈ t
{-
𝒍𝒆𝒎𝒎𝒂∶lookup⟶∈ : ∀ ( k : Key ) ( t : Tree ) → ( ∃ λ v → lookup k t ≡ just v ) → k ∈ t
𝒍𝒆𝒎𝒎𝒂∶lookup⟶∈ k (tree t) (v , lookup-k-t≡just-v) = {!k ∈ᵢ t!}

𝒍𝒆𝒎𝒎𝒂∶lookup⟶∈′ : ∀ ( k : Key ) ( t : Tree ) → ( ∃ λ v → lookup k t ≡ just v ) → k ∈′ t
𝒍𝒆𝒎𝒎𝒂∶lookup⟶∈′ = {!!}
-}
