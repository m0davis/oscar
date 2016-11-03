open import Level using (_⊔_; lift; Level)
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

module Match
  { α ℓ : Level }
  { a : Set α }
  { _<ᵃ_ : Rel a ℓ }
  { _≡ᶠ_ : Rel ( Free List a ) ℓ }
  ( isDecEquivalenceᶠ : IsDecEquivalence _≡ᶠ_ )
  ( isStrictTotalOrderᵃ : IsStrictTotalOrder _≡_ _<ᵃ_ )
  where

module Treeᵃ where

  open IsStrictTotalOrder isStrictTotalOrderᵃ
  open import Tree a isStrictTotalOrderᵃ
  open import Function

  reverseMap : Tree → Tree
  reverseMap = fromList ∘ Data.List.Base.map swap ∘ toList

module ∈ᵃ where

  open IsStrictTotalOrder isStrictTotalOrderᵃ using (_≟_)
  
  _∈ᵃ_ : a → List a → Bool
  x ∈ᵃ [] = false
  x ∈ᵃ (x₁ ∷ xs) with x ≟ x₁
  ... | yes _ = true
  ... | no _ = x ∈ᵃ xs

open ∈ᵃ

module AnyTree {xx} ( any : Set xx ) where
  open import Tree any isStrictTotalOrderᵃ public
   
module Treeᶠ where

  open import Tree ( Free List a ) isStrictTotalOrderᵃ

  match'expectation : Free List a → Free List a → Maybe Tree
  match'expectation pat exp with IsDecEquivalence._≟_ isDecEquivalenceᶠ pat exp
  match'expectation pat exp | yes p = just empty
  match'expectation pat exp | no ¬p = nothing
   
  match' : Free List a → Free List a → List a → Tree → Maybe Tree
  match' (pure x) m₂ vs bs with x ∈ᵃ vs
  match' (pure x) m₂ vs bs | true with lookup x bs
  match' (pure x) m₂ vs bs | true | just x₁ with match'expectation x₁ m₂
  match' (pure x₂) m₂ vs bs | true | just x₁ | just x = just x
  match' (pure x) m₂ vs bs | true | just x₁ | nothing = nothing
  match' (pure x) m₂ vs bs | true | nothing = just ( singleton x m₂ )
  match' (pure x) m₂ vs bs | false = match'expectation (pure x) m₂
  match' (free fpat (pat ∷ pats)) (free fexp (exp ∷ exps)) vs bs with match' (fpat pat) (fexp exp) vs bs
  match' (free fpat (pat ∷ pats)) (free fexp (exp ∷ exps)) vs bs | just mbs with match' (free fpat pats) (free fexp exps) vs (union mbs bs)
  match' (free fpat (pat ∷ pats)) (free fexp (exp ∷ exps)) vs bs | just mbs | just mbs' = just (union mbs mbs')
  match' (free fpat (pat ∷ pats)) (free fexp (exp ∷ exps)) vs bs | just mbs | nothing = nothing
  match' (free fpat (pat ∷ pats)) (free fexp (exp ∷ exps)) vs bs | nothing = nothing
  match' (free x₁ []) (free x₅ []) vs bs = just empty
  match' (free x₁ _) (free x₄ _) vs bs = nothing
  match' (free x₁ _) (pure _) vs bs = nothing
   
  match : Free List a →
          Free List a →
          List a →
          Maybe Tree
  match m₁ m₂ vs = match' m₁ m₂ vs empty
   
  open import Function

  open import Data.Sum

  sumList : ∀ { a b } { A : Set a } {B : Set b} → List A → List B → List (A ⊎ B)
  sumList as bs = Data.List.Base.map inj₁ as ++ Data.List.Base.map inj₂ bs 

  uF : List (Free List a) → Free List a
  uF [] = free (λ x → pure x) []
  uF (x ∷ xs) with uF xs
  uF (pure x ∷ _) | pure x' = free pure (x ∷ x' ∷ [])
  uF (free x₁ x₂ ∷ _) | pure x' = free ([_,_] x₁ pure) (sumList x₂ [ x' ])
  uF (pure x ∷ _) | free x₁ x₂ = free ([_,_] pure x₁) (sumList [ x ] x₂)
  uF (free f x ∷ _) | free f' x' = free ([_,_] f f') (sumList x x')

  mutual
  
    sublis : Tree → Free List a → Free List a
    sublis m (pure x₁) with lookup x₁ m
    sublis m (pure x₁) | just x = x
    sublis m (pure x₁) | nothing = pure x₁
    sublis m (free x₂ []) = free x₂ []
    sublis m (free fx (x ∷ xs)) with sublis m (fx x) | sublis' m fx xs
    sublis m (free fx (x₁ ∷ xs)) | s | s' = uF (s ∷ s')
   
    sublis' : ∀ { x } → Tree → (x → Free List a) → List x → List (Free List a)
    sublis' m fx [] = []
    sublis' m fx (x ∷ xs) with (fx x)
    sublis' m fx (x₁ ∷ xs) | pure x₂ with lookup x₂ m
    sublis' m fx (x₁ ∷ xs) | pure x₂ | just y = y ∷ sublis' m fx xs
    sublis' m fx (x₁ ∷ xs) | pure x₂ | nothing = pure x₂ ∷ sublis' m fx xs
    sublis' m f (_ ∷ xs) | free f' [] = free pure [] ∷ sublis' m f xs
    sublis' m f (x ∷ xs) | free f' xs' = uF (sublis m (f x) ∷ []) ∷ sublis' m f xs

  open Treeᵃ
  open import Data.Maybe.Base

  import Tree a isStrictTotalOrderᵃ as a

  pureMap : Tree → Maybe a.Tree
  pureMap m = (if null (AnyTree.toList _ f) then (just p) else nothing)
    where
      isPure : a × Free List a → Bool
      isPure (_ , pure _) = true
      isPure _ = false

      mapEither : ∀ {a' b} {A : Set a'} {B : Set b} → (Free List a → A ⊎ B) → Tree → AnyTree.Tree A × AnyTree.Tree B
      mapEither {A = A} {B = B} f t = mapEitherA f t , mapEitherB f t
        where
          mel : ∀ {a' b} {A : Set a'} {B : Set b} → (Free List a → A ⊎ B) → a × Free List a → a × (A ⊎ B)
          mel f (proj₁ , proj₂) = proj₁ , f proj₂
          
          mapEitherList : ∀ {a' b} {A : Set a'} {B : Set b} → (Free List a → A ⊎ B) → List (a × Free List a) → List (a × (A ⊎ B))
          mapEitherList f l = Data.List.Base.map (map2 f) l
            where
              map2 : ∀ {A'' B C} {a'' : Set A''} {b : Set B} {c : Set C} → (b → c) → a'' × b → a'' × c
              map2 f (proj₁ , proj₂) = proj₁ , (f proj₂)

          mapEitherA : ∀ {a' b} {A : Set a'} {B : Set b} → (Free List a → A ⊎ B) → Tree → AnyTree.Tree A
          mapEitherA {A = A} {B = B} f t = AnyTree.fromList A (gfilter (λ { (x , y) → Data.Maybe.map (λ z → x , z) (isInj₁ y) })
                                                                 (mapEitherList f (toList t)))

          mapEitherB : ∀ {a' b} {A : Set a'} {B : Set b} → (Free List a → A ⊎ B) → Tree → AnyTree.Tree B
          mapEitherB {A = A} {B = B} f t = AnyTree.fromList B (gfilter (λ { (x , y) → Data.Maybe.map (λ z → x , z) (isInj₂ y) })
                                                                 (mapEitherList f (toList t)))

      fp = mapEither cv m
        where
          cv : Free List a → ⊤ ⊎ a
          cv (pure x) = inj₂ x
          cv _ = inj₁ tt
      f = proj₁ fp
      p = proj₂ fp



  one-one-match : Free List a → Free List a → List a → List a → Maybe (a.Tree)
  one-one-match pat exp patv expv with match pat exp patv
  one-one-match pat exp patv expv | just (a.tree (a.Indexed.leaf l<u)) = just a.empty
  one-one-match pat exp patv expv | just m with isSubsequenceOf {ide = isDecEquivalenceᶠ} (elems m) (Data.List.Base.map pure expv)
  one-one-match pat exp patv expv | just m | true with pureMap m
  one-one-match pat exp patv expv | just m | true | nothing = nothing
  one-one-match pat exp patv expv | just _ | true | just m' with IsDecEquivalence._≟_ isDecEquivalenceᶠ pat
                (sublis ( ( AnyTree.fromList (Free List a) (Data.List.Base.map (λ { (a , a1) → a , pure a1 }) (AnyTree.toList a (reverseMap m') ) ) ) ) exp )
  one-one-match pat exp patv expv | just _ | true | just m' | yes _ = just m'
  one-one-match pat exp patv expv | just _ | true | just m' | no _ = nothing
  one-one-match pat exp patv expv | just m | false = nothing 
  one-one-match pat exp patv expv | nothing = nothing


  is-1-to-1 : AnyTree.Tree a → Set (ℓ ⊔ α)
  is-1-to-1 t = t ≡ reverseMap (reverseMap t)

  theorem : (fla1 : Free List a) → (fla2 : Free List a) → (l1 : List a) → (l2 : List a) → ((one-one-match fla1 fla2 l1 l2 ≡ nothing) ⊎ (∃ λ o → is-1-to-1 o × one-one-match fla1 fla2 l1 l2 ≡ just o))
  theorem fla1 fla2 l1 l2 with match fla1 fla2 l1
  theorem fla1 fla2 l1 l2 | just (tree (Indexed.leaf l<u)) = inj₂ (a.empty , (refl , refl))
  theorem fla1 fla2 l1 l2 | just m with isSubsequenceOf {ide = isDecEquivalenceᶠ} (elems m) (Data.List.Base.map pure l2)
  theorem fla1 fla2 l1 l2 | just m | true with pureMap m
  theorem fla1 fla2 l1 l2 | just m | true | just m' with IsDecEquivalence._≟_ isDecEquivalenceᶠ fla1
          (sublis ( ( AnyTree.fromList (Free List a) (Data.List.Base.map (λ { (a , a1) → a , pure a1 }) (AnyTree.toList a (reverseMap m') ) ) ) ) fla2 )
  theorem fla1 fla2 l1 l2 | just m | true | just m' | yes _ = {!!}
  theorem fla1 fla2 l1 l2 | just m | true | just m' | no _ = inj₁ {!!}
  theorem fla1 fla2 l1 l2 | just m | true | nothing = {!!}
  theorem fla1 fla2 l1 l2 | just m | false = inj₁ {!!}
  theorem fla1 fla2 l1 l2 | nothing = inj₁ refl
