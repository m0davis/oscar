    open import Data.Product
    open import Level
    open import Relation.Binary
    open import Relation.Binary.PropositionalEquality as P using (_≡_)

    module Data.AVL.Properties-Refuse
      {k v ℓ}
      {Key : Set k} (Value : Key → Set v)
      {_<_ : Rel Key ℓ}
      (isStrictTotalOrder : IsStrictTotalOrder P._≡_ _<_) where

      open import Data.AVL Value isStrictTotalOrder using (KV; module Extended-key; module Height-invariants; module Indexed)
      import Data.AVL Value isStrictTotalOrder as AVL
      open Extended-key                       
      open Height-invariants                  
      open Indexed                            

      open IsStrictTotalOrder isStrictTotalOrder

      data _∈_ {lb ub} (K : Key) : ∀ {n} → Tree lb ub n → Set (k ⊔ v ⊔ ℓ) where
        here : ∀ {hˡ hʳ} V
          {l : Tree lb [ K ] hˡ}
          {r : Tree [ K ] ub hʳ}
          {b : ∃ λ h → hˡ ∼ hʳ ⊔ h} →
          K ∈ node (K , V) l r (proj₂ b)
        left : ∀ {hˡ hʳ K′} {V : Value K′}
          {l : Tree lb [ K′ ] hˡ}
          {r : Tree [ K′ ] ub hʳ}
          {b : ∃ λ h → hˡ ∼ hʳ ⊔ h} →
          K < K′ →
          K ∈ l →
          K ∈ node (K′ , V) l r (proj₂ b)
        right : ∀ {hˡ hʳ K′} {V : Value K′}
          {l : Tree lb [ K′ ] hˡ}
          {r : Tree [ K′ ] ub hʳ}
          {b : ∃ λ h → hˡ ∼ hʳ ⊔ h} →
          K′ < K →
          K ∈ r →
          K ∈ node (K′ , V) l r (proj₂ b)

      -- here's the function prior to doing any case splitting
      refuse1 : ∀ {kₗ kᵤ h}
                ( t : Tree kₗ kᵤ h )
                ( k : Key )
                ( k∈t : k ∈ t ) →
                Set
      refuse1 = {!!}

      -- case-split, default
      refuse2 : ∀ {kₗ kᵤ h}
                ( t : Tree kₗ kᵤ h )
                ( k : Key )
                ( k∈t : k ∈ t ) →
                Set
      refuse2 t k₁ k∈t = {!!}

      -- case-split on t
      refuse3 : ∀ {kₗ kᵤ h}
                ( t : Tree kₗ kᵤ h )
                ( k : Key )
                ( k∈t : k ∈ t ) →
                Set
      refuse3 (leaf l<u) k₁ k∈t = {!!}
      refuse3 (node k₁ t t₁ bal) k₂ k∈t = {!!}

      -- case-split on bal
      refuse4 : ∀ {kₗ kᵤ h}
                ( t : Tree kₗ kᵤ h )
                ( k : Key )
                ( k∈t : k ∈ t ) →
                Set
      refuse4 (leaf l<u) k₁ k∈t = {!!}
      refuse4 (node k₁ t t₁ ∼+) k₂ k∈t = {!!}
      refuse4 (node k₁ t t₁ ∼0) k₂ k∈t = {!!}
      refuse4 (node k₁ t t₁ ∼-) k₂ k∈t = {!!}

{-
      -- case-split on k∈t of equation including (node ... ∼+)
      refuse5 : ∀ {kₗ kᵤ h}
                ( t : Tree kₗ kᵤ h )
                ( k : Key )
                ( k∈t : k ∈ t ) →
                Set
      refuse5 (leaf l<u) k₁ k∈t = {!!}
      refuse5 (node k₁ t t₁ ∼+) k₂ k∈t = {!k∈t!} -- oops, an error
      {- ERROR
        I'm not sure if there should be a case for the constructor here,
        because I get stuck when trying to solve the following unification
        problems (inferred index ≟ expected index):
          {_} ≟ {_}
          node (k₅ , V) l r (proj₂ b) ≟ node k₄
                                        t₂ t₃ ∼+
        when checking that the expression ? has type Set
      -}
      refuse5 (node k₁ t t₁ ∼0) k₂ k∈t = {!!}
      refuse5 (node k₁ t t₁ ∼-) k₂ k∈t = {!!}
-}
      -- Hmm... That didn't work. Maybe I need to follow Ulf's suggestion and case split on something else. Maybe by case splitting on something else, I'll be able to help Agda to solve the unification.
      -- This time, the case-split is done by hand, focused on the ∼+ line from refuse5, and includes many of the implicit variables.
{-
      open import Data.Nat.Base as ℕ

      refuse6 : ∀ {kₗ kᵤ h}
                ( t : Tree kₗ kᵤ h )
                ( k : Key )
                ( k∈t : k ∈ t ) →
                Set
      refuse6 {h = ℕ.suc .hˡ}
              (node (k , V) lk ku (∼+ {n = hˡ}))
              .k
              (here {hˡ = .hˡ} {hʳ = ℕ.suc .hˡ} .V {l = .lk} {r = .ku} {b = (ℕ.suc .hˡ , ∼+ {n = .hˡ})}) = {!!}
      {- ERROR
        Refuse to solve heterogeneous constraint proj₂ b :
        n AVL.Height-invariants.∼ hʳ ⊔ proj₁ b =?=
        .#Data.AVL-125146368.Height-invariants.∼+ :
        n AVL.Height-invariants.∼ ℕ.suc n ⊔ ℕ.suc n
        when checking that the pattern
        here {hˡ = .hˡ} {hʳ = ℕ.suc .hˡ} .V {l = .lk} {r = .ku}
          {b = ℕ.suc .hˡ , ∼+ {n = .hˡ}}
        has type
        k₂ ∈
        .#Data.AVL-125146368.Indexed.node (k₁ , V) lk ku
        .#Data.AVL-125146368.Height-invariants.∼+
      -}
      refuse6 _ _ _ = ?
-}
    
      data _inn_ {lb ub} (K : Key) : ∀ {n} → Tree lb ub n → Set (k ⊔ v ⊔ ℓ) where
        here : ∀ {hˡ hʳ} V
          {l : Tree lb [ K ] hˡ}
          {r : Tree [ K ] ub hʳ}
          {h : _}
          {b : hˡ ∼ hʳ ⊔ h} →
          K inn node (K , V) l r b
        left : ∀ {hˡ hʳ K′} {V : Value K′}
          {l : Tree lb [ K′ ] hˡ}
          {r : Tree [ K′ ] ub hʳ}
          {h : _} →
          {b : hˡ ∼ hʳ ⊔ h} →
          K < K′ →
          K inn l →
          K inn node (K′ , V) l r b
        right : ∀ {hˡ hʳ K′} {V : Value K′}
          {l : Tree lb [ K′ ] hˡ}
          {r : Tree [ K′ ] ub hʳ}
          {h : _} →
          {b : hˡ ∼ hʳ ⊔ h} →
          K′ < K →
          K inn r →
          K inn node (K′ , V) l r b

      view∈ : ∀ {lb ub n} {x : Key} {S : Tree lb ub n} → x ∈ S → x inn S
      view∈ (here V) = here V
      view∈ (left x₁ x₂) = left x₁ (view∈ x₂)
      view∈ (right x₁ x₂) = right x₁ (view∈ x₂)


      -- case-split on k∈t of equation including (node ... ∼+)
      refuse7 : ∀ {kₗ kᵤ h}
                ( t : Tree kₗ kᵤ h )
                ( k : Key )
                ( k∈t : k ∈ t ) →
                Set
      refuse7 (node (k , v) lk ku ∼+) k2 k∈t with view∈ k∈t
      refuse7 (node (k , v) lk ku ∼+) .k k∈t | here .v = {!!}
      refuse7 (node (k , v) lk ku ∼+) k2 k∈t | left k3 t3 = {!asdf!}
      refuse7 (node (k , v) lk ku ∼+) k2 k∈t | _ = {!asdf!}
      {- ERROR
        I'm not sure if there should be a case for the constructor here,
        because I get stuck when trying to solve the following unification
        problems (inferred index ≟ expected index):
          {_} ≟ {_}
          node (k₅ , V) l r (proj₂ b) ≟ node k₄
                                        t₂ t₃ ∼+
        when checking that the expression ? has type Set
      -}
      refuse7 _ _ _ = {!!}
