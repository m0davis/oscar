module inconsistentrewrite where

data _≡_ {a} {A : Set a} (x : A) : A → Set a where
  refl : x ≡ x

{-# BUILTIN EQUALITY _≡_ #-}
{-# BUILTIN REFL refl #-}

module AVL-ish
  { 𝑼⟨Key⟩ 𝑼⟨Value⟩ }
  { Key : Set 𝑼⟨Key⟩ }
  ( Value : Key → Set 𝑼⟨Value⟩ )
  where

  open import Agda.Primitive using ( _⊔_ )
    
  record Σ {a b} (A : Set a) (B : A → Set b) : Set (a ⊔ b) where
    constructor _,_
    field
      proj₁ : A
      proj₂ : B proj₁
   
  open Σ
   
  KV : Set (𝑼⟨Key⟩ ⊔ 𝑼⟨Value⟩)
  KV = Σ Key Value

  data Tree : Set (𝑼⟨Key⟩ ⊔ 𝑼⟨Value⟩) where
    node : (k : KV) → Tree
           
  data _∼_∈_ ( k : Key ) ( v : Value k ) : Tree → Set ( 𝑼⟨Key⟩ ⊔ 𝑼⟨Value⟩ ) where
    here :  k ∼ v ∈ node ( k , v )
            
  postulate
    k₁≡k₂ : ∀ ( k₁ k₂ : Key ) → k₁ ≡ k₂
    ∈→v₁≡v₂ : ∀ { k } { v₁ v₂ : Value k } → k ∼ v₁ ∈ node ( k , v₂ ) → v₁ ≡ v₂

  lem : ( t₁ : Tree )
        ( t₂ : Tree )
        ( _ : ∀ {k} {v : Value k} → k ∼ v ∈ t₁ → k ∼ v ∈ t₂ )
        ( _ : ∀ {k} {v : Value k} → k ∼ v ∈ t₂ → k ∼ v ∈ t₁ ) →
        Set
  lem ( node ( k₁ , v₁ ) ) ( node ( k₂ , v₂ ) ) t₁→t₂ t₂→t₁ rewrite k₁≡k₂ k₁ k₂
       -- When the below lines are commented-out, then C-c C-, at goal 0 (below) reports the following types:
          {-
            t₂→t₁    : {k : Key} {v : Value k} →
                       k ∼ v ∈ node (k₂ , v₂) → k ∼ v ∈ node (k₂ , v₁)
            t₁→t₂    : {k : Key} {v : Value k} →
                       k ∼ v ∈ node (k₂ , v₁) → k ∼ v ∈ node (k₂ , v₂)
          -}
   
       -- However, uncommenting the below rewrite...
       -- | ∈→v₁≡v₂ (t₁→t₂ here) -- equivalent to v₂ ≡ v₁
       -- ... results in the following types being reported:
          {-
            t₂→t₁    : {k : Key} {v : Value k} →
                       k ∼ v ∈ node (k₂ , v₂) → k ∼ v ∈ node (k₂ , v₂)
            t₁→t₂    : {k : Key} {v : Value k} →
                       k ∼ v ∈ node (k₂ , v₁) → k ∼ v ∈ node (k₂ , v₂)
          -}
   
       -- The unexpected behavior here is that v₁ has been rewritten to v₂ in t₂→t₁ but not in t₁→t₂.
       = {!subst ? (∈→v₁≡v₂ (t₁→t₂ here)) t₁→t₂!}