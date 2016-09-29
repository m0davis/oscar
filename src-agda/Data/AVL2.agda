{- Revision with emphasis on proofs -}

------------------------------------------------------------------------
-- The Agda standard library
--
-- AVL trees
------------------------------------------------------------------------

-- AVL trees are balanced binary search trees.

-- The search tree invariant is specified using the technique
-- described by Conor McBride in his talk "Pivotal pragmatism".

module Data.AVL2 where

module HEIGHT where
  open import Data.Fin using (Fin ; zero ; suc)
  open import Data.Nat.Base

  pattern 0# = zero
  pattern 1# = suc zero
  pattern ## = suc (suc ())
  
  infixl 6 _⊕_
    
  _⊕_ : Fin 2 → ℕ → ℕ
  0# ⊕ n = n
  1# ⊕ n = suc n
  ## ⊕ n

  _⊕_⊖1 : Fin 2 → ℕ → ℕ
  i ⊕ zero ⊖1 = zero
  i ⊕ suc n ⊖1 = i ⊕ n
 
  infix 4 _∼_⊔_
 
  -- If i ∼ j ⊔ m, then the difference between i and j is at most 1,
  -- and the maximum of i and j is m. _∼_⊔_ is used to record the
  -- balance factor of the AVL trees, and also to ensure that the
  -- absolute value of the balance factor is never more than 1.
 
  data _∼_⊔_ : ℕ → ℕ → ℕ → Set where
    ∼+ : ∀ {n} →     n ∼ 1 + n ⊔ 1 + n
    ∼0 : ∀ {n} →     n ∼ n     ⊔ n
    ∼- : ∀ {n} → 1 + n ∼ n     ⊔ 1 + n
 
  -- Some lemmas.
 
  max∼ : ∀ {i j m} → i ∼ j ⊔ m → m ∼ i ⊔ m
  max∼ ∼+ = ∼-
  max∼ ∼0 = ∼0
  max∼ ∼- = ∼0
 
  ∼max : ∀ {i j m} → i ∼ j ⊔ m → j ∼ m ⊔ m
  ∼max ∼+ = ∼0
  ∼max ∼0 = ∼0
  ∼max ∼- = ∼+


module ADDBOUNDS where

  data [_]⁺ {a} (A : Set a) : Set a where
    ⊥⁺  : [ A ]⁺
    [_] : (k : A) → [ A ]⁺
    ⊤⁺  : [ A ]⁺
   
  open import Relation.Binary
  open import Data.Unit
  open import Data.Empty
  open import Level using ( _⊔_ ; Lift ; lift )
  open Lift
   
  open StrictTotalOrder
 
  StrictTotalOrder⁺ : ∀ {a ℓ₁ ℓ₂} → StrictTotalOrder a ℓ₁ ℓ₂ → StrictTotalOrder a ℓ₁ ℓ₂
  StrictTotalOrder⁺ {a} {ℓ₁} {ℓ₂} sto = record { Carrier = [ Carrier sto ]⁺ ; _≈_ = _≈⁺_ ; _<_ = _<⁺_ ; isStrictTotalOrder = IsStrictTotalOrder⁺ } where
  
    _≈⁺_ : [ Carrier sto ]⁺ → [ Carrier sto ]⁺ → Set ℓ₁
    [ k ] ≈⁺ [ k₁ ] = (_≈_ sto k k₁)
    ⊥⁺ ≈⁺ ⊥⁺ = Lift ⊤
    ⊤⁺ ≈⁺ ⊤⁺ = Lift ⊤
    _  ≈⁺ _  = Lift ⊥

    _<⁺_ : [ Carrier sto ]⁺ → [ Carrier sto ]⁺ → Set ℓ₂
    ⊥⁺    <⁺ [ _ ] = Lift ⊤
    ⊥⁺    <⁺ ⊤⁺    = Lift ⊤
    [ x ] <⁺ [ y ] = _<_ sto x y
    [ _ ] <⁺ ⊤⁺    = Lift ⊤
    _     <⁺ _     = Lift ⊥

    IsStrictTotalOrder⁺ : IsStrictTotalOrder _≈⁺_ _<⁺_
    IsStrictTotalOrder⁺ = record { isEquivalence = IsEquivalence⁺ ; trans = λ {i} {j} {k} → trans⁺ {i} {j} {k} ; compare = compare⁺ ; <-resp-≈ = <-resp-≈⁺ } where
    
      IsEquivalence⁺ : IsEquivalence _≈⁺_
      IsEquivalence⁺ = record { refl = λ {x} → refl⁺ {x} ; sym = λ {i} {j} → sym⁺ {i} {j} ; trans = λ {i} {j} {k} → trans⁺ {i} {j} {k} } where
     
        refl⁺ : Reflexive _≈⁺_
        refl⁺ {⊥⁺} = lift tt
        refl⁺ {⊤⁺} = lift tt
        refl⁺ {[ k ]} = Eq.refl sto
     
        sym⁺ : Symmetric _≈⁺_
        sym⁺ {⊥⁺}    {⊥⁺}    _         = lift tt
        sym⁺ {⊥⁺}    {[ _ ]} (lift ())
        sym⁺ {⊥⁺}    {⊤⁺}    (lift ())
        sym⁺ {[ _ ]} {⊥⁺}    (lift ())
        sym⁺ {[ _ ]} {[ _ ]}           = Eq.sym sto
        sym⁺ {[ _ ]} {⊤⁺}    (lift ())
        sym⁺ {⊤⁺}    {⊥⁺}    (lift ())
        sym⁺ {⊤⁺}    {[ _ ]} (lift ())
        sym⁺ {⊤⁺}    {⊤⁺}    _         = lift tt
     
        trans⁺ : Transitive _≈⁺_
        trans⁺ {⊥⁺}     {⊥⁺}        {⊥⁺}      _         _         = lift tt
        trans⁺ {⊥⁺}     {[ _ ]}               (lift ())
        trans⁺ {⊥⁺}     {⊤⁺}                  (lift ())
        trans⁺ {[ _ ]}  {⊥⁺}                  (lift ())
        trans⁺ {[ _ ]}  {[ _ ]} {[ _ ]}                           = Eq.trans sto
        trans⁺ {[ _ ]}  {⊤⁺}                  (lift ())
        trans⁺ {⊤⁺}     {⊥⁺}                  (lift ())
        trans⁺ {⊤⁺}     {[ _ ]}               (lift ())
        trans⁺ {⊤⁺}     {⊤⁺}        {⊤⁺}      _         _         = lift tt
        trans⁺          {j = ⊥⁺}    {[ _ ]}   _         (lift ())
        trans⁺          {j = ⊥⁺}    {⊤⁺}      _         (lift ())
        trans⁺          {j = [ _ ]} {⊥⁺}      _         (lift ())
        trans⁺          {j = [ _ ]} {⊤⁺}      _         (lift ())
        trans⁺          {j = ⊤⁺}    {⊥⁺}      _         (lift ())
        trans⁺          {j = ⊤⁺}    {[ _ ]}   _         (lift ())

    
      trans⁺ : Transitive _<⁺_
      trans⁺ {⊥⁺}    {⊥⁺}                    (lift ())
      trans⁺ {⊥⁺}    {[ _ ]}     {[ _ ]}     _         _         = lift tt
      trans⁺ {⊥⁺}    {[ _ ]}     {⊤⁺}        _         _         = lift tt
      trans⁺ {[ _ ]} {⊥⁺}                    (lift ())
      trans⁺ {[ _ ]} {[ _ ]}     {[ _ ]} = trans sto
      trans⁺ {[ _ ]} {[ _ ]}     {⊤⁺}        _         _         = lift tt
      trans⁺ {⊤⁺}    (lift ())
      trans⁺         {j = [ _ ]} {⊥⁺} _                (lift ())
      trans⁺         {j = ⊤⁺}    {⊥⁺}        _         (lift ())
      trans⁺         {j = ⊤⁺}    {[ _ ]}     _         (lift ())
      trans⁺         {j = ⊤⁺}    {⊤⁺}        _         (lift ())
   
      compare⁺ : Trichotomous _≈⁺_ _<⁺_
      compare⁺ ⊥⁺ ⊥⁺    = tri≈ lower     (lift tt) lower
      compare⁺ ⊥⁺ [ _ ] = tri< (lift tt) lower     lower
      compare⁺ ⊥⁺ ⊤⁺    = tri< (lift tt) lower     lower
      compare⁺ [ _ ] ⊥⁺ = tri> lower     lower     (lift tt)
      compare⁺ [ x ] [ y ] = compare sto x y
      compare⁺ [ _ ] ⊤⁺ = tri< (lift tt) lower     lower
      compare⁺ ⊤⁺ ⊥⁺    = tri> lower     lower     (lift tt)
      compare⁺ ⊤⁺ [ _ ] = tri> lower     lower     (lift tt)
      compare⁺ ⊤⁺ ⊤⁺    = tri≈ lower     (lift tt) lower
   
      open import Data.Product
   
      <-resp-≈⁺ : _<⁺_ Respects₂ _≈⁺_
      proj₁ <-resp-≈⁺ {x}     {⊥⁺}    {[ k ]} (lift ())
      proj₁ <-resp-≈⁺ {x}     {⊥⁺}    {⊤⁺}    (lift ())
      proj₁ <-resp-≈⁺ {x}     {[ k ]} {⊥⁺}    (lift ())
      proj₁ <-resp-≈⁺ {x}     {[ k ]} {⊤⁺}    (lift ())
      proj₁ <-resp-≈⁺ {x}     {⊤⁺}    {⊥⁺}    (lift ())
      proj₁ <-resp-≈⁺ {x}     {⊤⁺}    {[ k ]} (lift ())
      proj₁ <-resp-≈⁺ {x}     {⊥⁺}    {⊥⁺}    y=z       x<y = x<y
      proj₁ <-resp-≈⁺ {x}     {⊤⁺}    {⊤⁺}    y=z       x<y = x<y
      proj₁ <-resp-≈⁺ {⊥⁺}    {[ y ]} {[ z ]} y=z       x<y = x<y
      proj₁ <-resp-≈⁺ {⊤⁺}    {[ y ]} {[ z ]} y=z       x<y = x<y
      proj₁ <-resp-≈⁺ {[ x ]} {[ y ]} {[ z ]}                     = proj₁ (<-resp-≈ sto) {x} {y} {z}
      proj₂ <-resp-≈⁺ {x}     {⊥⁺}    {[ k ]} (lift ())
      proj₂ <-resp-≈⁺ {x}     {⊥⁺}    {⊤⁺}    (lift ())
      proj₂ <-resp-≈⁺ {x}     {[ k ]} {⊥⁺}    (lift ())
      proj₂ <-resp-≈⁺ {x}     {[ k ]} {⊤⁺}    (lift ())
      proj₂ <-resp-≈⁺ {x}     {⊤⁺}    {⊥⁺}    (lift ())
      proj₂ <-resp-≈⁺ {x}     {⊤⁺}    {[ k ]} (lift ())
      proj₂ <-resp-≈⁺ {x}     {⊥⁺}    {⊥⁺}    y=z       y<x = y<x
      proj₂ <-resp-≈⁺ {⊥⁺}    {[ y ]} {[ z ]} y=z       y<x = y<x
      proj₂ <-resp-≈⁺ {⊤⁺}    {[ y ]} {[ z ]} y=z       y<x = y<x
      proj₂ <-resp-≈⁺ {x}     {⊤⁺}    {⊤⁺}    y=z       y<x = y<x
      proj₂ <-resp-≈⁺ {[ x ]} {[ y ]} {[ z ]}                     = proj₂ (<-resp-≈ sto) {x} {y} {z}

  
  open import Relation.Binary.Core using (_≡_ ; refl)
  open import Data.Product

  IsStrictTotalOrder⁺ : ∀ {a ℓ₂} {A : Set a} {_<_ : Rel A ℓ₂} → IsStrictTotalOrder _≡_ _<_ → ∃ λ (_<⁺_ : Rel [ A ]⁺ ℓ₂) →  IsStrictTotalOrder _≡_ _<⁺_
  IsStrictTotalOrder⁺ {ℓ₂ = ℓ₂} {A = A} {_<_} isto = _<⁺_ , record { isEquivalence = IsEquivalence⁺ ; trans = λ {i} {j} {k} → trans⁺ {i} {j} {k} ; compare = compare⁺ ; <-resp-≈ = <-resp-≈⁺ } where

    IsEquivalence⁺ : IsEquivalence _≡_
    IsEquivalence⁺ = record { refl = refl ; sym = sym⁺ ; trans = trans⁺ } where
      sym⁺ : Symmetric _≡_
      sym⁺ refl = refl

      trans⁺ : Transitive _≡_
      trans⁺ refl refl = refl

    _<⁺_ : [ A ]⁺ → [ A ]⁺ → Set ℓ₂
    ⊥⁺    <⁺ [ _ ] = Lift ⊤
    ⊥⁺    <⁺ ⊤⁺    = Lift ⊤
    [ x ] <⁺ [ y ] = _<_ x y
    [ _ ] <⁺ ⊤⁺    = Lift ⊤
    _     <⁺ _     = Lift ⊥
  
    trans⁺ : Transitive _<⁺_
    trans⁺ {⊥⁺}    {⊥⁺}                    (lift ())
    trans⁺ {⊥⁺}    {[ _ ]}     {[ _ ]}     _         _         = lift tt
    trans⁺ {⊥⁺}    {[ _ ]}     {⊤⁺}        _         _         = lift tt
    trans⁺ {[ _ ]} {⊥⁺}                    (lift ())
    trans⁺ {[ _ ]} {[ _ ]}     {[ _ ]} = IsStrictTotalOrder.trans isto
    trans⁺ {[ _ ]} {[ _ ]}     {⊤⁺}        _         _         = lift tt
    trans⁺ {⊤⁺}    (lift ())
    trans⁺         {j = [ _ ]} {⊥⁺} _                (lift ())
    trans⁺         {j = ⊤⁺}    {⊥⁺}        _         (lift ())
    trans⁺         {j = ⊤⁺}    {[ _ ]}     _         (lift ())
    trans⁺         {j = ⊤⁺}    {⊤⁺}        _         (lift ())

    liftit : ∀ {a} {A : Set a} {x y : A} → x ≡ y → [ x ] ≡ [ y ]
    liftit {a} {A₁} {x} {.x} refl = refl

    liftit2 : ∀ {a} {A : Set a} {x y : A} → [ x ] ≡ [ y ] → x ≡ y
    liftit2 {a} {A₁} {x} {.x} refl = refl

    open import Relation.Nullary.Negation

    compare⁺ : Trichotomous _≡_ _<⁺_
    compare⁺ ⊥⁺ ⊥⁺    = tri≈ lower     refl   lower
    compare⁺ ⊥⁺ [ _ ] = tri< (lift tt) (λ ()) lower
    compare⁺ ⊥⁺ ⊤⁺    = tri< (lift tt) (λ ()) lower
    compare⁺ [ _ ] ⊥⁺ = tri> lower     (λ ()) (lift tt)
    compare⁺ [ x ] [ y ] with IsStrictTotalOrder.compare isto x y
    compare⁺ [ x ] [ y ] | tri< a ¬b ¬c = tri< a (contraposition (liftit2 {A = A}) ¬b) ¬c
    compare⁺ [ x ] [ y ] | tri≈ ¬a b ¬c rewrite b = tri≈ ¬a refl ¬c
    compare⁺ [ x ] [ y ] | tri> ¬a ¬b c = tri> ¬a (contraposition (liftit2 {A = A}) ¬b) c
    compare⁺ [ _ ] ⊤⁺ = tri< (lift tt) (λ ()) lower
    compare⁺ ⊤⁺ ⊥⁺    = tri> lower     (λ ()) (lift tt)
    compare⁺ ⊤⁺ [ _ ] = tri> lower     (λ ()) (lift tt)
    compare⁺ ⊤⁺ ⊤⁺    = tri≈ lower     refl   lower
 
    open import Data.Product
 
    <-resp-≈⁺ : _<⁺_ Respects₂ _≡_
    proj₁ <-resp-≈⁺ {x}     {⊥⁺}    {[ k ]} ()
    proj₁ <-resp-≈⁺ {x}     {⊥⁺}    {⊤⁺}    ()
    proj₁ <-resp-≈⁺ {x}     {[ k ]} {⊥⁺}    ()
    proj₁ <-resp-≈⁺ {x}     {[ k ]} {⊤⁺}    ()
    proj₁ <-resp-≈⁺ {x}     {⊤⁺}    {⊥⁺}    ()
    proj₁ <-resp-≈⁺ {x}     {⊤⁺}    {[ k ]} ()
    proj₁ <-resp-≈⁺ {x}     {⊥⁺}    {⊥⁺}    y=z       x<y = x<y
    proj₁ <-resp-≈⁺ {x}     {⊤⁺}    {⊤⁺}    y=z       x<y = x<y
    proj₁ <-resp-≈⁺ {⊥⁺}    {[ y ]} {[ z ]} y=z       x<y = x<y
    proj₁ <-resp-≈⁺ {⊤⁺}    {[ y ]} {[ z ]} y=z       x<y = x<y
    proj₁ <-resp-≈⁺ {[ x ]} {[ y ]} {[ z ]} y=z       x<y rewrite liftit2 y=z = x<y
    proj₂ <-resp-≈⁺ {x}     {⊥⁺}    {[ k ]} ()
    proj₂ <-resp-≈⁺ {x}     {⊥⁺}    {⊤⁺}    ()
    proj₂ <-resp-≈⁺ {x}     {[ k ]} {⊥⁺}    ()
    proj₂ <-resp-≈⁺ {x}     {[ k ]} {⊤⁺}    ()
    proj₂ <-resp-≈⁺ {x}     {⊤⁺}    {⊥⁺}    ()
    proj₂ <-resp-≈⁺ {x}     {⊤⁺}    {[ k ]} ()
    proj₂ <-resp-≈⁺ {x}     {⊥⁺}    {⊥⁺}    y=z       y<x = y<x
    proj₂ <-resp-≈⁺ {⊥⁺}    {[ y ]} {[ z ]} y=z       y<x = y<x
    proj₂ <-resp-≈⁺ {⊤⁺}    {[ y ]} {[ z ]} y=z       y<x = y<x
    proj₂ <-resp-≈⁺ {x}     {⊤⁺}    {⊤⁺}    y=z       y<x = y<x
    proj₂ <-resp-≈⁺ {[ x ]} {[ y ]} {[ z ]} y=z       x<y rewrite liftit2 y=z = x<y

open import Relation.Binary
open import Data.Product
open import Relation.Binary.PropositionalEquality
      
module TREE (let open StrictTotalOrder)
  {𝑼⟨Key⟩ 𝑼⟨≈⟩ 𝑼⟨<⟩ 𝑼⟨Value⟩}
  (strictTotalOrder : StrictTotalOrder 𝑼⟨Key⟩ 𝑼⟨≈⟩ 𝑼⟨<⟩)
  (Value : Carrier strictTotalOrder → Set 𝑼⟨Value⟩)
  (lemma= : ∀ {k k'} → StrictTotalOrder._≈_ strictTotalOrder k k' → k ≡ k')
  where

  open import Level using ( _⊔_ ; Lift ; lift )
  open import Data.Product

  Key : Set 𝑼⟨Key⟩
  Key = Carrier strictTotalOrder

  KV : Set (𝑼⟨Key⟩ ⊔ 𝑼⟨Value⟩)
  KV = Σ Key Value
  
  open ADDBOUNDS
  open HEIGHT

  open import Data.Nat.Base hiding (_⊔_)

  open StrictTotalOrder (StrictTotalOrder⁺ strictTotalOrder) renaming (_<_ to _<⁺_) using ()
  open StrictTotalOrder strictTotalOrder


  data Tree (l u : [ Key ]⁺) : ℕ → Set (𝑼⟨Key⟩ ⊔ 𝑼⟨Value⟩ ⊔ 𝑼⟨<⟩) where
    leaf : (l<u : l <⁺ u) → Tree l u 0
    node : ∀ {hˡ hʳ h}
           (k : KV)
           (lk : Tree l [ proj₁ k ] hˡ)
           (ku : Tree [ proj₁ k ] u hʳ)
           (bal : hˡ ∼ hʳ ⊔ h) →
           Tree l u (suc h)

  open import Relation.Binary.PropositionalEquality as P using (_≡_ ; sym)

  Tree<* : (<k : [ Key ]⁺) → (kv : KV) → (h : ℕ) → (∃! _≡_ (λ s → s ≡ (Tree <k [ proj₁ kv ] h)))
  Tree<* <k (k , _) h = Tree <k [ k ] h , _≡_.refl , sym
 
  Tree< : [ Key ]⁺ → KV → ℕ → Set ( 𝑼⟨Key⟩ ⊔ 𝑼⟨Value⟩ ⊔ 𝑼⟨<⟩ )
  Tree< <k (k , _) h = Tree <k [ k ] h
 
  Tree> : ∀ (kv : KV) → (>k : [ Key ]⁺) → (h : ℕ) → Set ( 𝑼⟨Key⟩ ⊔ 𝑼⟨Value⟩ ⊔ 𝑼⟨<⟩ )
  Tree> (k , _) >k h = Tree [ k ] >k h
 
  data _∈_ { <k >k } ( kv : KV ) : ∀ { h } → Tree <k >k h → Set ( 𝑼⟨Key⟩ ⊔ 𝑼⟨Value⟩ ⊔ 𝑼⟨<⟩ ) where
    here : ∀
           { <h >h h }
           { <t : Tree< <k kv <h }
           { >t : Tree> kv >k >h }
           { bal : <h ∼ >h ⊔ h }
           → kv ∈ node kv <t >t bal
    left : ∀
           { <h >h h k′ } { v′ : Value k′ }
           { <t : Tree <k [ k′ ] <h }
           { >t : Tree [ k′ ]  >k >h }
           { bal : <h ∼ >h ⊔ h }
           → kv ∈ <t
           → kv ∈ node ( k′ , v′ ) <t >t bal
    right : ∀
            { <h >h h k′ } { v′ : Value k′ }
            { <t : Tree <k [ k′ ] <h }
            { >t : Tree [ k′ ] >k >h }
            { bal : <h ∼ >h ⊔ h }
            → kv ∈ >t
            → kv ∈ node ( k′ , v′ ) <t >t bal

  open import Data.Empty
  open import Relation.Nullary
  open import Relation.Nullary.Negation
  open import Relation.Binary.Consequences

  open StrictTotalOrder strictTotalOrder renaming (_<_ to _<̇_ ; _≈_ to _≈̇_)

  ∈⟶<⁺ : ∀ {k} {v : Value k} {l u} {h} {t : Tree l u h}
         → (k , v) ∈ t → (l <⁺ [ k ]) × ([ k ] <⁺ u)
  ∈⟶<⁺ = {!!}
  
  low : ∀ {k k'} → [ k ] <⁺ [ k' ] → k <̇ k'
  low {k} {k'} x = x
  

  <∈ : ∀ {k k'} {v : Value k} {v' : Value k'} {l u} {hl hu} {h} {lk : Tree l [ k' ] hl} {ku : Tree [ k' ] u hu} {bal : hl ∼ hu ⊔ h}
         → k <̇ k' → (k , v) ∈ node (k' , v') lk ku bal → (k , v) ∈ lk
  <∈ x here = ⊥-elim (tri⟶asym (StrictTotalOrder.compare strictTotalOrder) x x)
    where
      open StrictTotalOrder strictTotalOrder
  <∈ x (left x₁) = x₁
  <∈ x (right x₁) = let bound = proj₁ (∈⟶<⁺ x₁) in ⊥-elim
                                                     (tri⟶asym (StrictTotalOrder.compare strictTotalOrder) x
                                                      (low bound))
    where
      
      open StrictTotalOrder strictTotalOrder

  tri∈ : ∀ {k k'} {v : Value k} {v' : Value k'} {l u} {hl hu} {h} {lk : Tree l [ k' ] hl} {ku : Tree [ k' ] u hu} {bal : hl ∼ hu ⊔ h}
               → (k , v) ∈ node (k' , v') lk ku bal → Tri ((k , v) ∈ lk) ((k , v) ≡ (k' , v')) ((k , v) ∈ ku)
  tri∈ here = tri≈ {!!} refl {!!}
  tri∈ (left x) = tri< x {!!} {!!}
  tri∈ (right x) = tri> {!!} {!!} x
{-
  tri<⟶tri∈ : ∀ {k k'} {v : Value k} {v' : Value k'} {l u} {hl hu} {h} {lk : Tree l [ k' ] hl} {ku : Tree [ k' ] u hu} {bal : hl ∼ hu ⊔ h}
               → Tri (k <̇ k') (k ≈̇ k') (k' <̇ k') → (k , v) ∈ node (k' , v') lk ku bal → Tri ((k , v) ∈ lk) ((k , v) ≡ (k' , v')) ((k , v) ∈ ku)
  tri<⟶tri∈ (tri< a ¬b ¬c) here = {!!}
  tri<⟶tri∈ (tri< a ¬b ¬c) (left x₁) = {!!}
  tri<⟶tri∈ (tri< a ¬b ¬c) (right x₁) = {!!}
  tri<⟶tri∈ (tri≈ ¬a b ¬c) here rewrite lemma= b = tri≈ {!!} refl {!!}
  tri<⟶tri∈ (tri≈ ¬a b ¬c) (left x₁) = {!!}
  tri<⟶tri∈ (tri≈ ¬a b ¬c) (right x₁) = {!!}
  tri<⟶tri∈ (tri> ¬a ¬b c) here = {!!}
  tri<⟶tri∈ (tri> ¬a ¬b c) (left x₁) = {!!}
  tri<⟶tri∈ (tri> ¬a ¬b c) (right x₁) = {!!}
-}

  _∈?_ : ∀ {l u h} → (k : Key) → (t : Tree l u h) → Dec (∃ λ v → (k , v) ∈ t)
  k ∈? leaf l<u = no (λ {(_ , ())})
  k ∈? node (k' , v') _ _ _ with StrictTotalOrder.compare strictTotalOrder k k'
  k ∈? node (k' , v') lk ku bal | tri< a ¬b ¬c with k ∈? lk
  k ∈? node (k' , v') lk ku bal | tri< a ¬b ¬c | yes (proj₁ , proj₂) = yes (proj₁ , left proj₂)
  k ∈? node (k' , v') lk ku bal | tri< k<k' ¬b ¬c | no ¬∃v-kv∈lk = no (∀¬⟶¬∃ (λ v kv∈t → ¬∃v-kv∈lk (v , <∈ k<k' kv∈t)))
  k ∈? node (k' , v') lk ku bal | tri≈ ¬a b ¬c rewrite lemma= b = yes (v' , here)
  k ∈? node (k' , v') lk ku bal | tri> ¬a ¬b c with k ∈? ku
  k ∈? node (k' , v') lk ku bal | tri> ¬a ¬b c | yes (proj₁ , proj₂) = yes (proj₁ , right proj₂)
  k ∈? node (k' , v') lk ku bal | tri> ¬a ¬b c | no ¬p = {!!}

  

  singleton : ∀ {l u} → (k : Key) → (v : Value k) → ∃! _≡_ λ (t : Tree l u 1) → (k , v) ∈ t × (∀ k' → (v' : Value k') → (k' , v') ∈ t → (k' , v') ≡ (k , v))
  singleton k v = (node (k , v) (leaf {!!}) (leaf {!!}) ∼0) , {!!}

{-      
  infix 4 _<⁺_
   
  _<⁺_ : Key⁺ → Key⁺ → Set 𝑼⟨<⟩
  ⊥⁺    <⁺ [ _ ] = Lift ⊤
  ⊥⁺    <⁺ ⊤⁺    = Lift ⊤
  [ x ] <⁺ [ y ] = x < y
  [ _ ] <⁺ ⊤⁺    = Lift ⊤
  _     <⁺ _     = Lift ⊥
   
  -- A pair of ordering constraints.
   
  infix 4 _<_<_
   
  _<_<_ : Key⁺ → Key → Key⁺ → Set 𝑼⟨<⟩
  l < x < u = l <⁺ [ x ] × [ x ] <⁺ u
   
  -- _<⁺_ is transitive.
   
  trans⁺ : ∀ l {m u} → l <⁺ m → m <⁺ u → l <⁺ u
   
  trans⁺ [ l ] {m = [ m ]} {u = [ u ]} l<m m<u = trans l<m m<u
   
  trans⁺ ⊥⁺    {u = [ _ ]} _ _ = _
  trans⁺ ⊥⁺    {u = ⊤⁺}    _ _ = _
  trans⁺ [ _ ] {u = ⊤⁺}    _ _ = _
   
  trans⁺ _     {m = ⊥⁺}    {u = ⊥⁺}    _ (lift ())
  trans⁺ _     {m = [ _ ]} {u = ⊥⁺}    _ (lift ())
  trans⁺ _     {m = ⊤⁺}    {u = ⊥⁺}    _ (lift ())
  trans⁺ [ _ ] {m = ⊥⁺}    {u = [ _ ]} (lift ()) _
  trans⁺ [ _ ] {m = ⊤⁺}    {u = [ _ ]} _ (lift ())
  trans⁺ ⊤⁺    {m = ⊥⁺}                (lift ()) _
  trans⁺ ⊤⁺    {m = [ _ ]}             (lift ()) _
  trans⁺ ⊤⁺    {m = ⊤⁺}                (lift ()) _
  -}

{-
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as P using (_≡_ ; sym)

module SUB
  {𝑼⟨Key⟩ 𝑼⟨Value⟩ 𝑼⟨<⟩}
  {Key : Set 𝑼⟨Key⟩} (Value : Key → Set 𝑼⟨Value⟩)
  {_<_ : Rel Key 𝑼⟨<⟩}
  (isStrictTotalOrder : IsStrictTotalOrder _≡_ _<_)
  where

  open import Data.Bool.Base using (Bool)
  import Data.DifferenceList as DiffList
  open import Data.Empty
  open import Data.List.Base as List using (List)
  open import Data.Maybe.Base hiding (map)
  open import Data.Nat.Base hiding (_<_; _⊔_ ; compare)
  open import Data.Product hiding (map)
  open import Data.Unit
  open import Function
  open import Level using (_⊔_; Lift; lift)
   
  open IsStrictTotalOrder isStrictTotalOrder
   
  ------------------------------------------------------------------------
  -- Extended keys
   
  module Extended-key where
   
    -- The key type extended with a new minimum and maximum.
   
    data Key⁺ : Set 𝑼⟨Key⟩ where
      ⊥⁺ ⊤⁺ : Key⁺
      [_]   : (k : Key) → Key⁺
   
    -- An extended strict ordering relation.
   
    infix 4 _<⁺_
   
    _<⁺_ : Key⁺ → Key⁺ → Set 𝑼⟨<⟩
    ⊥⁺    <⁺ [ _ ] = Lift ⊤
    ⊥⁺    <⁺ ⊤⁺    = Lift ⊤
    [ x ] <⁺ [ y ] = x < y
    [ _ ] <⁺ ⊤⁺    = Lift ⊤
    _     <⁺ _     = Lift ⊥
   
    -- A pair of ordering constraints.
   
    infix 4 _<_<_
   
    _<_<_ : Key⁺ → Key → Key⁺ → Set 𝑼⟨<⟩
    l < x < u = l <⁺ [ x ] × [ x ] <⁺ u
   
    -- _<⁺_ is transitive.
   
    trans⁺ : ∀ l {m u} → l <⁺ m → m <⁺ u → l <⁺ u
   
    trans⁺ [ l ] {m = [ m ]} {u = [ u ]} l<m m<u = trans l<m m<u
   
    trans⁺ ⊥⁺    {u = [ _ ]} _ _ = _
    trans⁺ ⊥⁺    {u = ⊤⁺}    _ _ = _
    trans⁺ [ _ ] {u = ⊤⁺}    _ _ = _
   
    trans⁺ _     {m = ⊥⁺}    {u = ⊥⁺}    _ (lift ())
    trans⁺ _     {m = [ _ ]} {u = ⊥⁺}    _ (lift ())
    trans⁺ _     {m = ⊤⁺}    {u = ⊥⁺}    _ (lift ())
    trans⁺ [ _ ] {m = ⊥⁺}    {u = [ _ ]} (lift ()) _
    trans⁺ [ _ ] {m = ⊤⁺}    {u = [ _ ]} _ (lift ())
    trans⁺ ⊤⁺    {m = ⊥⁺}                (lift ()) _
    trans⁺ ⊤⁺    {m = [ _ ]}             (lift ()) _
    trans⁺ ⊤⁺    {m = ⊤⁺}                (lift ()) _
   
  ------------------------------------------------------------------------
  -- Types and functions which are used to keep track of height
  -- invariants
   
  module Height-invariants where
   
    -- Bits. (I would use Fin 2 instead if Agda had "defined patterns",
    -- so that I could pattern match on 1# instead of suc zero; the text
    -- "suc zero" takes up a lot more space.)
   
    data ℕ₂ : Set where
      0# : ℕ₂
      1# : ℕ₂
   
    -- Addition.
   
    infixl 6 _⊕_
   
    _⊕_ : ℕ₂ → ℕ → ℕ
    0# ⊕ n = n
    1# ⊕ n = 1 + n
   
    -- i ⊕ n -1 = pred (i ⊕ n).
   
    _⊕_─1 : ℕ₂ → ℕ → ℕ
    i ⊕ zero  ─1 = 0
    i ⊕ suc n ─1 = i ⊕ n
   
    infix 4 _∼_⊔_
   
    -- If i ∼ j ⊔ m, then the difference between i and j is at most 1,
    -- and the maximum of i and j is m. _∼_⊔_ is used to record the
    -- balance factor of the AVL trees, and also to ensure that the
    -- absolute value of the balance factor is never more than 1.
   
    data _∼_⊔_ : ℕ → ℕ → ℕ → Set where
      ∼+ : ∀ {n} →     n ∼ 1 + n ⊔ 1 + n
      ∼0 : ∀ {n} →     n ∼ n     ⊔ n
      ∼- : ∀ {n} → 1 + n ∼ n     ⊔ 1 + n
   
    -- Some lemmas.
   
    max∼ : ∀ {i j m} → i ∼ j ⊔ m → m ∼ i ⊔ m
    max∼ ∼+ = ∼-
    max∼ ∼0 = ∼0
    max∼ ∼- = ∼0
   
    ∼max : ∀ {i j m} → i ∼ j ⊔ m → j ∼ m ⊔ m
    ∼max ∼+ = ∼0
    ∼max ∼0 = ∼0
    ∼max ∼- = ∼+
   
  ------------------------------------------------------------------------
  -- AVL trees
   
  -- Key/value pairs.
   
  KV : Set (𝑼⟨Key⟩ ⊔ 𝑼⟨Value⟩)
  KV = Σ Key Value
   
  module Indexed where
   
    open Extended-key
    open Height-invariants
   
    -- The trees have three parameters/indices: a lower bound on the
    -- keys, an upper bound, and a height.
    --
    -- (The bal argument is the balance factor.)
   
    data Tree (l u : Key⁺) : ℕ → Set (𝑼⟨Key⟩ ⊔ 𝑼⟨Value⟩ ⊔ 𝑼⟨<⟩) where
      leaf : (l<u : l <⁺ u) → Tree l u 0
      node : ∀ {hˡ hʳ h}
             (k : KV)
             (lk : Tree l [ proj₁ k ] hˡ)
             (ku : Tree [ proj₁ k ] u hʳ)
             (bal : hˡ ∼ hʳ ⊔ h) →
             Tree l u (suc h)
   
    Tree<* : (<k : Key⁺) → (kv : KV) → (h : ℕ) → ∃! _≡_ λ s → s ≡ Tree <k [ proj₁ kv ] h
    Tree<* <k (k , _) h = Tree <k [ k ] h , _≡_.refl , sym
   
    Tree< : Key⁺ → KV → ℕ → Set ( 𝑼⟨Key⟩ ⊔ 𝑼⟨Value⟩ ⊔ 𝑼⟨<⟩ )
    Tree< <k (k , _) h = Tree <k [ k ] h
   
    Tree> : ∀ (kv : KV) → (>k : Key⁺) → (h : ℕ) → Set ( 𝑼⟨Key⟩ ⊔ 𝑼⟨Value⟩ ⊔ 𝑼⟨<⟩ )
    Tree> (k , _) >k h = Tree [ k ] >k h
   
    data _∈_ { <k >k } ( kv : KV ) : ∀ { h } → Tree <k >k h → Set ( 𝑼⟨Key⟩ ⊔ 𝑼⟨Value⟩ ⊔ 𝑼⟨<⟩ ) where
      here : ∀
             { <h >h h }
             { <t : Tree< <k kv <h }
             { >t : Tree> kv >k >h }
             { bal : <h ∼ >h ⊔ h }
             → kv ∈ node kv <t >t bal
      left : ∀
             { <h >h h k′ } { v′ : Value k′ }
             { <t : Tree <k [ k′ ] <h }
             { >t : Tree [ k′ ]  >k >h }
             { bal : <h ∼ >h ⊔ h }
             → kv ∈ <t
             → kv ∈ node ( k′ , v′ ) <t >t bal
      right : ∀
              { <h >h h k′ } { v′ : Value k′ }
              { <t : Tree <k [ k′ ] <h }
              { >t : Tree [ k′ ] >k >h }
              { bal : <h ∼ >h ⊔ h }
              → kv ∈ >t
              → kv ∈ node ( k′ , v′ ) <t >t bal
   
  --  ∈→Tree : ∀ (kvs : Setoid KV)
   
    open import Relation.Nullary
   
    Tree→∈ : ∀ { <k >k h } → (t : Tree <k >k h) → { kv : KV } → Dec (kv ∈ t)
    Tree→∈ (leaf l<u) = no (λ ())
    Tree→∈ (node (k , v) t t₁ bal) {(k' , v')} with compare k k'
    Tree→∈ (node (k , v) t t₁ bal) {k' , v'} | tri< a ¬b ¬c = {!!}
    Tree→∈ (node (k , v) t t₁ bal) {k' , v'} | tri≈ ¬a b ¬c = {!!}
    Tree→∈ (node (k , v) t t₁ bal) {k' , v'} | tri> ¬a ¬b c = {!!}
   
    {-
    Tree→∈ (leaf l<u) = no (λ ())
    Tree→∈ (node (k , v) t t₁ bal) {k1} {{ b = b }} with compare k k1
    Tree→∈ (node (k , v) t t₁ bal) {k1} {{ b = b }} | tri< k<k _ _ = {!!}
    Tree→∈ (node (k , v) t t₁ bal) {k1} {{ b = b }} | tri> _ _ k>k = {!!}
    Tree→∈ (node (k , v) t t₁ bal) {k1} {vv} {.(k , } {{ b = refl }} | tri≈ _ k=k _ rewrite k=k = ?
    -}
    
    -- Cast operations. Logarithmic in the size of the tree, if we don't
    -- count the time needed to construct the new proofs in the leaf
    -- cases. (The same kind of caveat applies to other operations
    -- below.)
    --
    -- Perhaps it would be worthwhile changing the data structure so
    -- that the casts could be implemented in constant time (excluding
    -- proof manipulation). However, note that this would not change the
    -- worst-case time complexity of the operations below (up to Θ).
   
    castˡ : ∀ {l m u h} → l <⁺ m → Tree m u h → Tree l u h
    castˡ {l} l<m (leaf m<u)         = leaf (trans⁺ l l<m m<u)
    castˡ     l<m (node k mk ku bal) = node k (castˡ l<m mk) ku bal
   
    castʳ : ∀ {l m u h} → Tree l m h → m <⁺ u → Tree l u h
    castʳ {l} (leaf l<m)         m<u = leaf (trans⁺ l l<m m<u)
    castʳ     (node k lk km bal) m<u = node k lk (castʳ km m<u) bal
   
    -- Various constant-time functions which construct trees out of
    -- smaller pieces, sometimes using rotation.
   
    joinˡ⁺ : ∀ {l u hˡ hʳ h} →
             (k : KV) →
             (∃ λ i → Tree l [ proj₁ k ] (i ⊕ hˡ)) →
             Tree [ proj₁ k ] u hʳ →
             (bal : hˡ ∼ hʳ ⊔ h) →
             ∃ λ i → Tree l u (i ⊕ (1 + h))
    joinˡ⁺ k₆ (1# , node k₂ t₁
                      (node k₄ t₃ t₅ bal)
                                  ∼+) t₇ ∼-  = (0# , node k₄
                                                          (node k₂ t₁ t₃ (max∼ bal))
                                                          (node k₆ t₅ t₇ (∼max bal))
                                                          ∼0)
    joinˡ⁺ k₄ (1# , node k₂ t₁ t₃ ∼-) t₅ ∼-  = (0# , node k₂ t₁ (node k₄ t₃ t₅ ∼0) ∼0)
    joinˡ⁺ k₄ (1# , node k₂ t₁ t₃ ∼0) t₅ ∼-  = (1# , node k₂ t₁ (node k₄ t₃ t₅ ∼-) ∼+)
    joinˡ⁺ k₂ (1# , t₁)               t₃ ∼0  = (1# , node k₂ t₁ t₃ ∼-)
    joinˡ⁺ k₂ (1# , t₁)               t₃ ∼+  = (0# , node k₂ t₁ t₃ ∼0)
    joinˡ⁺ k₂ (0# , t₁)               t₃ bal = (0# , node k₂ t₁ t₃ bal)
   
    joinʳ⁺ : ∀ {l u hˡ hʳ h} →
             (k : KV) →
             Tree l [ proj₁ k ] hˡ →
             (∃ λ i → Tree [ proj₁ k ] u (i ⊕ hʳ)) →
             (bal : hˡ ∼ hʳ ⊔ h) →
             ∃ λ i → Tree l u (i ⊕ (1 + h))
    joinʳ⁺ k₂ t₁ (1# , node k₆
                         (node k₄ t₃ t₅ bal)
                                  t₇ ∼-) ∼+  = (0# , node k₄
                                                          (node k₂ t₁ t₃ (max∼ bal))
                                                          (node k₆ t₅ t₇ (∼max bal))
                                                          ∼0)
    joinʳ⁺ k₂ t₁ (1# , node k₄ t₃ t₅ ∼+) ∼+  = (0# , node k₄ (node k₂ t₁ t₃ ∼0) t₅ ∼0)
    joinʳ⁺ k₂ t₁ (1# , node k₄ t₃ t₅ ∼0) ∼+  = (1# , node k₄ (node k₂ t₁ t₃ ∼+) t₅ ∼-)
    joinʳ⁺ k₂ t₁ (1# , t₃)               ∼0  = (1# , node k₂ t₁ t₃ ∼+)
    joinʳ⁺ k₂ t₁ (1# , t₃)               ∼-  = (0# , node k₂ t₁ t₃ ∼0)
    joinʳ⁺ k₂ t₁ (0# , t₃)               bal = (0# , node k₂ t₁ t₃ bal)
   
    joinˡ⁻ : ∀ {l u} hˡ {hʳ h} →
             (k : KV) →
             (∃ λ i → Tree l [ proj₁ k ] (i ⊕ hˡ ─1)) →
             Tree [ proj₁ k ] u hʳ →
             (bal : hˡ ∼ hʳ ⊔ h) →
             ∃ λ i → Tree l u (i ⊕ h)
    joinˡ⁻ zero    k₂ (0# , t₁) t₃ bal = (1# , node k₂ t₁ t₃ bal)
    joinˡ⁻ zero    k₂ (1# , t₁) t₃ bal = (1# , node k₂ t₁ t₃ bal)
    joinˡ⁻ (suc _) k₂ (0# , t₁) t₃ ∼+  = joinʳ⁺ k₂ t₁ (1# , t₃) ∼+
    joinˡ⁻ (suc _) k₂ (0# , t₁) t₃ ∼0  = (1# , node k₂ t₁ t₃ ∼+)
    joinˡ⁻ (suc _) k₂ (0# , t₁) t₃ ∼-  = (0# , node k₂ t₁ t₃ ∼0)
    joinˡ⁻ (suc _) k₂ (1# , t₁) t₃ bal = (1# , node k₂ t₁ t₃ bal)
   
    joinʳ⁻ : ∀ {l u hˡ} hʳ {h} →
             (k : KV) →
             Tree l [ proj₁ k ] hˡ →
             (∃ λ i → Tree [ proj₁ k ] u (i ⊕ hʳ ─1)) →
             (bal : hˡ ∼ hʳ ⊔ h) →
             ∃ λ i → Tree l u (i ⊕ h)
    joinʳ⁻ zero    k₂ t₁ (0# , t₃) bal = (1# , node k₂ t₁ t₃ bal)
    joinʳ⁻ zero    k₂ t₁ (1# , t₃) bal = (1# , node k₂ t₁ t₃ bal)
    joinʳ⁻ (suc _) k₂ t₁ (0# , t₃) ∼-  = joinˡ⁺ k₂ (1# , t₁) t₃ ∼-
    joinʳ⁻ (suc _) k₂ t₁ (0# , t₃) ∼0  = (1# , node k₂ t₁ t₃ ∼-)
    joinʳ⁻ (suc _) k₂ t₁ (0# , t₃) ∼+  = (0# , node k₂ t₁ t₃ ∼0)
    joinʳ⁻ (suc _) k₂ t₁ (1# , t₃) bal = (1# , node k₂ t₁ t₃ bal)
   
    -- Extracts the smallest element from the tree, plus the rest.
    -- Logarithmic in the size of the tree.
   
    headTail : ∀ {l u h} → Tree l u (1 + h) →
               ∃ λ (k : KV) → l <⁺ [ proj₁ k ] ×
                              ∃ λ i → Tree [ proj₁ k ] u (i ⊕ h)
    headTail (node k₁ (leaf l<k₁) t₂ ∼+) = (k₁ , l<k₁ , 0# , t₂)
    headTail (node k₁ (leaf l<k₁) t₂ ∼0) = (k₁ , l<k₁ , 0# , t₂)
    headTail (node {hˡ = suc _} k₃ t₁₂ t₄ bal) with headTail t₁₂
    ... | (k₁ , l<k₁ , t₂) = (k₁ , l<k₁ , joinˡ⁻ _ k₃ t₂ t₄ bal)
   
    -- Extracts the largest element from the tree, plus the rest.
    -- Logarithmic in the size of the tree.
   
    initLast : ∀ {l u h} → Tree l u (1 + h) →
               ∃ λ (k : KV) → [ proj₁ k ] <⁺ u ×
                              ∃ λ i → Tree l [ proj₁ k ] (i ⊕ h)
    initLast (node k₂ t₁ (leaf k₂<u) ∼-) = (k₂ , k₂<u , (0# , t₁))
    initLast (node k₂ t₁ (leaf k₂<u) ∼0) = (k₂ , k₂<u , (0# , t₁))
    initLast (node {hʳ = suc _} k₂ t₁ t₃₄ bal) with initLast t₃₄
    ... | (k₄ , k₄<u , t₃) = (k₄ , k₄<u , joinʳ⁻ _ k₂ t₁ t₃ bal)
   
    -- Another joining function. Logarithmic in the size of either of
    -- the input trees (which need to have almost equal heights).
   
    join : ∀ {l m u hˡ hʳ h} →
           Tree l m hˡ → Tree m u hʳ → (bal : hˡ ∼ hʳ ⊔ h) →
           ∃ λ i → Tree l u (i ⊕ h)
    join t₁ (leaf m<u) ∼0 = (0# , castʳ t₁ m<u)
    join t₁ (leaf m<u) ∼- = (0# , castʳ t₁ m<u)
    join {hʳ = suc _} t₁ t₂₃ bal with headTail t₂₃
    ... | (k₂ , m<k₂ , t₃) = joinʳ⁻ _ k₂ (castʳ t₁ m<k₂) t₃ bal
   
    -- An empty tree.
   
    empty : ∀ {l u} → l <⁺ u → Tree l u 0
    empty = leaf
   
    -- A singleton tree.
   
    singleton : ∀ {l u} (k : Key) → Value k → l < k < u → Tree l u 1
    singleton k v (l<k , k<u) = node (k , v) (leaf l<k) (leaf k<u) ∼0
   
    -- Inserts a key into the tree, using a function to combine any
    -- existing value with the new value. Logarithmic in the size of the
    -- tree (assuming constant-time comparisons and a constant-time
    -- combining function).
   
    insertWith : ∀ {l u h} → (k : Key) → Value k →
                 (Value k → Value k → Value k) →  -- New → old → result.
                 Tree l u h → l < k < u →
                 ∃ λ i → Tree l u (i ⊕ h)
    insertWith k v f (leaf l<u) l<k<u = (1# , singleton k v l<k<u)
    insertWith k v f (node (k′ , v′) lp pu bal) (l<k , k<u) with compare k k′
    ... | tri< k<k′ _ _ = joinˡ⁺ (k′ , v′) (insertWith k v f lp (l<k , k<k′)) pu bal
    ... | tri> _ _ k′<k = joinʳ⁺ (k′ , v′) lp (insertWith k v f pu (k′<k , k<u)) bal
    ... | tri≈ _ k≡k′ _ rewrite P.sym k≡k′ = (0# , node (k , f v v′) lp pu bal)
   
    -- Inserts a key into the tree. If the key already exists, then it
    -- is replaced. Logarithmic in the size of the tree (assuming
    -- constant-time comparisons).
   
    insert : ∀ {l u h} → (k : Key) → Value k → Tree l u h → l < k < u →
             ∃ λ i → Tree l u (i ⊕ h)
    insert k v = insertWith k v const
   
    -- Deletes the key/value pair containing the given key, if any.
    -- Logarithmic in the size of the tree (assuming constant-time
    -- comparisons).
   
    delete : ∀ {l u h} → Key → Tree l u h →
             ∃ λ i → Tree l u (i ⊕ h ─1)
    delete k (leaf l<u)         = (0# , leaf l<u)
    delete k (node p lp pu bal) with compare k (proj₁ p)
    ... | tri< _ _ _ = joinˡ⁻ _ p (delete k lp) pu bal
    ... | tri> _ _ _ = joinʳ⁻ _ p lp (delete k pu) bal
    ... | tri≈ _ _ _ = join lp pu bal
   
    -- Looks up a key. Logarithmic in the size of the tree (assuming
    -- constant-time comparisons).
   
    lookup : ∀ {l u h} → (k : Key) → Tree l u h → Maybe (Value k)
    lookup k (leaf _)                  = nothing
    lookup k (node (k′ , v) lk′ k′u _) with compare k k′
    ... | tri< _ _  _ = lookup k lk′
    ... | tri> _ _  _ = lookup k k′u
    ... | tri≈ _ eq _ rewrite eq = just v
   
    -- Maps a function over all values in the tree.
   
    map : (∀ {k} → Value k → Value k) →
          ∀ {l u h} → Tree l u h → Tree l u h
    map f (leaf l<u)             = leaf l<u
    map f (node (k , v) l r bal) = node (k , f v) (map f l) (map f r) bal
   
    -- Converts the tree to an ordered list. Linear in the size of the
    -- tree.
   
    open DiffList
   
    toDiffList : ∀ {l u h} → Tree l u h → DiffList KV
    toDiffList (leaf _)       = []
    toDiffList (node k l r _) = toDiffList l ++ k ∷ toDiffList r
   
  module OrderedList where
    open Indexed
   
    open Extended-key
    open Height-invariants
    
    open import Relation.Binary.HeterogeneousEquality as H using ( _≅_ )
    open import Relation.Nullary.Negation
    import Data.List as L
   
    infixr 6 _∷_
    data OrderedList (l u : Key⁺) : Set (𝑼⟨Key⟩ ⊔ 𝑼⟨<⟩) where
      [] : {{l<u : l <⁺ u}} → OrderedList l u
      _∷_ : ∀
             (k : Key)
             {{_ : l <⁺ [ k ]}}
             (ku : OrderedList [ k ] u) →
             OrderedList l u
   
    infixr 8 _++_
    _++_ : ∀ {l n u} → OrderedList l n → (∀ {m} → {{_ : m <⁺ n}} → OrderedList m u) → OrderedList l u
    [] ++ ys = ys
    (x ∷ xs) ++ ys = x ∷ xs ++ ys
   
    
      
    
   
  module MSD where
   
    open Indexed hiding ( _∈_ )
   
    open Extended-key
    open Height-invariants
    
    open import Relation.Binary.HeterogeneousEquality as H using ( _≅_ )
    open import Relation.Nullary.Negation
    import Data.List as L
   
    Tree⟶<⁺ : ∀ { k⃖ k⃗ h } → Tree k⃖ k⃗ h → k⃖ <⁺ k⃗
    Tree⟶<⁺ ( leaf k⃖<k⃗ ) = k⃖<k⃗
    Tree⟶<⁺ { k⃖ = k⃖ } ( node _ t⃖ t⃗ _ ) = trans⁺ k⃖ ( Tree⟶<⁺ t⃖ ) ( Tree⟶<⁺ t⃗ )
   
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
   
    ∈⟶Tree : ∀ { l u h } { t : Tree l u h } { k : Key } → k ∈ t → Tree l u h
    ∈⟶Tree { t = t } _ = t
   
    ∈⟶<< : ∀ { l u h } { t : Tree l u h } { k : Key } → k ∈ t → l < k < u
    ∈⟶<< ( here { t⃖ = t⃖ } { t⃗ = t⃗ } ) = Tree⟶<⁺ t⃖ , Tree⟶<⁺ t⃗
    ∈⟶<< { l = l } { u = u } { k = k } ( left { k′ = k′ } { t⃗ = t⃗ } k∈tˡ ) = l<k , k<u where
      l<k<k′ : l < k < [ k′ ]
      l<k<k′ = ∈⟶<< k∈tˡ
     
      l<k : l <⁺ [ k ]
      l<k = proj₁ l<k<k′
     
      k<k′ : [ k ] <⁺ [ k′ ]
      k<k′ = proj₂ l<k<k′
     
      k′<u : [ k′ ] <⁺ u
      k′<u = Tree⟶<⁺ t⃗
     
      k<u : [ k ] <⁺ u
      k<u = trans⁺ [ k ] { m = [ k′ ] } { u = u } k<k′ k′<u
    ∈⟶<< { l = l } { u = u } { k = k } ( right { k′ = k′ } { t⃖ = lk′ } k∈tʳ ) = l<k , k<u where
      k′<k<u : [ k′ ] < k < u
      k′<k<u = ∈⟶<< k∈tʳ
     
      k<u : [ k ] <⁺ u
      k<u = proj₂ k′<k<u
     
      k′<k : [ k′ ] <⁺ [ k ] 
      k′<k = proj₁ k′<k<u
     
      l<k′ : l <⁺ [ k′ ]
      l<k′ = Tree⟶<⁺ lk′
     
      l<k : l <⁺ [ k ]
      l<k = trans⁺ l { m = [ k′ ] } { u = [ k ] } l<k′ k′<k
     
    data _∼_∈̃_ { k⃖ k⃗ : Key⁺ } ( k : Key ) ( v : Value k ) {- ( k' : Key ) ⦃ _ : k ≡ k' ⦄ -} : ∀ { h : ℕ } → Tree k⃖ k⃗ h → Set ( 𝑼⟨Key⟩ ⊔ 𝑼⟨Value⟩ ⊔ 𝑼⟨<⟩ ) where
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
   
    _∈̌_ : ∀ { k⃖ k⃗ : Key⁺ } { h } ( kv : KV ) → ( t : Tree k⃖ k⃗ h )  → Set ( 𝑼⟨Key⟩ ⊔ 𝑼⟨Value⟩ ⊔ 𝑼⟨<⟩ )
    (k , v) ∈̌ t = k ∼ v ∈̃ t
   
    ∈̃→∈ : ∀ { k l u h } { v : Value k } { t : Tree l u h } → k ∼ v ∈̃ t → k ∈ t
    ∈̃→∈ here = here
    ∈̃→∈ (left x) = left (∈̃→∈ x)
    ∈̃→∈ (right x) = right (∈̃→∈ x)
   
    ∈̌⟶l<⁺k : ∀ { k l u h } { v : Value k } { t : Tree l u h } → k ∼ v ∈̃ t → l <⁺ [ k ]
    ∈̌⟶l<⁺k x = proj₁ (∈⟶<< (∈̃→∈ x))
   
    ∈̌⟶k<⁺u : ∀ { k l u h } { v : Value k } { t : Tree l u h } → k ∼ v ∈̃ t → [ k ] <⁺ u
    ∈̌⟶k<⁺u x = proj₂ (∈⟶<< (∈̃→∈ x))
   
    open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
   
    a≮a : ∀ { k } → k < k → ⊥
    a≮a = irrefl P.refl
    
    lemL : ∀ { k l h } { v : Value k } { t : Tree l [ k ] h } → k ∼ v ∈̃ t → ⊥
    lemL x = contradiction ( proj₂ (∈⟶<< (∈̃→∈ x))) ( a≮a) where
      
    lemR : ∀ { k u h } { v : Value k } { t : Tree [ k ] u h } → k ∼ v ∈̃ t → ⊥
    lemR x = contradiction ( proj₁ (∈⟶<< (∈̃→∈ x))) ( a≮a) where
   
    open import Relation.Binary.Consequences
      
    k→v : ∀ {kv1 kv2 : KV} {l u h} {t : Tree l u h} → kv1 ∈̌ t → kv2 ∈̌ t → proj₁ kv1 ≡ proj₁ kv2 → kv1 ≅ kv2
    k→v here here P.refl = H.refl
    k→v (here { t⃖ = t⃖ })  (left kv2∈̌t) P.refl = ⊥-elim (lemL kv2∈̌t)
    k→v here (right kv2∈̌t) P.refl = ⊥-elim (lemR kv2∈̌t)
    k→v (left kv1∈̌tˡ) here P.refl = ⊥-elim (lemL kv1∈̌tˡ)
    k→v (left kv1∈̌tˡ) (left kv2∈̌t) P.refl = k→v kv1∈̌tˡ kv2∈̌t P.refl
    k→v (left kv1∈̌tˡ) (right kv2∈̌t) P.refl = contradiction (proj₂ (∈⟶<< (∈̃→∈ kv1∈̌tˡ))) (tri⟶asym compare (proj₁ (∈⟶<< (∈̃→∈ kv2∈̌t))))
    k→v (right kv1∈̌tʳ) here P.refl = ⊥-elim (lemR kv1∈̌tʳ)
    k→v (right kv1∈̌tʳ) (left kv2∈̌t) P.refl = contradiction (proj₂ (∈⟶<< (∈̃→∈ kv2∈̌t))) (tri⟶asym compare (proj₁ (∈⟶<< (∈̃→∈ kv1∈̌tʳ))))
    k→v (right kv1∈̌tʳ) (right kv2∈̌t) P.refl = k→v kv1∈̌tʳ kv2∈̌t P.refl
   
    k→v' : ∀ { k : Key } { v₁ v₂ : Value k } { l u h } { t : Tree l u h } → k ∼ v₁ ∈̃ t → k ∼ v₂ ∈̃ t → v₁ ≡ v₂
    k→v' here here = P.refl
    k→v' here (left kv2∈̌t) = ⊥-elim (lemL kv2∈̌t)
    k→v' here (right kv2∈̌t) = ⊥-elim (lemR kv2∈̌t)
    k→v' (left kv1∈̌tˡ) here = ⊥-elim (lemL kv1∈̌tˡ)
    k→v' (left kv1∈̌tˡ) (left kv2∈̌t) = k→v' kv1∈̌tˡ kv2∈̌t
    k→v' (left kv1∈̌tˡ) (right kv2∈̌t) = contradiction (proj₂ (∈⟶<< (∈̃→∈ kv1∈̌tˡ))) (tri⟶asym compare (proj₁ (∈⟶<< (∈̃→∈ kv2∈̌t))))
    k→v' (right kv1∈̌tʳ) here = ⊥-elim (lemR kv1∈̌tʳ)
    k→v' (right kv1∈̌tʳ) (left kv2∈̌t) = contradiction (proj₂ (∈⟶<< (∈̃→∈ kv2∈̌t))) (tri⟶asym compare (proj₁ (∈⟶<< (∈̃→∈ kv1∈̌tʳ))))
    k→v' (right kv1∈̌tʳ) (right kv2∈̌t) = k→v' kv1∈̌tʳ kv2∈̌t
   
    <⁺⟶< : ∀ {l u} → [ l ] <⁺ [ u ] → l < u
    <⁺⟶< [l]<⁺[u] = [l]<⁺[u]
   
    kv<k→kv∈t1 : ∀ {l1 u1 k kv h1 h2 H1} →
              {v : Value k}
              {t1 : Tree l1 [ k ] h1} →
              {t2 : Tree [ k ] u1 h2} →
              {bal1 : h1 ∼ h2 ⊔ H1} →
              proj₁ kv < k →
              kv ∈̌ node (k , v) t1 t2 bal1 → 
              kv ∈̌ t1
    kv<k→kv∈t1 kv<k here = ⊥-elim (irrefl P.refl kv<k)
    kv<k→kv∈t1 kv<k (left kv∈̌node) = kv∈̌node
    kv<k→kv∈t1 {kv = (k , v)} kv<k (right kv∈̌node) = contradiction (<⁺⟶< (∈̌⟶l<⁺k kv∈̌node)) (tri⟶asym compare kv<k)
   
    k<kv→kv∈t2 : ∀ {l1 u1 k kv h1 h2 H1} →
              {v : Value k}
              {t1 : Tree l1 [ k ] h1} →
              {t2 : Tree [ k ] u1 h2} →
              {bal1 : h1 ∼ h2 ⊔ H1} →
              k < proj₁ kv →
              kv ∈̌ node (k , v) t1 t2 bal1 → 
              kv ∈̌ t2
    k<kv→kv∈t2 k<kv here = ⊥-elim (irrefl P.refl k<kv)
    k<kv→kv∈t2 k<kv (right kv∈̌node) = kv∈̌node
    k<kv→kv∈t2 {kv = (k , v)} k<kv (left kv∈̌node) = contradiction (<⁺⟶< (∈̌⟶k<⁺u kv∈̌node)) (tri⟶asym compare k<kv)
   
    t1→t3 : ∀ {l1 l2 u1 u2 k kv h1 h2 h3 h4 H1 H2} →
              {v : Value k}
              {t1 : Tree l1 [ k ] h1} →
              {t2 : Tree [ k ] u1 h2} →
              {t3 : Tree l2 [ k ] h3} →
              {t4 : Tree [ k ] u2 h4} →
              {bal1 : h1 ∼ h2 ⊔ H1}
              {bal2 : h3 ∼ h4 ⊔ H2} →
              (kv ∈̌ node (k , v) t1 t2 bal1 → kv ∈̌ node (k , v) t3 t4 bal2) →
              kv ∈̌ t1 → kv ∈̌ t3
    t1→t3 ∈̌→∈̌ kv∈̌t1 = let kv∈̌node12 = left kv∈̌t1 in kv<k→kv∈t1 (<⁺⟶< (∈̌⟶k<⁺u kv∈̌t1)) (∈̌→∈̌ kv∈̌node12)
   
    t2→t4 : ∀ {l1 l2 u1 u2 k kv h1 h2 h3 h4 H1 H2} →
              {v : Value k}
              {t1 : Tree l1 [ k ] h1} →
              {t2 : Tree [ k ] u1 h2} →
              {t3 : Tree l2 [ k ] h3} →
              {t4 : Tree [ k ] u2 h4} →
              {bal1 : h1 ∼ h2 ⊔ H1}
              {bal2 : h3 ∼ h4 ⊔ H2} →
              (kv ∈̌ node (k , v) t1 t2 bal1 → kv ∈̌ node (k , v) t3 t4 bal2) →
              kv ∈̌ t2 → kv ∈̌ t4
    t2→t4 ∈̌→∈̌ kv∈̌t2 = let kv∈̌node12 = right kv∈̌t2 in k<kv→kv∈t2 (<⁺⟶< (∈̌⟶l<⁺k kv∈̌t2)) (∈̌→∈̌ kv∈̌node12)
   
    open import Relation.Binary.PropositionalEquality.Core
    open import Relation.Binary.PropositionalEquality
   
    ∈̃→v1≡v2 : ∀ { k l u h1 h2 h } → { v1 v2 : Value k } { t₁ : Tree l [ k ] h1 } { t₂ : Tree [ k ] u h2 } { bal : h1 ∼ h2 ⊔ h } → k ∼ v1 ∈̃ node (k , v2) t₁ t₂ bal → v1 ≡ v2
    ∈̃→v1≡v2 here = refl
    ∈̃→v1≡v2 (left x) = ⊥-elim (lemL x)
    ∈̃→v1≡v2 (right x) = ⊥-elim (lemR x)
      
    ∈̃→v2≡v1 : ∀ { k l u h1 h2 h } → { v1 v2 : Value k } { t₁ : Tree l [ k ] h1 } { t₂ : Tree [ k ] u h2 } { bal : h1 ∼ h2 ⊔ h } → k ∼ v1 ∈̃ node (k , v2) t₁ t₂ bal → v2 ≡ v1
    ∈̃→v2≡v1 here = refl
    ∈̃→v2≡v1 (left x) = ⊥-elim (lemL x)
    ∈̃→v2≡v1 (right x) = ⊥-elim (lemR x)
   
  {-
    data Tree* (l u : Key⁺) : ℕ → Set (𝑼⟨Key⟩ ⊔ 𝑼⟨Value⟩ ⊔ 𝑼⟨<⟩) where
      leaf : (l<u : l <⁺ u) → Tree* l u 0
      node : ∀ {hˡ hʳ h}
             (k : KV)
             (lk : Tree* l [ proj₁ k ] hˡ)
             (ku : Tree* [ proj₁ k ] u hʳ)
             (bal : hˡ ∼ hʳ ⊔ h) →
             Tree* l u (suc h)
  -}
    duh : ∀ {k l₁₂ l₃₄ u₁₂ u₃₄ h₁ h₂ h₁₂ h₃ h₄ h₃₄} {v₁ v₂ : Value k}
            { t₁ : Tree l₁₂ [ k ] h₁ }
            { t₂ : Tree [ k ] u₁₂ h₂ }
            { t₃ : Tree l₃₄ [ k ] h₃ }
            { t₄ : Tree [ k ] u₃₄ h₄ }
            { bal₁₂ : h₁ ∼ h₂ ⊔ h₁₂ }
            { bal₃₄ : h₃ ∼ h₄ ⊔ h₃₄ } →
            (∀ {kv : Σ Key Value} →
             proj₁ kv ∼ proj₂ kv ∈̃ node (k , v₁) t₁ t₂ bal₁₂ →
             proj₁ kv ∼ proj₂ kv ∈̃ node (k , v₂) t₃ t₄ bal₃₄
            )
          → v₂ ≡ v₁
          → (∀ {kv : Σ Key Value} →
             proj₁ kv ∼ proj₂ kv ∈̃ node (k , v₁) t₁ t₂ bal₁₂ →
             proj₁ kv ∼ proj₂ kv ∈̃ node (k , v₁) t₃ t₄ bal₃₄)
    duh x x₁ x₂ rewrite x₁ = x x₂
   
    open OrderedList
   
    toOrderedList : ∀ {l u h} → Tree l u h → OrderedList l u
    toOrderedList (leaf l<u) = []
    toOrderedList (node k tl tr bal) = toOrderedList tl ++ (proj₁ k ∷ toOrderedList tr)
   
    data _∈ₗ_ {l u} (k : Key) : OrderedList l u → Set (𝑼⟨<⟩ ⊔ 𝑼⟨Key⟩) where
      here : ∀ {ks : OrderedList [ k ] u} {{p : l <⁺ [ k ] }} → k ∈ₗ (k ∷ ks)
      succ : ∀ {k' : Key} {ks : OrderedList [ k' ] u} {{p : l <⁺ [ k' ] }} → k ∈ₗ ks → k ∈ₗ (k' ∷ ks)
   
    lem'' : ∀ {l u} (y : OrderedList l u) (l<u : l <⁺ u) → (x : ∀ (k : Key) → (k ∈ₗ y → _∈ₗ_ {l} {u} k [])) → [] ≡ y
    lem'' {l} {u} ([]) l<u₁ x = {!refl!} -- l<u₁ != .l<u of type l <⁺ u
    lem'' (k ∷ y) l<u x₁ = {!!}
    
    lem' : ∀ {l u} (y : OrderedList l u) (l<u : l <⁺ u) → (x : ∀ (k : Key) → (k ∈ₗ y → _∈_ {l} k (leaf l<u))) → [] ≡ y
    lem' {l} {u} ([]) l<u₁ x = {!refl!} -- l<u₁ != .l<u of type l <⁺ u
    lem' (k ∷ y) l<u x₁ = {!!}
    
    lem : ∀ {l u} (y : OrderedList l u) (l<u : l <⁺ u) → (x : ∀ (k : Key) → (_∈_ {l} k (leaf l<u) → k ∈ₗ y) × (k ∈ₗ y → _∈_ {l} k (leaf l<u))) → [] ≡ y
    lem {l} {u} ([]) l<u₁ x = {!refl!} -- l<u₁ != .l<u of type l <⁺ u
    lem (k ∷ y) l<u x₁ = {!!}
   
    LEM : ∀ { l u } k {a : OrderedList l [ k ]} {b : OrderedList [ k ] u} → k ∈ₗ (a ++ (k ∷ b))
    LEM k {[]} = here
    LEM k {k₁ ∷ a} = succ (LEM k {a})
   
    LEM2 : ∀ { l m u } {a : OrderedList l m} {b : ∀ {m'} {{_ : m' <⁺ m}} → OrderedList m' u} → ∀ k → k ∈ₗ a → k ∈ₗ (a ++ b)
    LEM2 = {!!}
   
    lemma1 : ∀ {l u h} → (t : Tree l u h) → (o : OrderedList l u) → o ≡ toOrderedList t → ∀ k → k ∈ t → k ∈ₗ o
    lemma1 ._ ._ refl k (here {t⃖ = t⃖}) = LEM k {a = toOrderedList t⃖}
    lemma1 (node k1 tl tr bal) ._ refl k (left x1) = LEM2 k (lemma1 _ _ refl k x1)
    lemma1 ._ ._ refl k (right x₁) = {!!}
   
    lemma2 : ∀ {k₁ hˡ hʳ h k l u} {bal      : hˡ ∼ hʳ ⊔ h} {tr       : Tree [ proj₁ k ] u hʳ} {tl       : Tree l [ proj₁ k ] hˡ}
               (x : k₁ ∈ₗ (toOrderedList tl ++ (λ {m} {-{_ : {!!}}-} → proj₁ k ∷ toOrderedList tr))) →
               k₁ ∈ node k tl tr bal
    lemma2 {tl = leaf l<u} here = here
    lemma2 {tl = leaf l<u} (succ x) = {!!}
    lemma2 {tl = node k tl tl₁ bal₁} x = {!!}
   
    toOrderedList' : ∀ {l u h} → (t : Tree l u h) → ∃! _≡_ λ (o : OrderedList l u) → ∀ k → (k ∈ t → k ∈ₗ o) × (k ∈ₗ o → k ∈ t)
    toOrderedList' (leaf l<u) = [] , (λ k → (λ ()) , (λ ())) , (λ x → (lem _ l<u x))
    toOrderedList' (node k tl tr bal) = toOrderedList tl ++ (proj₁ k ∷ toOrderedList tr) , (λ k₁ → (λ x → lemma1 (node k tl tr bal) (toOrderedList tl ++ (proj₁ k ∷ toOrderedList tr)) refl k₁ x) , (λ x → {!!})) , (λ x → {!!}) where
      
   
   
   
    lemjl- : ∀ { k⃖₁ k⃗₁ h₁ k⃖₂ k⃗₂ h₂ } →
             ( t₁ : Tree k⃖₁ k⃗₁ h₁ )
             ( t₂ : Tree k⃖₂ k⃗₂ h₂ )
             ( _ : ∀ {kv} → kv ∈̌ t₁ → kv ∈̌ t₂ )
             ( _ : ∀ {kv} → kv ∈̌ t₂ → kv ∈̌ t₁ ) →
             ( lst : List KV ) →
             (toDiffList t₁) lst ≡ (toDiffList t₂) lst
    lemjl- (leaf l<u) (leaf l<u₁) x₂ x₃ lst = P.refl
    lemjl- (leaf l<u) (node k₁ t₂ t₃ bal) x₂ x₃ lst = contradiction (x₃ here) (λ ())
    lemjl- (node k₁ t₁ t₂ bal) (leaf l<u) x₂ x₃ lst = contradiction (x₂ here) (λ ())
    lemjl- (node k₁ t₁ t₂ bal) (node k₂ t₃ t₄ bal₁) x₂ x₃ lst with compare (proj₁ k₁) (proj₁ k₂)
    lemjl- (node ( k₁ , v₁ ) t₁ t₂ _) (node ( k₂ , v₂ ) t₃ t₄ _) kv∈̌t₁→kv∈̌t₂ kv∈̌t₂→kv∈̌t₁ lst | tri≈ k₁≮k₂ k₁≡k₂ k₂≮k₁ rewrite k₁≡k₂ | ∈̃→v2≡v1 (kv∈̌t₁→kv∈̌t₂ here) with duh kv∈̌t₁→kv∈̌t₂ (∈̃→v2≡v1 (kv∈̌t₁→kv∈̌t₂ here))
    lemjl- (node ( k₁ , v₁ ) t₁ t₂ _) (node ( k₂ , v₂ ) t₃ t₄ _) kv∈̌t₁→kv∈̌t₂ kv∈̌t₂→kv∈̌t₁ lst | tri≈ k₁≮k₂ k₁≡k₂ k₂≮k₁ | kv∈̌t₁→kv∈̌t₂' rewrite lemjl- t₂ t₄ (t2→t4 kv∈̌t₁→kv∈̌t₂') (t2→t4 kv∈̌t₂→kv∈̌t₁) lst = lemjl- t₁ t₃ (t1→t3 kv∈̌t₁→kv∈̌t₂') (t1→t3 kv∈̌t₂→kv∈̌t₁) ((k₂ , v₁) List.∷ toDiffList t₄ lst)
    lemjl- (node k₁ t₁ (leaf l<u) bal) (node k₂ t₃ t₄ bal₁) kv∈̌t₁→kv∈̌t₂ kv∈̌t₂→kv∈̌t₁ lst | tri< k₁<k₂ k₁≢k₂ k₂≮k₁ = contradiction {!!} {!!}
    lemjl- (node k₁ t₁ (node k t₂ t₃ bal) bal₁) (node k₂ (leaf l<u) t₅ bal₂) kv∈̌t₁→kv∈̌t₂ kv∈̌t₂→kv∈̌t₁ lst | tri< k₁<k₂ k₁≢k₂ k₂≮k₁ = contradiction {!!} {!!}
    lemjl- (node k₂ t₁ (node k₄ t₃ t₅ _) _) (node k₄' (node k₂' t₁' t₃' _) t₅' _) ∈̌t→∈̌t' ∈̌t'→∈̌t lst | tri< k₂<k₄' _ _ with compare (proj₁ k₄) (proj₁ k₂')
    lemjl- (node k₂ t₁ (node k₄ t₃ t₅ _) _) (node k₄' (node k₂' t₁' t₃' _) t₅' _) ∈̌t→∈̌t' ∈̌t'→∈̌t lst | tri< k₂<k₄' _ _ | tri< k₄<k₂' _ _ = {!!}
    lemjl- (node k₂ t₁ (node (k₄ , _) t₃ t₅ _) _) (node k₄' (node (k₂' , _) t₁' t₃' _) t₅' _) ∈̌t→∈̌t' ∈̌t'→∈̌t lst | tri< k₂<k₄' _ _ | tri≈ _ k₄≡k₂' _ rewrite k₄≡k₂' = {!!}
    lemjl- (node k₂ t₁ (node k₄ t₃ t₅ _) _) (node k₄' (node k₂' t₁' t₃' _) t₅' _) ∈̌t→∈̌t' ∈̌t'→∈̌t lst | tri< k₂<k₄' _ _ | tri> _ _ k₄≮k₂' = {!!}
   
    -- kv<k→kv∈t1 k₁<k₂ (kv∈̌t₁→kv∈̌t₂ here)
    lemjl- (node k₁ t₁ t₂ bal) (node k₂ t₃ t₄ bal₁) kv∈̌t₁→kv∈̌t₂ kv∈̌t₂→kv∈̌t₁ lst | tri> k₁≮k₂ k₁≢k₂ k₂<k₁ = {!!}
   
  {-
    data OrderedList : Maybe Key →Maybe Key → Set ( 𝑼⟨Key⟩ ⊔ 𝑼⟨<⟩ ) where
      [] : OrderedList ⊥⁺ ⊤⁺
      _∷_ : (x : Key⁺) → {x- x+ : Key⁺} → {{_ : x- <⁺ x}} → (xs : OrderedList x- x+) → OrderedList x x+
   
    _++_ : ∀ {a- a+ b- b+} → {{_ : a+ <⁺ b- }} → OrderedList a- a+ → OrderedList b- b+ → OrderedList a- b+
    [] ++ u = {!u!}
    (x ∷ l) ++ u = {!!}
   
    toOrderedList : ∀ {l u h} → Tree l u h → ∃ λ k- → ∃ λ k+ → OrderedList k- k+
    toOrderedList (leaf l<u) = _ , _ , []
    toOrderedList (node k₁ t t₁ bal) = toOrderedList t₁
  -}
   
  {-
    lemjl- : ∀ { k⃖₁ k⃗₁ h₁ k⃖₂ k⃗₂ h₂ } →
             ( t₁ : Tree k⃖₁ k⃗₁ h₁ )
             ( t₂ : Tree k⃖₂ k⃗₂ h₂ )
             ( _ : ∀ {kv} → kv ∈̌ t₁ → kv ∈̌ t₂ )
             ( _ : ∀ {kv} → kv ∈̌ t₂ → kv ∈̌ t₁ ) →
             ( lst : List KV ) →
             (toDiffList t₁) lst ≡ (toDiffList t₂) lst
    lemjl- (leaf l<u) (leaf l<u₁) x₂ x₃ lst = P.refl
    lemjl- (leaf l<u) (node k₁ t₂ t₃ bal) x₂ x₃ lst = contradiction (x₃ here) (λ ())
    lemjl- (node k₁ t₁ t₂ bal) (leaf l<u) x₂ x₃ lst = contradiction (x₂ here) (λ ())
    lemjl- (node k₁ t₁ t₂ bal) (node k₂ t₃ t₄ bal₁) x₂ x₃ lst with compare (proj₁ k₁) (proj₁ k₂)
    lemjl- (node ( k₁ , v₁ ) t₁ t₂ _) (node ( k₂ , v₂ ) t₃ t₄ _) kv∈̌t₁→kv∈̌t₂ kv∈̌t₂→kv∈̌t₁ lst | tri≈ k₁≮k₂ k₁≡k₂ k₂≮k₁ rewrite k₁≡k₂ | ∈̃→v2≡v1 (kv∈̌t₁→kv∈̌t₂ here) with duh kv∈̌t₁→kv∈̌t₂ (∈̃→v2≡v1 (kv∈̌t₁→kv∈̌t₂ here))
    lemjl- (node ( k₁ , v₁ ) t₁ t₂ _) (node ( k₂ , v₂ ) t₃ t₄ _) kv∈̌t₁→kv∈̌t₂ kv∈̌t₂→kv∈̌t₁ lst | tri≈ k₁≮k₂ k₁≡k₂ k₂≮k₁ | kv∈̌t₁→kv∈̌t₂' rewrite lemjl- t₂ t₄ (t2→t4 kv∈̌t₁→kv∈̌t₂') (t2→t4 kv∈̌t₂→kv∈̌t₁) lst = lemjl- t₁ t₃ (t1→t3 kv∈̌t₁→kv∈̌t₂') (t1→t3 kv∈̌t₂→kv∈̌t₁) ((k₂ , v₁) List.∷ toDiffList t₄ lst)
    lemjl- (node k₁ t₁ t₂ bal) (node k₂ t₃ t₄ bal₁) kv∈̌t₁→kv∈̌t₂ kv∈̌t₂→kv∈̌t₁ lst | tri< k₁<k₂ k₁≢k₂ k₂≮k₁ = {!!} -- kv<k→kv∈t1 k₁<k₂ (kv∈̌t₁→kv∈̌t₂ here)
    lemjl- (node k₁ t₁ t₂ bal) (node k₂ t₃ t₄ bal₁) kv∈̌t₁→kv∈̌t₂ kv∈̌t₂→kv∈̌t₁ lst | tri> k₁≮k₂ k₁≢k₂ k₂<k₁ = {!!}
  -}  
   
  {-
    lemjl- : ∀ { k⃖₁ k⃗₁ h₁ k⃖₂ k⃗₂ h₂ } →
             ( t₁ : Tree k⃖₁ k⃗₁ h₁ )
             ( t₂ : Tree k⃖₂ k⃗₂ h₂ )
             ( _ : ∀ {kv} → kv ∈̌ t₁ → kv ∈̌ t₂ )
             ( _ : ∀ {kv} → kv ∈̌ t₂ → kv ∈̌ t₁ ) →
             ( lst : List KV ) →
             (toDiffList t₁) lst ≡ (toDiffList t₂) lst
    lemjl- (leaf l<u) (leaf l<u₁) x₂ x₃ lst = P.refl
    lemjl- (leaf l<u) (node k₁ t₂ t₃ bal) x₂ x₃ lst = contradiction (x₃ here) (λ ())
    lemjl- (node k₁ t₁ t₂ bal) (leaf l<u) x₂ x₃ lst = contradiction (x₂ here) (λ ())
    lemjl- (node k₁ t₁ t₂ bal) (node k₂ t₃ t₄ bal₁) x₂ x₃ lst with compare (proj₁ k₁) (proj₁ k₂)
    lemjl- (node ( k₁ , v₁ ) t₁ t₂ bal) (node ( k₂ , v₂ ) t₃ t₄ bal₁) kv∈̌t₁→kv∈̌t₂ kv∈̌t₂→kv∈̌t₁ lst | tri≈ k₁≮k₂ k₁≡k₂ k₂≮k₁ rewrite
           k₁≡k₂ -- |
           -- ∈̃→v1≡v2 (kv∈̌t₂→kv∈̌t₁ here) |
           -- | ∈̃→v2≡v1 (kv∈̌t₁→kv∈̌t₂ here)
           -- lemjl- t₂ t₄ (t2→t4 kv∈̌t₁→kv∈̌t₂) {!!} lst -- (t2→t4 kv∈̌t₂→kv∈̌t₁) -- subst (∈̃→v1≡v2 (kv∈̌t₂→kv∈̌t₁ here)) kv∈̌t₂→kv∈̌t₁
           = {!!} -- lemjl- t₁ t₃ {!!} {!!} ((k₂ , v₂) L.∷ toDiffList t₄ lst)
    -- (kv∈̌t₁→kv∈̌t₂ here) -- k₂ ∼ v₁ ∈̃ node (k₂ , v₂) t₃ t₄ bal₁
    -- (kv∈̌t₂→kv∈̌t₁ here) -- k₂ ∼ v₂ ∈̃ node (k₂ , v₁) t₁ t₂ bal
    -- k→v' (kv∈̌t₁→kv∈̌t₂ here) (kv∈̌t₂→kv∈̌t₁ here)
   
  -- {-k→v'-}  {! (lemjl- t₂ t₄ (? kv∈̌t₁→kv∈̌t₂) (? kv∈̌t₂→kv∈̌t₁) lst)!}
    -- subst {!!} (lemjl- t₂ t₄ ({!!} kv∈̌t₁→kv∈̌t₂) ({!!} kv∈̌t₂→kv∈̌t₁) lst) {!!} where
    lemjl- (node k₁ t₁ t₂ bal) (node k₂ t₃ t₄ bal₁) kv∈̌t₁→kv∈̌t₂ kv∈̌t₂→kv∈̌t₁ lst | tri< k₁<k₂ k₁≢k₂ k₂≮k₁ = {!!}
    lemjl- (node k₁ t₁ t₂ bal) (node k₂ t₃ t₄ bal₁) kv∈̌t₁→kv∈̌t₂ kv∈̌t₂→kv∈̌t₁ lst | tri> k₁≮k₂ k₁≢k₂ k₂<k₁ = {!!}
  -}
    
    lemjl+ : ∀ { k⃖₁ k⃗₁ h₁ k⃖₂ k⃗₂ h₂ } →
             ( t₁ : Tree k⃖₁ k⃗₁ h₁ )
             ( t₂ : Tree k⃖₂ k⃗₂ h₂ )
             ( _ : ∀ {kv} → proj₁ kv ∼ proj₂ kv ∈̃ t₁ → proj₁ kv ∼ proj₂ kv ∈̃ t₂ )
             ( _ : ∀ {kv} → proj₁ kv ∼ proj₂ kv ∈̃ t₂ → proj₁ kv ∼ proj₂ kv ∈̃ t₁ ) →
             (toDiffList t₁) L.[] ≅ (toDiffList t₂) L.[]
    lemjl+ (leaf l<u) (leaf l<u₁) x₂ x₃ = H.refl
    lemjl+ (leaf l<u) (node k₁ t₂ t₃ bal) x₂ x₃ = contradiction (x₃ here) (λ ())
    lemjl+ (node k₁ t₁ t₂ bal) (leaf l<u) x₂ x₃ = contradiction (x₂ here) (λ ())
    lemjl+ (node k₁ t₁ t₂ bal) (node k₂ t₃ t₄ bal₁) x₂ x₃ with compare (proj₁ k₁) (proj₁ k₂)
    lemjl+ (node k₁ t₁ t₂ bal) (node k₂ t₃ t₄ bal₁) x₂ x₃ | tri< a ¬b ¬c = {!!}
    lemjl+ (node k₁ t₁ t₂ bal) (node k₂ t₃ t₄ bal₁) x₂ x₃ | tri≈ ¬a b ¬c = {!!}
    lemjl+ (node k₁ t₁ t₂ bal) (node k₂ t₃ t₄ bal₁) x₂ x₃ | tri> ¬a ¬b c = {!!}
   
    joinˡ⁺! : ∀ {l u hˡ hʳ h} →
              (k : KV) →
              (tl+ : (∃ λ i → Tree l [ proj₁ k ] (i ⊕ hˡ))) →
              (tr : Tree [ proj₁ k ] u hʳ) →
              (bal : hˡ ∼ hʳ ⊔ h) →
              ∃ λ i → ∃! _≡_ λ (t : Tree l u (i ⊕ (1 + h))) →
              (∀ (k' : Key) (v' : Value k') →
              (  (k' ∼ v' ∈̃ proj₂ tl+ → k' ∼ v' ∈̃ t)
               × (k' ∼ v' ∈̃ tr → k' ∼ v' ∈̃ t)
               × (k' ∼ v' ∈̃ t → (k' ∼ v' ∈̃ proj₂ tl+) ⊎ (k' ∼ v' ∈̃ tr) ⊎ ((k' , v') ≡ k) )
               × (proj₁ k ∼ proj₂ k ∈̃ t)
               ))
    joinˡ⁺! k₆ (1# , node k₂ t₁
                      (node k₄ t₃ t₅ bal)
                                  ∼+) t₇ ∼-  = 0# , node k₄
                                                          (node k₂ t₁ t₃ (max∼ bal))
                                                          (node k₆ t₅ t₇ (∼max bal))
                                                          ∼0 , (λ k' v' → proof , (λ x → right (right x)) , proof2 , right here) , (λ x → {!!})
               where
      proof : ∀ {k' k₂ t₁l t₁h k₄ t₃h k₆ t₅h t₇u bal}
                {v' : Value k'}
                {t₁ : Tree t₁l [ proj₁ k₂ ] t₁h}
                {t₃ : Tree [ proj₁ k₂ ] [ proj₁ k₄ ] t₃h}
                {t₅ : Tree [ proj₁ k₄ ] [ proj₁ k₆ ] t₅h}
                {t₇ : Tree [ proj₁ k₆ ] t₇u t₁h}  →
                k' ∼ v' ∈̃ node k₂ t₁ (node k₄ t₃ t₅ bal) ∼+ →
                k' ∼ v' ∈̃ node k₄ (node k₂ t₁ t₃ (max∼ bal)) (node k₆ t₅ t₇ (∼max bal)) ∼0
      proof here = left here
      proof (left x) = left (left x)
      proof (right here) = here
      proof (right (left x)) = left (right x)
      proof (right (right x)) = right (left x)
   
      proof2 : ∀ {k' k₂ t₁l t₁h k₄ t₃h k₆ t₅h t₇u bal}
                {v' : Value k'}
                {t₁ : Tree t₁l [ proj₁ k₂ ] t₁h}
                {t₃ : Tree [ proj₁ k₂ ] [ proj₁ k₄ ] t₃h}
                {t₅ : Tree [ proj₁ k₄ ] [ proj₁ k₆ ] t₅h}
                {t₇ : Tree [ proj₁ k₆ ] t₇u t₁h}  →
               k' ∼ v' ∈̃ node k₄ (node k₂ t₁ t₃ (max∼ bal)) (node k₆ t₅ t₇ (∼max bal)) ∼0 →
               k' ∼ v' ∈̃ node k₂ t₁ (node k₄ t₃ t₅ bal) ∼+ ⊎ k' ∼ v' ∈̃ t₇ ⊎ ((k' , v') ≡ k₆)
      proof2 here = inj₁ (right here)
      proof2 (left here) = inj₁ here
      proof2 (left (left x)) = inj₁ (left x)
      proof2 (left (right x)) = inj₁ (right (left x))
      proof2 (right here) = inj₂ (inj₂ P.refl)
      proof2 (right (left x)) = inj₁ (right (right x))
      proof2 (right (right x)) = inj₂ (inj₁ x)
      
    joinˡ⁺! k₄ (1# , node k₂ t₁ t₃ ∼-) t₅ ∼-  = 0# , node k₂ t₁ (node k₄ t₃ t₅ ∼0) ∼0 , {!!}
    joinˡ⁺! k₄ (1# , node k₂ t₁ t₃ ∼0) t₅ ∼-  = 1# , node k₂ t₁ (node k₄ t₃ t₅ ∼-) ∼+ , {!!}
    joinˡ⁺! k₂ (1# , t₁)               t₃ ∼0  = 1# , node k₂ t₁ t₃ ∼- , {!!}
    joinˡ⁺! k₂ (1# , t₁)               t₃ ∼+  = 0# , node k₂ t₁ t₃ ∼0 , {!!}
    joinˡ⁺! k₂ (0# , t₁)               t₃ bal = 0# , node k₂ t₁ t₃ bal , {!!}
   
  ------------------------------------------------------------------------
  -- Types and functions with hidden indices
   
  data Tree : Set (𝑼⟨Key⟩ ⊔ 𝑼⟨Value⟩ ⊔ 𝑼⟨<⟩) where
    tree : let open Extended-key in
           ∀ {h} → Indexed.Tree ⊥⁺ ⊤⁺ h → Tree
   
  empty : Tree
  empty = tree (Indexed.empty _)
   
  singleton : (k : Key) → Value k → Tree
  singleton k v = tree (Indexed.singleton k v _)
   
  insert : (k : Key) → Value k → Tree → Tree
  insert k v (tree t) = tree $ proj₂ $ Indexed.insert k v t _
   
  insertWith : (k : Key) → Value k → (Value k → Value k → Value k) →
               Tree → Tree
  insertWith k v f (tree t) = tree $ proj₂ $ Indexed.insertWith k v f t _
   
  delete : Key → Tree → Tree
  delete k (tree t) = tree $ proj₂ $ Indexed.delete k t
   
  lookup : (k : Key) → Tree → Maybe (Value k)
  lookup k (tree t) = Indexed.lookup k t
   
  map : ({k : Key} → Value k → Value k) → Tree → Tree
  map f (tree t) = tree $ Indexed.map f t
   
  infix 4 _∈?_
   
  _∈?_ : Key → Tree → Bool
  k ∈? t = is-just (lookup k t)
   
  headTail : Tree → Maybe (KV × Tree)
  headTail (tree (Indexed.leaf _)) = nothing
  headTail (tree {h = suc _} t)    with Indexed.headTail t
  ... | (k , _ , _ , t′) = just (k , tree (Indexed.castˡ _ t′))
   
  initLast : Tree → Maybe (Tree × KV)
  initLast (tree (Indexed.leaf _)) = nothing
  initLast (tree {h = suc _} t)    with Indexed.initLast t
  ... | (k , _ , _ , t′) = just (tree (Indexed.castʳ t′ _) , k)
   
  -- The input does not need to be ordered.
   
  fromList : List KV → Tree
  fromList = List.foldr (uncurry insert) empty
   
  -- Returns an ordered list.
   
  toList : Tree → List KV
  toList (tree t) = DiffList.toList (Indexed.toDiffList t)
   
  -- Naive implementations of union.
   
  unionWith : (∀ {k} → Value k → Value k → Value k) →
              -- Left → right → result.
              Tree → Tree → Tree
  unionWith f t₁ t₂ =
    List.foldr (λ { (k , v) → insertWith k v f }) t₂ (toList t₁)
   
  -- Left-biased.
   
  union : Tree → Tree → Tree
  union = unionWith const
   
  unionsWith : (∀ {k} → Value k → Value k → Value k) → List Tree → Tree
  unionsWith f ts = List.foldr (unionWith f) empty ts
   
  -- Left-biased.
   
  unions : List Tree → Tree
  unions = unionsWith const

-}


