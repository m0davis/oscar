module Sandbox where

{-
While trying to come up with a solution to a question I posed [here](http://stackoverflow.com/questions/31900036/proof-help-in-agda-node-balancing-in-data-avl), I discovered the acceptability (by Agda) of a refl proof depends in a strange way on the order of arguments of a function that is called on one side of the equation. In code below, see how all but one of the bottom 4 theorems are proved with refl.

Why the discrepancy? Does this represent a bug in Agda? How would I prove the remaining theorem (thm1)?
-}

  module ArgumentOrderMatters where

    open import Data.Nat
    open import Data.Product

    -- Stolen (with little modification) from Data.AVL

    data ℕ₂ : Set where
      0# : ℕ₂
      1# : ℕ₂

    infixl 6 _⊕_

    _⊕_ : ℕ₂ → ℕ → ℕ
    0# ⊕ n = n
    1# ⊕ n = suc n

    infix 4 _∼_⊔_

    data _∼_⊔_ : ℕ → ℕ → ℕ → Set where
      ∼+ : ∀ {n} →     n ∼ suc n ⊔ suc n
      ∼0 : ∀ {n} →     n ∼ n     ⊔ n
      ∼- : ∀ {n} → suc n ∼ n     ⊔ suc n

    max∼ : ∀ {i j m} → i ∼ j ⊔ m → m ∼ i ⊔ m
    max∼ ∼+ = ∼-
    max∼ ∼0 = ∼0
    max∼ ∼- = ∼0

    ∼max : ∀ {i j m} → i ∼ j ⊔ m → j ∼ m ⊔ m
    ∼max ∼+ = ∼0
    ∼max ∼0 = ∼0
    ∼max ∼- = ∼+

    -- for simplicity, this tree has no keys
    data Tree : ℕ → Set where
      leaf : Tree 0
      node : ∀ {l u h}
             (L : Tree l)
             (U : Tree u)
             (bal : l ∼ u ⊔ h) →
             Tree (suc h)

    -- similar to joinˡ⁺ from Data.AVL

    join : ∀ {hˡ hʳ h : ℕ} →
           (∃ λ i → Tree (i ⊕ hˡ)) →
           Tree hʳ →
           (bal : hˡ ∼ hʳ ⊔ h) →
           ∃ λ i → Tree (i ⊕ (suc h))
    join (1# , node t₁
                    (node t₃ t₅ bal)
                    ∼+) t₇ ∼-  = (0# , node 
                                            (node t₁ t₃ (max∼ bal))
                                            (node t₅ t₇ (∼max bal))
                                            ∼0)
    join (1# , node t₁ t₃ ∼-) t₅ ∼-  = (0# , node t₁ (node t₃ t₅ ∼0) ∼0)
    join (1# , node t₁ t₃ ∼0) t₅ ∼-  = (1# , node t₁ (node t₃ t₅ ∼-) ∼+)
    join (1# , t₁)            t₃ ∼0  = (1# , node t₁ t₃ ∼-)
    join (1# , t₁)            t₃ ∼+  = (0# , node t₁ t₃ ∼0)
    join (0# , t₁)            t₃ bal = (0# , node t₁ t₃ bal)

    -- just like join but with "bal" earlier in the argument list
    join' : ∀ {hˡ hʳ h : ℕ} →
           (bal : hˡ ∼ hʳ ⊔ h) →
           (∃ λ i → Tree (i ⊕ hˡ)) →
           Tree hʳ →
           ∃ λ i → Tree (i ⊕ (suc h))
    join' ∼- (1# , node t₁
                    (node t₃ t₅ bal)
                    ∼+) t₇  = (0# , node 
                                            (node t₁ t₃ (max∼ bal))
                                            (node t₅ t₇ (∼max bal))
                                            ∼0)
    join' ∼-  (1# , node t₁ t₃ ∼-) t₅ = (0# , node t₁ (node t₃ t₅ ∼0) ∼0)
    join' ∼-  (1# , node t₁ t₃ ∼0) t₅ = (1# , node t₁ (node t₃ t₅ ∼-) ∼+)
    join' ∼0  (1# , t₁)            t₃ = (1# , node t₁ t₃ ∼-)
    join' ∼+  (1# , t₁)            t₃ = (0# , node t₁ t₃ ∼0)
    join' bal (0# , t₁)            t₃ = (0# , node t₁ t₃ bal)

    open import Relation.Binary.PropositionalEquality

    thm0 : ∀ {h : ℕ} (tl : Tree h) (tr : Tree (suc h)) → join (0# , tl) tr ∼+ ≡ (0# , node tl tr ∼+)
    thm0 tl tr = refl

    thm1 : ∀ {h : ℕ} (tl : Tree (suc h)) (tr : Tree (suc h)) → join (1# , tl) tr ∼+ ≡ (0# , node tl tr ∼0)
    thm1 (node tl (node tl₁ tl₂ bal) ∼+) tr = refl
    thm1 (node tl leaf ∼0) tr = refl
    thm1 (node tl (node tl₁ tl₂ bal) ∼0) tr = refl
    thm1 (node tl leaf ∼-) tr = refl
    thm1 (node tl (node tl₁ tl₂ bal) ∼-) tr = refl  -- FIXME refl doesn't work here!

    thm0' : ∀ {h : ℕ} (tl : Tree h) (tr : Tree (suc h)) → join' ∼+ (0# , tl) tr ≡ (0# , node tl tr ∼+)
    thm0' tl tr = refl

    thm1' : ∀ {h : ℕ} (tl : Tree (suc h)) (tr : Tree (suc h)) → join' ∼+ (1# , tl) tr ≡ (0# , node tl tr ∼0)
    thm1' tl tr = refl -- refl works fine here, and all I did was switch the order of arguments to join(')

  module OpaqueContexts where

    open import Relation.Binary.PropositionalEquality

    data S : Set where
      s1 : S
      s2 : S

    f : S → S → S
    f s1 s1 = s2
    f s1 s2 = s2
    f s2 s2 = s2
    f _ _ = s1

    g : S → S → S
    g x y = f y x

    l : ∀ (s : S) → g (g s s) s ≡ s2
    l s1 = {!!}
    l s2 = {!!}

    f' : S → S
    f' s1 = s2
    f' s2 = s2

    g' : S → S
    g' x = f' x

    l' : ∀ (s : S) → g' s ≡ s2
    l' s1 = {!!}
    l' s2 = {!!}

    l'' : ∀ (s : S) → f' s ≡ s2
    l'' s1 = {!!}
    l'' s2 = {!!}

   

  module ReproduceWeirdnessinBalancingAVLActQ2 where

    open import Data.Nat
    open import Data.Product

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
    -- 1# ⊕ n = 1 + n
    1# ⊕ n = suc n

    -- i ⊕ n -1 = pred (i ⊕ n).

    _⊕_-1 : ℕ₂ → ℕ → ℕ
    i ⊕ zero  -1 = 0
    i ⊕ suc n -1 = i ⊕ n

    infix 4 _∼_⊔_

    -- If i ∼ j ⊔ m, then the difference between i and j is at most 1,
    -- and the maximum of i and j is m. _∼_⊔_ is used to record the
    -- balance factor of the AVL trees, and also to ensure that the
    -- absolute value of the balance factor is never more than 1.

    data _∼_⊔_ : ℕ → ℕ → ℕ → Set where
      ∼+ : ∀ {n} →     n ∼ suc n ⊔ suc n
      ∼0 : ∀ {n} →     n ∼ n     ⊔ n
      ∼- : ∀ {n} → suc n ∼ n     ⊔ suc n

    -- Some lemmas.

    max∼ : ∀ {i j m} → i ∼ j ⊔ m → m ∼ i ⊔ m
    max∼ ∼+ = ∼-
    max∼ ∼0 = ∼0
    max∼ ∼- = ∼0

    ∼max : ∀ {i j m} → i ∼ j ⊔ m → j ∼ m ⊔ m
    ∼max ∼+ = ∼0
    ∼max ∼0 = ∼0
    ∼max ∼- = ∼+
  
    data Exp : ℕ → Set where
      leaf : Exp 0
      node : ∀ {l u h}
             (L : Exp l)
             (U : Exp u)
             (bal : l ∼ u ⊔ h) →
             Exp (suc h)

    join : ∀ {hˡ hʳ h : ℕ} →
           (∃ λ i → Exp (i ⊕ hˡ)) →
           Exp hʳ →
           (bal : hˡ ∼ hʳ ⊔ h) →
           ∃ λ i → Exp (i ⊕ (suc h))
    join (1# , node t₁
                    (node t₃ t₅ bal)
                    ∼+) t₇ ∼-  = (0# , node 
                                            (node t₁ t₃ (max∼ bal))
                                            (node t₅ t₇ (∼max bal))
                                            ∼0)
    join (1# , node t₁ t₃ ∼-) t₅ ∼-  = (0# , node t₁ (node t₃ t₅ ∼0) ∼0)
    join (1# , node t₁ t₃ ∼0) t₅ ∼-  = (1# , node t₁ (node t₃ t₅ ∼-) ∼+)
    join (1# , t₁)            t₃ ∼0  = (1# , node t₁ t₃ ∼-)
    join (1# , t₁)            t₃ ∼+  = (0# , node t₁ t₃ ∼0)
    join (0# , t₁)            t₃ bal = (0# , node t₁ t₃ bal)

    open import Relation.Binary.PropositionalEquality

    join0 : ∀ {hˡ hʳ h : ℕ} →
           (bal : hˡ ∼ hʳ ⊔ h) →
           (∃ λ i → Exp (i ⊕ hˡ)) →
           Exp hʳ →
           ∃ λ i → Exp (i ⊕ (suc h))
    join0 bal tl tr = join tl tr bal

    lem0 : ∀ {h : ℕ} (tl : Exp (suc h)) (tr : Exp (suc h)) → join (1# , tl) tr ∼+ ≡ (0# , node tl tr ∼0)
    lem0 {h} tl tr = {!!} -- Goal: join (1# , tl) tr ∼+ ≡ (0# , node tl tr ∼0)

    lem1 : ∀ {h : ℕ} (tl : Exp h) (tr : Exp (suc h)) → join (0# , tl) tr ∼+ ≡ (0# , node tl tr ∼+)
    lem1 {h} tl tr = {!!} -- Goal: (0# , node tl tr ∼+) ≡ (0# , node tl tr ∼+)

    lem00 : ∀ {h : ℕ} (tl : Exp (suc h)) (tr : Exp (suc h)) → join0 ∼+ (1# , tl) tr ≡ (0# , node tl tr ∼0)
    lem00 {h} tl tr = {!!} -- Goal: join (1# , tl) tr ∼+ ≡ (0# , node tl tr ∼0)

    lem10 : ∀ {h : ℕ} (tl : Exp h) (tr : Exp (suc h)) → join0 ∼+ (0# , tl) tr ≡ (0# , node tl tr ∼+)
    lem10 {h} tl tr = {!!} -- Goal: (0# , node tl tr ∼+) ≡ (0# , node tl tr ∼+)

    join' : ∀ {hˡ hʳ h : ℕ} →
           (bal : hˡ ∼ hʳ ⊔ h) →
           (∃ λ i → Exp (i ⊕ hˡ)) →
           Exp hʳ →
           ∃ λ i → Exp (i ⊕ (suc h))
    join' ∼- (1# , node t₁
                    (node t₃ t₅ bal)
                    ∼+) t₇  = (0# , node 
                                            (node t₁ t₃ (max∼ bal))
                                            (node t₅ t₇ (∼max bal))
                                            ∼0)
    join' ∼-  (1# , node t₁ t₃ ∼-) t₅ = (0# , node t₁ (node t₃ t₅ ∼0) ∼0)
    join' ∼-  (1# , node t₁ t₃ ∼0) t₅ = (1# , node t₁ (node t₃ t₅ ∼-) ∼+)
    join' ∼0  (1# , t₁)            t₃ = (1# , node t₁ t₃ ∼-)
    join' ∼+  (1# , t₁)            t₃ = (0# , node t₁ t₃ ∼0)
    join' bal (0# , t₁)            t₃ = (0# , node t₁ t₃ bal)

    open import Relation.Binary.PropositionalEquality

    lem0' : ∀ {h : ℕ} (tl : Exp (suc h)) (tr : Exp (suc h)) → join' ∼+ (1# , tl) tr ≡ (0# , node tl tr ∼0)
    lem0' {h} tl tr = {!!}

    lem1' : ∀ {h : ℕ} (tl : Exp h) (tr : Exp (suc h)) → join' ∼+ (0# , tl) tr ≡ (0# , node tl tr ∼+)
    lem1' {h} tl tr = {!!} -- Goal: (0# , node tl tr ∼+) ≡ (0# , node tl tr ∼+)

    join'' : ∀ {hˡ hʳ h : ℕ} →
           (∃ λ i → Exp (i ⊕ hˡ)) →
           (bal : hˡ ∼ hʳ ⊔ h) →
           Exp hʳ →
           ∃ λ i → Exp (i ⊕ (suc h))
    join'' (1# , node t₁
                    (node t₃ t₅ bal)
                    ∼+) ∼- t₇  = (0# , node 
                                            (node t₁ t₃ (max∼ bal))
                                            (node t₅ t₇ (∼max bal))
                                            ∼0)
    join'' (1# , node t₁ t₃ ∼-) ∼-  t₅ = (0# , node t₁ (node t₃ t₅ ∼0) ∼0)
    join'' (1# , node t₁ t₃ ∼0) ∼-  t₅ = (1# , node t₁ (node t₃ t₅ ∼-) ∼+)
    join'' (1# , t₁)            ∼0  t₃ = (1# , node t₁ t₃ ∼-)
    join'' (1# , t₁)            ∼+  t₃ = (0# , node t₁ t₃ ∼0)
    join'' (0# , t₁)            bal t₃ = (0# , node t₁ t₃ bal)

    open import Relation.Binary.PropositionalEquality

    lem0'' : ∀ {h : ℕ} (tl : Exp (suc h)) (tr : Exp (suc h)) → join'' (1# , tl) ∼+ tr ≡ (0# , node tl tr ∼0)
    lem0'' {h} tl tr = {!!} -- Goal: join (1# , tl) tr ∼+ ≡ (0# , node tl tr ∼0)

    lem1'' : ∀ {h : ℕ} (tl : Exp h) (tr : Exp (suc h)) → join'' (0# , tl) ∼+ tr ≡ (0# , node tl tr ∼+)
    lem1'' {h} tl tr = {!!} -- Goal: (0# , node tl tr ∼+) ≡ (0# , node tl tr ∼+)


  module ReproduceWeirdnessinBalancingAVLAct where

    open import Data.Nat
    open import Data.Product

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
    -- 1# ⊕ n = 1 + n
    1# ⊕ n = suc n

    -- i ⊕ n -1 = pred (i ⊕ n).

    _⊕_-1 : ℕ₂ → ℕ → ℕ
    i ⊕ zero  -1 = 0
    i ⊕ suc n -1 = i ⊕ n

    infix 4 _∼_⊔_

    -- If i ∼ j ⊔ m, then the difference between i and j is at most 1,
    -- and the maximum of i and j is m. _∼_⊔_ is used to record the
    -- balance factor of the AVL trees, and also to ensure that the
    -- absolute value of the balance factor is never more than 1.

    data _∼_⊔_ : ℕ → ℕ → ℕ → Set where
      ∼+ : ∀ {n} →     n ∼ suc n ⊔ suc n
      ∼0 : ∀ {n} →     n ∼ n     ⊔ n
      ∼- : ∀ {n} → suc n ∼ n     ⊔ suc n
      -- ∼+ : ∀ {n} →     n ∼ 1 + n ⊔ 1 + n
      -- ∼0 : ∀ {n} →     n ∼ n     ⊔ n
      -- ∼- : ∀ {n} → 1 + n ∼ n     ⊔ 1 + n

    -- Some lemmas.

    max∼ : ∀ {i j m} → i ∼ j ⊔ m → m ∼ i ⊔ m
    max∼ ∼+ = ∼-
    max∼ ∼0 = ∼0
    max∼ ∼- = ∼0

    ∼max : ∀ {i j m} → i ∼ j ⊔ m → j ∼ m ⊔ m
    ∼max ∼+ = ∼0
    ∼max ∼0 = ∼0
    ∼max ∼- = ∼+
  
    data Exp : ℕ → Set where
      leaf : Exp 0
      node : ∀ {l u h}
             (L : Exp l)
             (U : Exp u)
             (bal : l ∼ u ⊔ h) →
             Exp (suc h)

    data ∈_ : ∀ {n} → Exp n → Set where
{-    
      here : ∀ {hˡ hʳ}
        {l : Exp hˡ}
        {r : Exp hʳ}
        {b : ∃ λ h → hˡ ∼ hʳ ⊔ h} →
        ∈ node l r (proj₂ b)
-}

    join : ∀ {hˡ hʳ h : ℕ} →
           (∃ λ i → Exp (i ⊕ hˡ)) →
           Exp hʳ →
           (bal : hˡ ∼ hʳ ⊔ h) →
           ∃ λ i → Exp (i ⊕ (suc h))
    join (1# , node t₁
                    (node t₃ t₅ bal)
                    ∼+) t₇ ∼-  = (0# , node 
                                            (node t₁ t₃ (max∼ bal))
                                            (node t₅ t₇ (∼max bal))
                                            ∼0)
    join (1# , node t₁ t₃ ∼-) t₅ ∼-  = (0# , node t₁ (node t₃ t₅ ∼0) ∼0)
    join (1# , node t₁ t₃ ∼0) t₅ ∼-  = (1# , node t₁ (node t₃ t₅ ∼-) ∼+)
    join (1# , t₁)            t₃ ∼0  = (1# , node t₁ t₃ ∼-)
    join (1# , t₁)            t₃ ∼+  = (0# , node t₁ t₃ ∼0)
    join (0# , t₁)            t₃ bal = (0# , node t₁ t₃ bal)

    open import Relation.Binary.PropositionalEquality
    open import Function
    open import Relation.Nullary.Negation

    -- lem : ∀ (h : ℕ) → (∃ λ hl → ∃ λ hr → ∃ λ tl → ∃ λ tr → hl ∼ hr ⊔ h → hl ≡ hr → proj₁ (join (1# , tl) tr ∼+) ≡ 0#)
    --lem : ∀ (hl hr h : ℕ) (bal : hl ∼ hr ⊔ h) (asdf : hl ≡ hr) (pb : bal ≡ ∼0) (tl : Exp (suc hl)) (tr : Exp (suc hr)) → proj₁ (join (1# , tl) tr ∼+) ≡ 0#
    -- lem = ?

    lem0 : ∀ {h : ℕ} (tl : Exp (suc h)) (tr : Exp (suc h)) → join (1# , tl) tr ∼+ ≡ (0# , node tl tr ∼0)
    lem0 {h} tl tr = {!!} -- Goal: join (1# , tl) tr ∼+ ≡ (0# , node tl tr ∼0)

    lem1 : ∀ {h : ℕ} (tl : Exp h) (tr : Exp (suc h)) → join (0# , tl) tr ∼+ ≡ (0# , node tl tr ∼+)
    lem1 {h} tl tr = {!!} -- Goal: (0# , node tl tr ∼+) ≡ (0# , node tl tr ∼+)

    lem : ∀ {h : ℕ} (tl : Exp (suc h)) (tr : Exp (suc h)) → proj₁ (join (1# , tl) tr ∼+) ≡ 0#
    lem {h} tl tr = {!!}

    lem' : ∀ (h : ℕ) (tl : Exp (suc h)) (tr : Exp (suc h)) → proj₁ (join (0# , tl) tr ∼0) ≡ 0#
    lem' h tl tr = refl

    lemJoinIsCorrect : ∀ {hˡ hʳ h}
        (itˡ : ∃ λ i → Exp (i ⊕ hˡ))
        (tʳ : Exp hʳ)
        (bal : hˡ ∼ hʳ ⊔ h) →
        ∈ proj₂ (join itˡ tʳ bal)
    lemJoinIsCorrect (0# , tˡ) tʳ bal = {!!} -- here
    -- lemJoinIsCorrect (1# , tˡ) tʳ ∼+ rewrite lem = here
    -- lemJoinIsCorrect {hˡ = hˡ} {hʳ = suc .hˡ} {h = suc .hˡ} (1# , node _ _ (∼0 {n = .hˡ})) (node _ _ (∼0 {n = .hˡ})) (∼+ {n = .hˡ}) =
    --  here {hˡ = suc hˡ} {hʳ = suc hˡ} {b = suc hˡ , ∼0 {n = suc hˡ}}
    lemJoinIsCorrect (1# , tˡ) tʳ _ {-rewrite (lem tˡ tʳ)-} = {!!}

{-
suc (proj₁ (_b_165 tˡ tʳ)) !=
proj₁ (join (1# , tˡ) tʳ ∼+) ⊕ suc (suc .hˡ) of type ℕ
when checking that the expression here has type
∈ proj₂ (join (1# , tˡ) tʳ ∼+)
-}

{-
/home/martin/Desktop/OSCAR/Sandbox.agda:102,7-69
suc (suc hˡ) !=
proj₁ (join (1# , node .L .U ∼0) (node .L₁ .U₁ ∼0) ∼+) ⊕
suc (suc hˡ)
of type ℕ
when checking that the expression
here {hˡ = suc hˡ} {hʳ = suc hˡ} {b = suc hˡ , ∼0 {n = suc hˡ}} has
type ∈ proj₂ (join (1# , node .L .U ∼0) (node .L₁ .U₁ ∼0) ∼+)
-}
        
--      lemJoinˡ⁺IsCorrect {hˡ = hˡ} K (1# , node _ _ _ (∼0 {n = ℕ.suc .hˡ})) (node _ _ _ (∼0 {n = ℕ.suc .hˡ})) (∼+ {n = .hˡ}) = {!!}
    -- lemJoinˡ⁺IsCorrect {hˡ = hˡ} {hʳ = ℕ.suc .hˡ} {h = ℕ.suc .hˡ} K (1# , node _ _ _ (∼0 {n = .hˡ})) (node _ _ _ (∼0 {n = .hˡ})) (∼+ {n = .hˡ}) = here {hˡ = ℕ.suc hˡ} {hʳ = ℕ.suc hˡ} (proj₂ K) (ℕ.suc hˡ , ∼0 {n = ℕ.suc hˡ})
    
    

  module inspectInspect where
    open import Relation.Binary.PropositionalEquality
    open import Relation.Nullary.Negation
    open import Data.Nat.Base
    open import Data.List.Base

    data Stuff : Set where
      0# : Stuff
      1# : Stuff
      2# : Stuff

    foo : List ℕ → Stuff → ℕ
    foo (x ∷ 2 ∷ xs) s = 5
    foo (0 ∷ 3 ∷ []) s = 3
    foo (1 ∷ xs) s = 1
    foo _ _ = 0 

    bar : ∀ (s : Stuff) → foo (1 ∷ []) s ≡ 1
    bar = {!!}

    
    

  module impossible-state where
    data State : Set where
      s1 : State
      s2 : State
      s3 : State


    moveState : State → State
    moveState s1 = s2
    moveState s2 = s3
    moveState s3 = s3

    open import Relation.Binary.PropositionalEquality
    open import Relation.Nullary.Negation

    lemo : s1 ≢ s2
    lemo = λ ()

    lem3' : ∀ (s : State) → moveState (moveState s) ≡ s3
    lem3' s = {!!}
    
    lem3 : ∀ (s : State) → moveState (moveState s) ≡ s3
    lem3 s1 = {!!}
    lem3 s2 = {!!}
    lem3 s3 = {!!}
    
    lem2 : ∀ (s : State) → moveState (moveState s) ≡ s3
    lem2 s with inspect moveState s
    lem2 s1 | b = {!!}
    lem2 s2 | b = {!!}
    lem2 s3 | b = {!!}
    
    lem : ∀ (s : State) → moveState (moveState s) ≡ s3
    lem s with moveState s | inspect moveState s
    lem s1 | s1 | [ eq ] = contradiction eq (λ ())
    lem s2 | s1 | [ eq ] = {!!}
    lem s3 | s1 | [ eq ] = {!!}
    lem s | s2 | _ = {!!}
    lem s | s3 | _ = {!!}

  module hide-and-go-seek where
    open import Data.Nat.Base
    open import Data.Product
    
    data Shown : ℕ → Set where
      s1 : Shown 0
      s2 : (n : ℕ) → Shown (suc n)

    data Hidden : Set where
      shown : ∀ n → Shown n → Hidden

    unhide : Hidden → ∃ λ i → Shown i
    unhide (shown n x) = n , x

    id2 : Hidden → Hidden
    id2 h = shown (zero) {!!}

  module AVL where

    open import Relation.Binary
    open import Relation.Binary.PropositionalEquality as P using (_≡_)

    module AVL-Instantiated
      {k v ℓ}
      {Key : Set k} (Value : Key → Set v)
      {_<_ : Rel Key ℓ}
      (isStrictTotalOrder : IsStrictTotalOrder _≡_ _<_)  
      where

      module TreeToIndexedTree where
        import Data.AVL Value isStrictTotalOrder as AVL
        open AVL using (Tree; tree; module Indexed; module Extended-key)

        toIndexedTree : ∀ h → Tree → Indexed.Tree Extended-key.⊥⁺ Extended-key.⊤⁺ h
        toIndexedTree h (tree x) = {!!}

  module equivalences where

    open import Relation.Binary
    open import Relation.Binary.Core
    open import Relation.Binary.PropositionalEquality
    open import Relation.Nullary
    open import Relation.Nullary.Negation

    module obvious-facts
      { α ℓ }
      ( A : Set α )
      { _≞_ : Rel A ℓ }
      ( isDecEquivalence : IsDecEquivalence _≞_ )
      where

      open IsDecEquivalence isDecEquivalence

      proveMe : ∀ ( a : A ) → a ≞ a
      proveMe = λ _ → IsEquivalence.refl
                        (IsDecEquivalence.isEquivalence isDecEquivalence)

      open import Data.Product

      thmNonequalityOfYesAndNo : ∀ {p} {P : Set p} (py : P) (pn : ¬ P) → ¬ (yes py ≡ no pn)
      thmNonequalityOfYesAndNo py pn x = pn py

      thmNonequalityOfYesAndNo' : ∀ {p} {P : Set p} (py : P) (pn : ¬ P) → ¬ (no pn ≡ yes py)
      thmNonequalityOfYesAndNo' py pn x = pn py
      
      thmEquivalence : ∀ ( a : A ) → ( ∃ λ p → ( a ≟ a ) ≡ yes p )
      thmEquivalence a with a ≟ a
      thmEquivalence a | yes p = p , _≡_.refl
      thmEquivalence a | no np with proveMe a
      thmEquivalence a | no np | pma with thmNonequalityOfYesAndNo' pma np
      thmEquivalence a | no np | pma | t = contradiction pma np

  module prove-inverse where

    module using-simple-intermediate-data where

      open import Relation.Binary.PropositionalEquality

      data end : Set where
        home : end
        blood : end
        office : end

      data intermediate : Set where
        Ferry : intermediate
        Eighth : intermediate
        Oak : intermediate

      f : end → intermediate
      f home = Ferry
      f blood = Eighth
      f office = Oak

      f-inverse : intermediate → end
      f-inverse Ferry = home
      f-inverse Eighth = blood
      f-inverse Oak = office

      proveMe : ∀ x → f-inverse (f x) ≡ x
      proveMe home = refl
      proveMe blood = refl
      proveMe office = refl

    module map-as-a-list-of-products where

      open import Data.Product
      open import Data.List.Base
      open import Data.Maybe.Base
      open import Relation.Binary
      open import Relation.Binary.Core
      open import Relation.Binary.PropositionalEquality
      open import Relation.Nullary
      open import Relation.Nullary.Negation

      module map
             { a b ℓ }
             ( A : Set a ) ( B : Set b )
             { _≞_ : Rel A ℓ }
             ( isDecEquivalence : IsDecEquivalence _≞_ )
        where

        open IsDecEquivalence isDecEquivalence
        
        M : _
        M = List ( A × B )

        empty : M
        empty = []

        insert : A → B → M → M
        insert a b m = ( a ,′ b ) ∷ m

        retrieve : A → M → Maybe B
        retrieve a [] = nothing
        retrieve a ( ( a' , b ) ∷ l ) with a ≟ a'
        retrieve a ( ( a' , b ) ∷ l ) | yes _ = just b
        retrieve a ( ( a' , b ) ∷ l ) | no _ = retrieve a l

        singleton : A → B → M
        singleton a b = insert a b empty

        refd : ∀ ( a : A ) → a ≞ a
        refd = λ _ → IsEquivalence.refl
                     (IsDecEquivalence.isEquivalence isDecEquivalence)

        thmEquivalence : ∀ ( a : A ) → ( ∃ λ p → ( a ≟ a ) ≡ yes p )
        thmEquivalence a with a ≟ a
        thmEquivalence a | yes p = p , _≡_.refl
        thmEquivalence a | no ¬p with refd a
        ... | ra = contradiction ra ¬p

        proveMe : ∀ ( a : A ) ( b : B ) → retrieve a ( singleton a b ) ≡ just b
        proveMe a b with a ≟ proj₁ (a ,′ b)
        proveMe a b | yes p = _≡_.refl
        proveMe a b | no ¬p = contradiction ¬p (λ x → contradiction (refd a) ¬p)
        
      module map-unit-tests where

        open import Data.Nat
        open import Data.String
        
        open map ℕ String ( DecTotalOrder.Eq.isDecEquivalence decTotalOrder )

        proveMe'' : retrieve 83770 ( singleton 83770 "world" ) ≡ just "world"
        proveMe'' = refl

  module with-impossible-patterns where

    open import Relation.Binary
    open import Relation.Binary.PropositionalEquality as P using (_≡_)

    data Foo : Set where
      foo : Foo

    data Bar : Set where
      bar : Foo → Bar
      bir : Bar
      bor : Foo → Bar

    qux : Foo
    qux = foo

    baz : Bar
    baz = bar qux

    como : baz ≡ bar foo
    como with baz
    como | bar x = P.refl
    como | bir = P.refl
    como | bor x = P.refl

  module AVL' where

    import Data.AVL as Mp
    import Data.AVL.IndexedMap as Map
    import Relation.Binary
    import Relation.Binary.Core
    import Agda.Primitive
    import Data.Product
    import Data.AVL
    import Level

    open import Data.Vec using (Vec; _∷_; [])
    open import Data.Nat
    open import Data.String using (String)
    open import Relation.Binary
    open import Relation.Binary.Sum
    open import Relation.Binary.Product.StrictLex

    import Data.Nat.Properties as ℕ

    open import Data.Product

    mt : Mp.Tree (Vec String) (StrictTotalOrder.isStrictTotalOrder ℕ.strictTotalOrder)
    mt = Mp.empty (Vec String) (StrictTotalOrder.isStrictTotalOrder ℕ.strictTotalOrder)

  module Feng' where

    open import Data.Nat
    open import Data.Sum

    data Feng : Set where

    less? : (n m : ℕ) → n < m ⊎ m ≤ n
    less? 0 0 = inj₂ z≤n
    less? 0 (suc n) = inj₁ (s≤s z≤n)
    less? (suc n) 0 = inj₂ z≤n
    less? (suc n) (suc m) with less? n m
    less? (suc n) (suc m) | inj₁ n<m = inj₁ (s≤s n<m)
    less? (suc n) (suc m) | inj₂ m≤n = inj₂ (s≤s m≤n)

    module equalities-of-nat where

      open import Data.Unit using (⊤; tt)
      open import Data.Empty using (⊥)
      open import Data.Bool.Base using (if_then_else_; Bool; true; false)
      open import Relation.Binary.Core using (_≡_; Reflexive; refl)

      data list {l} (e : Set l) : Set l where
        Nil : list e
        Cons : e -> list e -> list e

      data nat : Set where
        Base : nat
        Succ : nat -> nat

      _++_ : nat -> nat -> nat
      Base ++ x₁ = x₁
      Succ x ++ x₁ = Succ (x ++ x₁)

      member : forall {E : Set} -> (E -> E -> Bool) -> E -> list E -> Set
      member eq e Nil = ⊥
      member eq e (Cons e' l) = if eq e e' then ⊤ else (member eq e l)

      natEquality : nat -> nat -> Bool
      natEquality Base Base = true
      natEquality Base (Succ x₂) = false
      natEquality (Succ x₁) Base = false
      natEquality (Succ x₁) (Succ x₂) = natEquality x₁ x₂

      m0 : member natEquality Base (Cons Base Nil)
      m0 = tt

      m1 : member natEquality (Succ Base) (Cons (Succ Base) Nil)
      m1 = tt

      mall : ∀ (n : nat) → member natEquality n (Cons n Nil)
      mall Base = tt
      mall (Succ n) = mall n

      nEGeneral : ∀ (n : nat) → natEquality n n ≡ true
      nEGeneral Base = refl
      nEGeneral (Succ n) = nEGeneral n

      mallGeneral : ∀ (n : nat) (l : list nat) → member natEquality n (Cons n l)
      mallGeneral n Nil = mall n
      mallGeneral Base (Cons n l) = tt
      mallGeneral (Succ n) (Cons Base l) = mallGeneral (Succ n) l
      mallGeneral (Succ n) (Cons (Succ n') l) rewrite nEGeneral n = tt

      crazyListCondition : list nat → Set
      crazyListCondition l = member natEquality (Succ Base) l

      test1 : (a : nat) (b : nat) (c : nat) → list nat
      test1 = λ a b c → Nil

      test2 : (a : nat) → (b : nat) → (c : nat) → list nat
      test2 = λ a b c → Nil

      test2' : (a b c : nat) → list nat
      test2' = λ a b c → Nil

      test2'' : nat → nat → nat → list nat
      test2'' = λ a b c → Nil

      test3' : (a a a : nat) → list nat
      test3' = λ a a a → Cons a Nil

      test3 : list nat
      test3 = test3' Base (Succ Base) Base

      myListFunction : (l : list nat) {_ : crazyListCondition l} → list nat
      myListFunction Nil {_} = Nil
      myListFunction (Cons x l) {_} = Cons x l

      my2 : list nat
      my2 = myListFunction (Cons (Succ Base) Nil) {tt}

      module asdf where
        atest1 : (a : nat) (b : nat) (c : nat) → list nat
        atest1 _ _ _ = Nil

        atest2 : (a : nat) → (b : nat) → (c : nat) → list nat
        atest2 = λ a b c → Nil

        atest2' : (a b c : nat) → list nat
        atest2' = λ a b c → Nil

        atest2'' : nat → nat → nat → list nat
        atest2'' = λ a b c → Nil

        atest3' : (a a a : nat) → list nat
        atest3' = λ a a a → Cons a Nil

        atest3 : list nat
        atest3 = test3' Base (Succ Base) Base

        amyListFunction : (l : list nat) {_ : crazyListCondition l} → list nat
        amyListFunction Nil {_} = Nil
        amyListFunction (Cons x l) {_} = Cons x l

        amy2 : list nat
        amy2 = myListFunction (Cons (Succ Base) Nil) {tt}

      module Ooooops where

        open import Function

        data Oops : Set → Set where
          oops : Bool → Oops Bool
          ok : ℕ → Oops ℕ

        w : ℕ → Oops Bool 
        w 0 = oops true
        w (suc n) = oops false

        f : ∀ {x : Set} → Oops x → ℕ
        f x₁ = zero

        open import Category.Functor
