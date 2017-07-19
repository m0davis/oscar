
module Test𝓢urjectivityWithOverlapping𝓢urjection where

open import Oscar.Prelude
open import Oscar.Data
open import Oscar.Class

module !1 where

  postulate
    A : Set
    B : Set
    _~A~_ : A → A → Set
    _~B~_ : B → B → Set
    s1 : A → B
    s2 : A → B
    f1 : ∀ {x y} → x ~A~ y → s1 x ~B~ s1 y
    f2 : ∀ {x y} → x ~A~ y → s2 x ~B~ s2 y

  instance

    𝓢urjection1 : 𝓢urjection A B
    𝓢urjection1 = ∁ s1

    𝓢urjection2 : 𝓢urjection A B
    𝓢urjection2 = ∁ s2

    [𝓢urjectivity]AB : [𝓢urjectivity] _~A~_ _~B~_
    [𝓢urjectivity]AB = ∁

    𝓢urjectivity1 : 𝓢urjectivity _~A~_ _~B~_
    𝓢urjectivity.surjectivity 𝓢urjectivity1 = f1

    𝓢urjectivity2 : 𝓢urjectivity _~A~_ _~B~_
    𝓢urjectivity.surjectivity 𝓢urjectivity2 = f2

  test1 : ∀ {x y} → x ~A~ y → s1 x ~B~ s1 y
  test1 = surjectivity

  test2 : ∀ {x y} → x ~A~ y → s2 x ~B~ s2 y
  test2 = surjectivity

module !2 where

  postulate
    A : Set
    B : Set
    _~A~_ : A → A → Set
    s1 : A → B
    s2 : A → B
    f1 : ∀ {x y} → x ~A~ y → s1 x ≡ s1 y
    f2 : ∀ {x y} → x ~A~ y → s2 x ≡ s2 y

  instance

    𝓢urjection1 : 𝓢urjection A B
    𝓢urjection1 = ∁ s1

    𝓢urjection2 : 𝓢urjection A B
    𝓢urjection2 = ∁ s2

    [𝓢urjectivity]AB : [𝓢urjectivity] _~A~_ Proposequality⟦ B ⟧
    [𝓢urjectivity]AB = ∁

    𝓢urjectivity1 : 𝓢urjectivity _~A~_ _≡_
    𝓢urjectivity.surjectivity 𝓢urjectivity1 = f1

    𝓢urjectivity2 : 𝓢urjectivity _~A~_ _≡_
    𝓢urjectivity.surjectivity 𝓢urjectivity2 = f2

  test-rhs-1 : ∀ {x y} → x ~A~ y → s2 x ≡ s2 y
  test-rhs-1 = surjectivity

  test-rhs-2 : ∀ {x y} → x ~A~ y → s2 x ≡ s2 y
  test-rhs-2 {x} {y} x~A~y = Proposequality⟦ B ⟧ (s2 x) (s2 y) ∋ surjectivity x~A~y

  test-rhs-3 : ∀ {x y} → x ~A~ y → s2 x ≡ s2 y
  test-rhs-3 {x} {y} x~A~y = (Proposequality⟦ B ⟧ on s2) x y ∋ surjectivity x~A~y

  test-lhs-1 : ∀ {x y} → x ~A~ y → s2 x ≡ s2 y
  test-lhs-1 x~A~y rewrite surjectivity ⦃ r = 𝓢urjectivity2 ⦄ x~A~y = ∅

  test-lhs-2 : ∀ {x y} → x ~A~ y → s2 x ≡ s2 y
  test-lhs-2 x~A~y rewrite surjectivity {_∼₂_ = Proposequality} ⦃ 𝓢urjection2 ⦄ x~A~y = ∅

  test-lhs-3 : ∀ {x y} → x ~A~ y → s2 x ≡ s2 y
  test-lhs-3 x~A~y rewrite Proposequality (s1 _) _ ∋ surjectivity x~A~y = magic

  test-lhs-4 : ∀ {x y} → x ~A~ y → s2 x ≡ s2 y
  test-lhs-4 x~A~y rewrite Proposequality (s2 _) _ ∋ surjectivity x~A~y = ∅

  test-lhs-5 : ∀ {x y} → x ~A~ y → s2 x ≡ s2 y
  test-lhs-5 x~A~y rewrite (Proposequality on s2) _ _ ∋ surjectivity x~A~y = ∅
