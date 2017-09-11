
module Test.𝓢urjectivityWithOverlapping𝓢urjection where

open import Oscar.Prelude
open import Oscar.Data.Proposequality
open import Oscar.Class
open import Oscar.Class.Surjection
open import Oscar.Class.Smap
-- import Everything -- FIXME

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

    𝓢urjection1 : Surjection.class A B
    𝓢urjection1 = ∁ s1

    𝓢urjection2 : Surjection.class A B
    𝓢urjection2 = ∁ s2

    𝓢urjectivity1 : Smap!.class _~A~_ _~B~_
    𝓢urjectivity1 .⋆ _ _ = f1

    𝓢urjectivity2 : Smap!.class _~A~_ _~B~_
    𝓢urjectivity2 .⋆ _ _ = f2

  test1 : ∀ {x y} → x ~A~ y → s1 x ~B~ s1 y
  test1 = smap

  test2 : ∀ {x y} → x ~A~ y → s2 x ~B~ s2 y
  test2 = smap

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

    𝓢urjection1 : Surjection.class A B
    𝓢urjection1 = ∁ s1

    𝓢urjection2 : Surjection.class A B
    𝓢urjection2 = ∁ s2

    𝓢urjectivity1 : Smap!.class _~A~_ _≡_
    𝓢urjectivity1 .⋆ _ _ = f1

    𝓢urjectivity2 : Smap!.class _~A~_ _≡_
    𝓢urjectivity2 .⋆ _ _ = f2

  test-rhs-1 : ∀ {x y} → x ~A~ y → s2 x ≡ s2 y
  test-rhs-1 = smap

  test-rhs-2 : ∀ {x y} → x ~A~ y → s2 x ≡ s2 y
  test-rhs-2 {x} {y} x~A~y = Proposequality⟦ B ⟧ (s2 x) (s2 y) ∋ smap x~A~y

  test-rhs-3 : ∀ {x y} → x ~A~ y → s2 x ≡ s2 y
  test-rhs-3 {x} {y} x~A~y = (Proposequality⟦ B ⟧ on s2) x y ∋ smap x~A~y

  test-lhs-1 : ∀ {x y} → x ~A~ y → s2 x ≡ s2 y
  test-lhs-1 x~A~y rewrite smap ⦃ 𝓢urjectivity2 ⦄ x~A~y = ∅

  test-lhs-2 : ∀ {x y} → x ~A~ y → s2 x ≡ s2 y
  test-lhs-2 x~A~y rewrite smap {_∼₂_ = Proposequality} { surjection ⦃ 𝓢urjection2 ⦄} x~A~y = ∅

  test-lhs-3 : ∀ {x y} → x ~A~ y → s2 x ≡ s2 y
  test-lhs-3 x~A~y rewrite Proposequality (s1 _) _ ∋ smap x~A~y = magic

  test-lhs-4 : ∀ {x y} → x ~A~ y → s2 x ≡ s2 y
  test-lhs-4 x~A~y rewrite Proposequality (s2 _) _ ∋ smap x~A~y = ∅

  test-lhs-5 : ∀ {x y} → x ~A~ y → s2 x ≡ s2 y
  test-lhs-5 x~A~y rewrite (Proposequality on s2) _ _ ∋ smap x~A~y = ∅

  test-lhs-6 : ∀ {x y} → x ~A~ y → s2 x ≡ s2 y
  test-lhs-6 x~A~y rewrite smap⟦ Proposequality / s2 / s2 ⟧ x~A~y = ∅

  test-lhs-6' : ∀ {x y} → x ~A~ y → s2 x ≡ s2 y
  test-lhs-6' x~A~y rewrite ≡-Smap.method _ s2 s2 x~A~y = ∅

  test-lhs-7 : ∀ {x y} → x ~A~ y → s2 x ≡ s2 y
  test-lhs-7 x~A~y rewrite ≡-smap⟦ s2 ⟧ s2 x~A~y = ∅
