
open import Oscar.Prelude
open import Oscar.Class.Reflexivity

module Test.Test6 where


module TestReflexivity where

  postulate

    X : Set
    F : X → X → Set
    instance ReflexivityF : Reflexivity.class F

  test : ∀ {y} → F y y
  test {y = y} = reflexivity

  {-
  Goal: F y y
  Have: {𝔬 : Ł} {𝔒 : Set 𝔬} {𝔯 : Ł} {_∼_ : 𝔒 → 𝔒 → Set 𝔯}
        {{r : 𝓡eflexivity {𝔬} {𝔒} {𝔯} _∼_}} {x  : 𝔒} →
        x ∼ x
  ————————————————————————————————————————————————————————————
  y : X

  _𝔬1 : Ł
  _𝔒1 : Set _𝔬1
  _𝔯1 : Ł
  __∼1_ : _𝔒1 → _𝔒1 → Set _𝔯1
  _r1 : 𝓡eflexivity {_𝔬1} {_𝔒1} {_𝔯1} __∼1_
  _x1 : _𝔒1

  __∼1_ _x1 _x1 = F y y

  __∼1_ := λ s t → F s t
  _x1 := y

  __∼1_ := λ s t → F t s
  _x1 := y

  __∼1_ := λ s t → F y y

  λ {𝔬} {𝔒} {𝔯} {_∼_} → 𝓡eflexivity.reflexivity
  -}


module _Indexed where

  record I (M : Set) (N : M → Set) : Set where
    field f : ∀ {m} → N m

  open I ⦃ … ⦄

  postulate
    A : Set
    B : A → Set
    instance iB : I A B

  test : ∀ {a} → B a
  test {a = a} = f


module IndexedTotal1Var where

  record Indexed (M : Set) (N : M → Set) : Set where
    field fooI : ∀ {m} → N m

  open Indexed ⦃ … ⦄

  record Total (N : Set) : Set where
    field fooT : N

  open Total ⦃ … ⦄

  postulate
    A : Set
    B : A → Set
    B' : A → Set
    instance iIndexed : Indexed A B
    instance iTotal : ∀ {x} → Total (B x)
    instance iIndexed' : Indexed A B'
    instance iTotal' : ∀ {x} → Total (B' x)

  testIndexed : ∀ {a} → B a
  testIndexed {a = a} = fooI

  testTotal : ∀ {a} → B a
  testTotal {a = a} = fooT

  {-

  Goal: B a
  Have: {M : Set} {N : M → Set} {{r : R M N}} {m : M} → N m
  ————————————————————————————————————————————————————————————
  a : A

  _M : Set
  _N : _M → Set
  _r : R _M _N
  _m : _M

  _N _m = B a

  no unconstrained metavariables in type of _r because _M occurs in the type of _N and _N _m = B a

  candidate#1
  _r := iR : R A B
  _M = A
  _M := A
  _N = B
  _N := B

  now we can solve for _m:
  _N := B
  _N _m = B a
  B _m = B a
  _m = a
  _m := a

  -}


module Indexed≡Total2Prop where

  open import Oscar.Data.Proposequality

  record Indexed {M : Set} (N : M → Set) (s : ∀ {m} → N m → N m) (S : ∀ {m} → N m → N m → Set) {F : ∀ {m} (n : N m) → Set} ⦃ _ : (λ {m} (n : N m) → S n (s n)) ≡ F ⦄ : Set where
    field fooI : ∀ {m} {n : N m} → S n (s n)

  open Indexed ⦃ … ⦄

  record Total {N : Set} (s : N → N) (S : N → N → Set) : Set where
    field fooT : ∀ n → S n (s n)

  open Total ⦃ … ⦄

  postulate
    A : Set
    B : A → Set
    f : ∀ {x} → B x → B x
    F : ∀ {x} → B x → B x → Set

    instance iIndexed : Indexed B f F ⦃ ∅ ⦄
    instance iTotal : ∀ {x} → Total (f {x}) (F {x})

  testIndexed : ∀ {a} {b : B a} → F b (f b)
  testIndexed = fooI ⦃ ∅ ⦄

  testTotal : ∀ {a} (b : B a) → F b (f b)
  testTotal = fooT {S = F}


module Indexed≡Total1Prop where

  open import Oscar.Data.Proposequality

  record Indexed {M : Set} (N : M → Set) (s : ∀ {m} → N m → N m) (S : ∀ {m} → N m → Set) {F : ∀ {m} (n : N m) → Set} ⦃ _ : (λ {m} (n : N m) → S (s n)) ≡ F ⦄ : Set where
    field fooI : ∀ {m} {n : N m} → S (s n)

  open Indexed ⦃ … ⦄

  record Total {N : Set} (s : N → N) (S : N → Set) : Set where
    field fooT : ∀ n → S (s n)

  open Total ⦃ … ⦄

  postulate
    A : Set
    B : A → Set
    f : ∀ {x} → B x → B x
    F : ∀ {x} → B x → Set

    instance iIndexed : Indexed B f F ⦃ ∅ ⦄
    instance iTotal : ∀ {x} → Total (f {x}) (F {x})

  testIndexed : ∀ {a} {b : B a} → F (f b)
  testIndexed = fooI ⦃ ∅ ⦄

  testTotal : ∀ {a} (b : B a) → F (f b)
  testTotal = fooT {S = F}

module Indexed≡Total1Prop<Constraint where

  open import Oscar.Data.Proposequality

  data Luft {a} {A : Set a} (x : A) : Set where
    instance ∅ : Luft x

  record Indexed {M : Set} (N : M → Set) (s : ∀ {m} → N m → N m) (S : ∀ {m} → N m → Set) ⦃ _ : Luft (λ {m} → s {m}) ⦄ : Set where
    field fooI : ∀ {m} {n : N m} → S (s n)

  open Indexed ⦃ … ⦄

  record Total {N : Set} (s : N → N) (S : N → Set) : Set where
    field fooT : ∀ n → S (s n)

  open Total ⦃ … ⦄

  postulate
    A : Set
    B : A → Set
    f : ∀ {x} → B x → B x
    F : ∀ {x} → B x → Set

    instance iIndexed : Indexed B f F
    instance iTotal : ∀ {x} → Total (f {x}) (F {x})

  testIndexed : ∀ {a} {b : B a} → F (f b)
  testIndexed = fooI ⦃ ∅ ⦄

  testTotal : ∀ {a} (b : B a) → F (f b)
  testTotal = fooT {S = F}

module Indexed≡Total2Prop<Constraint-Multi where

  open import Oscar.Data.Proposequality

  data Luft {a} {A : Set a} (x : A) : Set where
    instance ∅ : Luft x

  record Indexed {M : Set} (N : M → Set) (s : ∀ {m} → N m → N m) (S : ∀ {m} → N m → N m → Set) ⦃ _ : Luft (λ {m} → s {m}) ⦄ : Set where
    field fooI : ∀ {m} {n : N m} → S n (s n)

  open Indexed ⦃ … ⦄

  record Total {N : Set} (s : N → N) (S : N → N → Set) : Set where
    field fooT : ∀ n → S n (s n)

  open Total ⦃ … ⦄

  postulate
    A : Set
    B : A → Set
    f f' : ∀ {x} → B x → B x
    F F' : ∀ {x} → B x → B x → Set

    instance _ : Indexed B f F
    instance _ : Indexed B f' F
    instance _ : Indexed B f F'
    instance _ : Indexed B f' F'
    instance _ : ∀ {x} → Total (f {x}) (F {x})

  testIndexed : ∀ {a} {b : B a} → F b (f b)
  testIndexed = fooI ⦃ ∅ ⦄

  testIndexed2 : ∀ {a} {b : B a} → F (f b) (f (f b))
  testIndexed2 = fooI ⦃ ∅ ⦄

  testTotal : ∀ {a} (b : B a) → F b (f b)
  testTotal = fooT {S = F}

module Indexed≡Total2Prop<Constraint-Multi-2Fun where

  open import Oscar.Data.Proposequality

  data Luft {a} {A : Set a} (x : A) : Set where
    instance ∅ : Luft x

  record Indexed {M : Set} (N : M → Set) (s t : ∀ {m} → N m → N m) (S : ∀ {m} → N m → N m → Set) ⦃ _ : Luft (λ {m} → s {m}) ⦄ ⦃ _ : Luft (λ {m} → t {m}) ⦄ : Set where
    field fooI : ∀ {m} {n : N m} → S (t n) (s n)

  fooI : {M : Set} {N : M → Set} {s t : ∀ {m} → N m → N m} {S : ∀ {m} → N m → N m → Set} ⦃ _ : Indexed N s t S ⦄ → ∀ {m} {n : N m} → S (t n) (s n)
  fooI ⦃ I ⦄ = Indexed.fooI I -- equivalently, fooI = Indexed.fooI ⦃ ∅ ⦄ ⦃ ∅ ⦄ !

  record Total {N : Set} (s t : N → N) (S : N → N → Set) ⦃ _ : Luft s ⦄ ⦃ _ : Luft t ⦄ : Set where
    field fooT : ∀ {n} → S (t n) (s n)

  fooT : {N : Set} {s t : N → N} {S : N → N → Set} ⦃ _ : Total s t S ⦄ → ∀ {n : N} → S (t n) (s n)
  fooT ⦃ I ⦄ = Total.fooT I

  IndexedTotal : {M : Set} (N : M → Set) (s t : ∀ {m} → N m → N m) (S : ∀ {m} → N m → N m → Set) → Set
  IndexedTotal _ s t S = ∀ {x} → Total (s {x}) (t {x}) (S {x})

  postulate
    A : Set
    B : A → Set
    f f' : ∀ {x} → B x → B x
    g g' : ∀ {x} → B x → B x
    F F' : ∀ {x} → B x → B x → Set

    instance _ : Indexed B f f F
    instance _ : Indexed B f' g F
    instance _ : Indexed B f g F'
    instance _ : Indexed B f' g F'
    instance _ : IndexedTotal B f f F
    instance _ : IndexedTotal B f' g F
    instance _ : IndexedTotal B f g F'
    instance _ : IndexedTotal B f' g F'
    instance _ : Indexed B f g F
    -- instance _ : Indexed B (λ b → f (g' b)) (λ b → g (g' b)) F -- this would overlap with the above
    instance _ : ∀ {x} → Total (f {x}) (g {x}) (F {x})

  testIndexed : ∀ {a} {b : B a} → F (g b) (f b)
  testIndexed = fooI

  testIndexed2 : ∀ {a} {b : B a} → F (g (g' b)) (f (g' b))
  testIndexed2 = fooI

  testIndexed3 : ∀ {a} {b : B a} → F (f (g' b)) (f (g' b))
  testIndexed3 = fooI

  testTotal : ∀ {a} {b : B a} → F (g b) (f b)
  testTotal = fooT

module Indexed≡Total2Prop<Constraint-Multi-2Fun-NoIndexedRecord where

  open import Oscar.Data.Proposequality

  data Luft {a} {A : Set a} (x : A) : Set where
    instance ∅ : Luft x

  record Total {N : Set} (s t : N → N) (S : N → N → Set) ⦃ _ : Luft s ⦄ ⦃ _ : Luft t ⦄ : Set where
    field fooT : ∀ {n} → S (t n) (s n)

  fooT : {N : Set} {s t : N → N} {S : N → N → Set} ⦃ _ : Total s t S ⦄ → ∀ {n : N} → S (t n) (s n)
  fooT ⦃ I ⦄ = Total.fooT I

  Indexed : {M : Set} (N : M → Set) (s t : ∀ {m} → N m → N m) (S : ∀ {m} → N m → N m → Set) (x : M) → Set
  Indexed _ s t S x = Total (s {x}) (t {x}) (S {x})

  IndexedTotal : {M : Set} (N : M → Set) (s t : ∀ {m} → N m → N m) (S : ∀ {m} → N m → N m → Set) → Set
  IndexedTotal _ s t S = ∀ {x} → Total (s {x}) (t {x}) (S {x})

  fooI : {M : Set} {N : M → Set} {s t : ∀ {m} → N m → N m} {S : ∀ {m} → N m → N m → Set} ⦃ _ : IndexedTotal N s t S ⦄ → ∀ {m} {n : N m} → S (t n) (s n)
  fooI = fooT

  fooI' : {M : Set} {N : M → Set} → ∀ {m} {s t : N m → N m} {S : N m → N m → Set} ⦃ _ : Total s t S ⦄ → {n : N m} → S (t n) (s n)
  fooI' = fooT

  postulate
    A : Set
    B : A → Set
    f f' : ∀ {x} → B x → B x
    g g' : ∀ {x} → B x → B x
    F F' : ∀ {x} → B x → B x → Set

    instance _ : IndexedTotal B f f F
    instance _ : IndexedTotal B f' g F
    instance _ : IndexedTotal B f g F'
    instance _ : IndexedTotal B f' g F'
    instance _ : IndexedTotal B f g F
    -- instance _ : Indexed B (λ b → f (g' b)) (λ b → g (g' b)) F -- this would overlap with the above
    -- instance _ : ∀ {x} → Total (f {x}) (g {x}) (F {x})


  module _ {a a' : A} (b : B a) (b' : B a') where
    postulate instance _ : Total (g {a'}) f' F
    postulate instance i2 : Indexed B g f' F a
    testTotal' : F (g _) (f _)
    testTotal' = fooT {n = b}
    testTotal'2 : F (f' _) (g _)
    testTotal'2 = fooT {n = b'}
    testTotal'2I : F (f' b') (g _)
    testTotal'2I = fooI {m = a'} -- use fooI when instance given by Total
    testTotal'2I' : F (f' b') (g b')
    testTotal'2I' = fooI' {N = B}
    testTotal'3 : F (f' b) (g b)
    testTotal'3 = fooI {m = a} -- or by Indexed
    testTotal'3' : F (f' b) (g b)
    testTotal'3' = fooI' {N = B}

  testTotalLhs : ∀ {a} {b : B a} → _
  testTotalLhs {a} {b} = fooT {s = f'} {S = F'} {n = b}

  testIndexed : ∀ {a} {b : B a} → F (g b) (f b)
  testIndexed {a} {b} = fooI {S = λ {x} → F {x}} -- use fooI when instance given by IndexedTotal
{-
Have: {M : Set} {N : M → Set} {s t : {m : M} → N m → N m}
      {S : {m : M} → N m → N m → Set}
      {{_ : Indexed {M} N s t S {{∅}} {{∅}}}} {m : M} {n : N m} →
      S {m} (t {m} n) (s {m} n)

Have: {N : Set} {s t : N → N} {S : N → N → Set}
      {{_ : Total {N} s t S {{∅}} {{∅}}}} {n : N} →
      S (t n) (s n)
-}

  testIndexed2 : ∀ {a} {b : B a} → F (g (g' b)) (f (g' b))
  testIndexed2 = fooT

  testIndexed3 : ∀ {a} {b : B a} → F (f (g' b)) (f (g' b))
  testIndexed3 = fooT

  testTotal : ∀ {a} {b : B a} → F (g b) (f b)
  testTotal = fooT

module Indexed≡Total1Prop+Data where

  open import Oscar.Data.Proposequality

  data [_/_/_]≡_ {M : Set} (N : M → Set) (s : ∀ {m} → N m → N m) (S : ∀ {m} → N m → Set) (F : ∀ {m} (n : N m) → Set) : Set where
    instance ∅ : [ N / s / S ]≡ F

  record Indexed {M : Set} (N : M → Set) (s : ∀ {m} → N m → N m) (S : ∀ {m} → N m → Set) ⦃ _ : [ N / s / S ]≡ λ {m} (n : N m) → S (s n) ⦄ : Set where
    field fooI : ∀ {m} {n : N m} → S (s n)

  open Indexed ⦃ … ⦄

  record Total {N : Set} (s : N → N) (S : N → Set) : Set where
    field fooT : ∀ n → S (s n)

  open Total ⦃ … ⦄

  postulate
    A : Set
    B : A → Set
    f : ∀ {x} → B x → B x
    F : ∀ {x} → B x → Set

    instance iIndexed : Indexed B f F ⦃ ∅ ⦄
    instance iTotal : ∀ {x} → Total (f {x}) (F {x})

  testIndexed : ∀ {a} {b : B a} → F (f b)
  testIndexed = fooI ⦃ ∅ ⦄

  testTotal : ∀ {a} (b : B a) → F (f b)
  testTotal = fooT {S = F}

module Indexed≡Total1Prop+Data2 where

  open import Oscar.Data.Proposequality

  data [_/_] {M : Set} (N : M → Set) (s : ∀ {m} → N m → N m) : Set where
    instance ∅ : [ N / s ]

  record Indexed {M : Set} (N : M → Set) (s : ∀ {m} → N m → N m) (S : ∀ {m} → N m → Set) ⦃ _ : [ N / s ] ⦄ : Set where
    field fooI : ∀ {m} {n : N m} → S (s n)

  open Indexed ⦃ … ⦄

  record Total {N : Set} (s : N → N) (S : N → Set) : Set where
    field fooT : ∀ n → S (s n)

  open Total ⦃ … ⦄

  postulate
    A : Set
    B : A → Set
    f : ∀ {x} → B x → B x
    F : ∀ {x} → B x → Set

    instance iIndexed : Indexed B f F ⦃ ∅ ⦄
    instance iTotal : ∀ {x} → Total (f {x}) (F {x})

  testIndexed : ∀ {a} {b : B a} → F (f b)
  testIndexed = fooI ⦃ ∅ ⦄

  testTotal : ∀ {a} (b : B a) → F (f b)
  testTotal = fooT {S = F}
