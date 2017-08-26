```agda
{-# OPTIONS -v 1 #-}
{-# OPTIONS --show-implicit #-}

module $RequiredForInstanceResolution where

open import Agda.Primitive

infixr -20 _$_
_$_ : {A : Set} {B : A → Set} → (∀ x → B x) → ∀ x → B x
f $ x = f x

Extension : {𝔒 : Set} (𝔓 : 𝔒 → Set) → 𝔒 → 𝔒 → Set
Extension A x y = A x → A y

it : ∀ {a} {A : Set a} {{x : A}} -> A
it {{x}} = x

postulate
  InnerClass : Set → Set
  I : Set

SurjectivityClass : (I → I → Set) → Set
SurjectivityClass S = InnerClass ∀ x y → S x y

postulate

  R : I → I → Set
  m n : I

  surjectivity : ∀
    {S : I → I → Set}
    ⦃ _ : SurjectivityClass S ⦄
    → S m n

  surjectextensivity : ∀
    {P : I → Set}
    ⦃ _ : SurjectivityClass (Extension P) ⦄
    → Extension P m n

postulate
  Prop : (I → I → Set) → I → Set
  instance I-Surjext-PropR : SurjectivityClass (Extension (Prop R))

P = Prop R

postulate
  p : P m

works-1a : P n
works-1a = surjectextensivity p

works-2a : P n
works-2a = surjectivity $ p

works-3a : P n
works-3a = surjectivity p

mutual

  ?S3a : I → I → Set
  ?S3a = _

  ?iSC3a : InnerClass ∀ x y → ?S3a x y
  ?iSC3a = it

  solve3a : P n
  solve3a = surjectivity {?S3a} {{?iSC3a}} p

postulate
  Foo : I → I → Set
  instance I-Surj-Foo : SurjectivityClass Foo
  instance I-Surjext-PropRFoo : SurjectivityClass (Extension (Prop Foo))
  instance I-Surjext-PropR' : SurjectivityClass (λ x y → Prop R x → Prop R x)

works-1b : P n
works-1b = surjectextensivity p

module 2b where

  test : P n
  test = _$_ {A = _} {B = _} (surjectivity {S = _} {{it}}) p

  mutual

    -- first argument to surjectivity (S, hidden)
    s?S : I → I → Set
    s?S = _

    it?a : Level
    it?a = _

    it?A : Set it?a
    it?A = _

    it?x : it?A
    it?x = it

    -- second argument to surjectivity (instance)
    s?iSC : InnerClass ∀ x y → s?S x y
    s?iSC = it {a = it?a} {A = it?A} {{x = it?x}}

    -- first argument to _$_ (A, hidden)
    $?A : Set
    $?A = _

    -- second argument to _$_ (B, hidden)
    $?B : $?A → Set
    $?B = _

    -- third argument to _$_ (first visible)
    $?f : ∀ x → $?B x
    $?f = surjectivity {S = s?S} {{s?iSC}}

    -- fourth argument to _$_ (second visible)
    $?x : $?A
    $?x = p

    -- definition of _$_
    app : P n
    app = $?f $?x

  solve : P n
  solve = _$_ {A = $?A} {B = $?B} (surjectivity {S = s?S} {{s?iSC}}) p

module 3b where

  test : P n
  test = surjectivity p

  mutual

    ?S : I → I → Set
    ?S = _

    ?iSC : InnerClass ∀ x y → ?S x y
    ?iSC = it

    app : ?S m n → P n
    app s = s p

  solve : ?S m n → P n
  solve s = surjectivity {S = ?S} {{?iSC}} p
```
