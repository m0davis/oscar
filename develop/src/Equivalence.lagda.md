
```agda
module Equivalence where
```

# Remark the first.

In the below, I attempt but fail to prove `StoTtoS`. This surprises me because I am able to give a kind of infinitary proof by successively case-splitting on two of the arguments. I want to know if I am on a fool's errand (h/t Conor McBride) or if there is indeed a finitary proof (in Agda).

# Remark the second.

I did find a way of proving it. There's a lesson in that somewhere for me.

### boilerplate

```agda
open import Agda.Builtin.Equality

cong : ∀ {a b} {A : Set a} {B : Set b} (f : A → B) {x y} → x ≡ y → f x ≡ f y
cong f refl = refl

transport : ∀ {a b} {A : Set a} (B : A → Set b) {x y} → x ≡ y → B x → B y
transport B refl bx = bx

data Nat : Set where
  zero : Nat
  suc  : (n : Nat) → Nat

_+_ : Nat → Nat → Nat
zero  + m = m
suc n + m = suc (n + m)

right-zero-identity : ∀ n → n ≡ n + zero
right-zero-identity zero = refl
right-zero-identity (suc n) = cong suc (right-zero-identity n)
```

## main code

```agda
postulate P : Nat → Set

data S (N : Nat) : Set where
  cS : (pN : P N) → S N

data T (N : Nat) : Set where
  cT : (x : Nat) (N≡x+0 : N ≡ x + zero) (px : P x) → T N

toT : ∀ N → S N → T N
toT N (cS x) = cT N (right-zero-identity N) x

toS : ∀ N → T N → S N
toS .(x + zero) (cT x refl px) = cS (transport P (right-zero-identity x) px)
```

### the problem

```
StoTtoS : ∀ N (x x' : S N) (t : T N) (toTx≡t : toT N x ≡ t) (toSt≡x' : toS N t ≡ x') → x' ≡ x
StoTtoS _ (cS _) (cS _) (cT zero refl _)                      refl   refl = refl
StoTtoS _ (cS _) (cS _) (cT (suc zero) refl _)                refl   refl = refl
StoTtoS _ (cS _) (cS _) (cT (suc (suc zero)) refl _)          refl   refl = refl
StoTtoS _ (cS _) (cS _) (cT (suc (suc (suc zero))) refl _)    toTx≡t refl = {!!}
StoTtoS _ (cS _) (cS _) (cT (suc (suc (suc (suc x)))) refl _) toTx≡t refl = {!!}
```

## the solution

```
sym : ∀ {a} {A : Set a} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : ∀ {a} {A : Set a} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl eq = eq
```

```
inj-cT-x : (N : Nat) (x x' : Nat) (N≡x+0 : N ≡ x + zero) (N≡x'+0 : N ≡ x' + zero) (px : P x) (px' : P x')
          → (cT≡cT' : cT x N≡x+0 px ≡ cT x' N≡x'+0 px')
          → x ≡ x'
inj-cT-x .(x + zero) x .x refl .refl px .px refl = refl

inj-cT-px : (N : Nat) (x x' : Nat) (N≡x+0 : N ≡ x + zero) (N≡x'+0 : N ≡ x' + zero) (px : P x) (px' : P x')
          → (cT≡cT' : cT x N≡x+0 px ≡ cT x' N≡x'+0 px')
          → px' ≡ transport P (inj-cT-x _ _ _ _ _ _ _ cT≡cT') px
inj-cT-px .(x + zero) x .x refl .refl px .px refl = refl
```

```agda
transportation-eq :
  ∀ {a b} {A : Set a} (B : A → Set b) {x y} → (eq eq' : x ≡ y) → (bx : B x)
  → transport B eq bx ≡ transport B eq' bx
transportation-eq B refl refl bx = refl
```

```agda
inj-cS : ∀ N (pN pN' : P N)
       → cS pN ≡ cS pN'
       → pN ≡ pN'
inj-cS N pN .pN refl = refl

prv : ∀ N (x x' : S N) (t : T N) (toTx≡t : toT N x ≡ t) (toSt≡x' : toS N t ≡ x') → x' ≡ x
prv .(x + zero) (cS pN) (cS pN') (cT x refl px) toTx≡t toSt≡x' =
  let cT= : pN ≡
              transport P
              (inj-cT-x (x + zero) x (x + zero) refl
               (right-zero-identity (x + zero)) px pN (sym toTx≡t))
              px
      cT= = inj-cT-px _ _ _ _ _ _ _ (sym toTx≡t)
      cS= : pN' ≡ transport P (right-zero-identity x) px
      cS= = inj-cS _ _ _ (sym toSt≡x')
  in cong cS (trans cS= (trans (transportation-eq P (right-zero-identity x) (inj-cT-x (x + zero) x (x + zero) refl
       (right-zero-identity (x + zero)) px pN (sym toTx≡t)) px) (sym cT=)))
```
