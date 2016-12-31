{- https://lists.chalmers.se/pipermail/agda/2013/006033.html http://code.haskell.org/~Saizan/unification/ 18-Nov-2013 Andrea Vezzosi -}
module Unify where

open import Data.Fin using (Fin; suc; zero)
open import Data.Nat hiding (_≤_)
open import Relation.Binary.PropositionalEquality
open import Function
open import Relation.Nullary
open import Data.Product
open import Data.Empty

data Term : ℕ -> Set where
  i : ∀ {n} -> (x : Fin n) -> Term n
  leaf : ∀ {n} -> Term n
  _fork_ : ∀ {n} -> (s t : Term n) -> Term n

_~>_ : (m n : ℕ) -> Set
m ~> n = Fin m -> Term n

▹ : ∀ {m n} -> (r : Fin m -> Fin n) -> Fin m -> Term n
▹ r = i ∘ r

_◃ : ∀ {m n} -> (f : m ~> n) -> Term m -> Term n
(f ◃ ) (i x) = f x
(f ◃ ) leaf = leaf
(f ◃ ) (s fork t) = (f ◃) s fork (f ◃) t

_◃_ : ∀ {m n} -> (f : m ~> n) -> Term m -> Term n
_◃_ = _◃

_≐_ : {m n : ℕ} -> (Fin m -> Term n) -> (Fin m -> Term n) -> Set
f ≐ g = ∀ x -> f x ≡ g x

◃ext : ∀ {m n} {f g : Fin m -> Term n} -> f ≐ g -> ∀ t -> f ◃ t ≡ g ◃ t
◃ext p (i x) = p x
◃ext p leaf = refl
◃ext p (s fork t) = cong₂ _fork_ (◃ext p s) (◃ext p t)

_◇_ : ∀ {l m n : ℕ } -> (f : Fin m -> Term n) (g : Fin l -> Term m) -> Fin l -> Term n
f ◇ g = (f ◃) ∘ g

≐-cong : ∀ {m n o} {f : m ~> n} {g} (h : _ ~> o) -> f ≐ g -> (h ◇ f) ≐ (h ◇ g)
≐-cong h f≐g t = cong (h ◃) (f≐g t)

≐-sym : ∀ {m n} {f : m ~> n} {g} -> f ≐ g -> g ≐ f
≐-sym f≐g = sym ∘ f≐g

module Sub where
  fact1 : ∀ {n} -> (t : Term n) -> i ◃ t ≡ t
  fact1 (i x) = refl
  fact1 leaf = refl
  fact1 (s fork t) = cong₂ _fork_ (fact1 s) (fact1 t)

  fact2 : ∀ {l m n} -> (f : Fin m -> Term n) (g : _) (t : Term l)
    -> (f ◇ g) ◃ t ≡ f ◃ (g ◃ t)
  fact2 f g (i x) = refl
  fact2 f g leaf = refl
  fact2 f g (s fork t) = cong₂ _fork_ (fact2 f g s) (fact2 f g t)

  fact3 : ∀ {l m n} (f : Fin m -> Term n) (r : Fin l -> Fin m) -> (f ◇ (▹ r)) ≡ (f ∘ r)
  fact3 f r = refl -- ext (λ _ -> refl)

◃ext' : ∀ {m n o} {f : Fin m -> Term n}{g : Fin m -> Term o}{h} -> f ≐ (h ◇ g) -> ∀ t -> f ◃ t ≡ h ◃ (g ◃ t)
◃ext' p t = trans (◃ext p t) (Sub.fact2 _ _ t)
s : ℕ -> ℕ
s = suc

thin : ∀ {n} -> (x : Fin (s n)) (y : Fin n) -> Fin (s n)
thin zero y = suc y
thin (suc x) zero = zero
thin (suc x) (suc y) = suc (thin x y)

p : ∀ {n} -> Fin (suc (suc n)) -> Fin (suc n)
p (suc x) = x
p zero = zero

module Thin where
  fact1 : ∀ {n} x y z -> thin {n} x y ≡ thin x z -> y ≡ z
  fact1 zero y .y refl = refl
  fact1 (suc x) zero zero r = refl
  fact1 (suc x) zero (suc z) ()
  fact1 (suc x) (suc y) zero ()
  fact1 (suc x) (suc y) (suc z) r = cong suc (fact1 x y z (cong p r))

  fact2 : ∀ {n} x y -> ¬ thin {n} x y ≡ x
  fact2 zero y ()
  fact2 (suc x) zero ()
  fact2 (suc x) (suc y) r = fact2 x y (cong p r)

  fact3 : ∀{n} x y -> ¬ x ≡ y -> ∃ λ y' -> thin {n} x y' ≡ y
  fact3 zero zero ne = ⊥-elim (ne refl)
  fact3 zero (suc y) _ = y , refl
  fact3 {zero} (suc ()) _ _
  fact3 {suc n} (suc x) zero ne = zero , refl
  fact3 {suc n} (suc x) (suc y) ne with y | fact3 x y (ne ∘ cong suc)
  ... | .(thin x y') | y' , refl = suc y' , refl

open import Data.Maybe
open import Category.Functor
open import Category.Monad
import Level
open RawMonad (Data.Maybe.monad {Level.zero})

thick : ∀ {n} -> (x y : Fin (suc n)) -> Maybe (Fin n)
thick zero zero = nothing
thick zero (suc y) = just y
thick {zero} (suc ()) _
thick {suc _} (suc x) zero = just zero
thick {suc _} (suc x) (suc y) = suc <$> (thick x y)

open import Data.Sum

_≡Fin_ : ∀ {n} -> (x y : Fin n) -> Dec (x ≡ y)
zero ≡Fin zero = yes refl
zero ≡Fin suc y = no λ ()
suc x ≡Fin zero = no λ ()
suc {suc _} x ≡Fin suc y with x ≡Fin y
...              | yes r = yes (cong suc r)
...              | no r = no λ e -> r (cong p e)
suc {zero} () ≡Fin _

module Thick where
  half1 : ∀ {n} (x : Fin (suc n)) -> thick x x ≡ nothing
  half1 zero = refl
  half1 {suc _} (suc x) = cong (_<$>_ suc) (half1 x)
  half1 {zero} (suc ())

  half2 : ∀ {n} (x : Fin (suc n)) y -> ∀ y' -> thin x y' ≡ y -> thick x y ≡ just y'
  half2 zero zero y' ()
  half2 zero (suc y) .y refl = refl
  half2 {suc n} (suc x) zero zero refl = refl
  half2 {suc _} (suc _) zero (suc _) ()
  half2 {suc n} (suc x) (suc y) zero ()
  half2 {suc n} (suc x) (suc .(thin x y')) (suc y') refl with thick x (thin x y') | half2 x (thin x y') y' refl
  ...                                                       | .(just y')          | refl = refl
  half2 {zero} (suc ()) _ _ _

  fact1 : ∀ {n} (x : Fin (suc n)) y r
    -> thick x y ≡ r
    -> x ≡ y × r ≡ nothing ⊎ ∃ λ y' -> thin x y' ≡ y × r ≡ just y'
  fact1 x y .(thick x y) refl with x ≡Fin y
  fact1 x .x ._ refl | yes refl = inj₁ (refl , half1 x)
  ... | no el with Thin.fact3 x y el
  ...            | y' , thinxy'=y = inj₂ (y' , ( thinxy'=y , half2 x y y' thinxy'=y ))


check : ∀{n} (x : Fin (suc n)) (t : Term (suc n)) -> Maybe (Term n)
check x (i y) = i <$> thick x y
check x leaf = just leaf
check x (s fork t) = _fork_ <$> check x s ⊛ check x t

_for_ : ∀ {n} (t' : Term n) (x : Fin (suc n)) -> Fin (suc n) -> Term n
(t' for x) y = maybe′ i t' (thick x y)

data AList : ℕ -> ℕ -> Set where
  anil : ∀ {n} -> AList n n
  _asnoc_/_ : ∀ {m n} (σ : AList m n) (t' : Term m) (x : Fin (suc m))
               -> AList (suc m) n

sub : ∀ {m n} (σ : AList m n) -> Fin m -> Term n
sub anil = i
sub (σ asnoc t' / x) = sub σ ◇ (t' for x)

_++_ : ∀ {l m n} (ρ : AList m n) (σ : AList l m) -> AList l n
ρ ++ anil = ρ
ρ ++ (σ asnoc t' / x) = (ρ ++ σ) asnoc t' / x

++-assoc : ∀ {l m n o} (ρ : AList l m) (σ : AList n _) (τ : AList o _) -> ρ ++ (σ ++ τ) ≡ (ρ ++ σ) ++ τ
++-assoc ρ σ anil = refl
++-assoc ρ σ (τ asnoc t / x) = cong (λ s -> s asnoc t / x) (++-assoc ρ σ τ)

module SubList where
  anil-id-l : ∀ {m n} (σ : AList m n) -> anil ++ σ ≡ σ
  anil-id-l anil = refl
  anil-id-l (σ asnoc t' / x) = cong (λ σ -> σ asnoc t' / x) (anil-id-l σ)

  fact1 : ∀ {l m n} (ρ : AList m n) (σ : AList l m) -> sub (ρ ++ σ) ≐ (sub ρ ◇ sub σ)
  fact1 ρ anil v = refl
  fact1 {suc l} {m} {n} r (s asnoc t' / x) v = trans hyp-on-terms ◃-assoc
    where
      t = (t' for x) v
      hyp-on-terms = ◃ext (fact1 r s) t
      ◃-assoc = Sub.fact2 (sub r) (sub s) t


_∃asnoc_/_ : ∀ {m} (a : ∃ (AList m)) (t' : Term m) (x : Fin (suc m))
  -> ∃ (AList (suc m))
(n , σ) ∃asnoc t' / x = n , σ asnoc t' / x

flexFlex : ∀ {m} (x y : Fin m) -> ∃ (AList m)
flexFlex {suc m} x y with thick x y
...              | just y' = m , anil asnoc i y' / x
...              | nothing = suc m , anil
flexFlex {zero} () _

flexRigid : ∀ {m} (x : Fin m) (t : Term m) -> Maybe (∃(AList m))
flexRigid {suc m} x t with check x t
...                   | just t' = just (m , anil asnoc t' / x)
...                   | nothing = nothing
flexRigid {zero} () _


amgu : ∀ {m} (s t : Term m) (acc : ∃ (AList m)) -> Maybe (∃ (AList m))
amgu leaf leaf acc = just acc
amgu leaf (s' fork t') acc = nothing
amgu (s' fork t') leaf acc = nothing
amgu (s1 fork s2) (t1 fork t2) acc =
                  amgu s2 t2 =<< amgu s1 t1 acc
amgu (i x) (i y) (m , anil) = just (flexFlex x y)
amgu (i x) t     (m , anil) = flexRigid x t
amgu t     (i x) (m , anil) = flexRigid x t
amgu s     t  (n , σ asnoc r / z) =
         (λ σ -> σ ∃asnoc r / z) <$>
           amgu ((r for z) ◃ s) ((r for z) ◃ t) (n , σ)

mgu : ∀ {m} -> (s t : Term m) -> Maybe (∃ (AList m))
mgu {m} s t = amgu s t (m , anil)
