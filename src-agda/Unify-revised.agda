{- https://lists.chalmers.se/pipermail/agda/2013/006033.html http://code.haskell.org/~Saizan/unification/ 18-Nov-2013 Andrea Vezzosi -}
module Unify-revised where

-- some equivalences needed to adapt Tactic.Nat to the standard library
module EquivalenceOf≤ where
  open import Agda.Builtin.Equality
  open import Agda.Builtin.Nat

  open import Data.Nat using (less-than-or-equal) renaming (_≤_ to _≤s_)
  open import Data.Nat.Properties using (≤⇒≤″; ≤″⇒≤)
  open import Prelude using (diff; id) renaming (_≤_ to _≤p_)

  open import Tactic.Nat.Generic (quote _≤p_) (quote id) (quote id) using (by)

  ≤p→≤s : ∀ {a b} → a ≤p b → a ≤s b
  ≤p→≤s (diff k b₊₁≡k₊₁+a) = ≤″⇒≤ (less-than-or-equal {k = k} (by b₊₁≡k₊₁+a))

  ≤s→≤p : ∀ {a b} → a ≤s b → a ≤p b
  ≤s→≤p a≤sb with ≤⇒≤″ a≤sb
  ≤s→≤p _ | less-than-or-equal {k = k} a+k≡b = diff k (by a+k≡b)

module _ where
  open EquivalenceOf≤
  open import Data.Nat
  open import Tactic.Nat.Generic (quote _≤_) (quote ≤s→≤p) (quote ≤p→≤s) public

open import Data.Fin using (Fin; suc; zero)
open import Data.Nat hiding (_≤_)
--open import Relation.Binary.PropositionalEquality
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Function
open import Relation.Nullary
--open import Data.Product
open import Data.Product renaming (map to _***_)
open import Data.Empty

data Term (n : ℕ) : Set where
  i : (x : Fin n) -> Term n
  leaf : Term n
  _fork_ : (s t : Term n) -> Term n

{-
data Term : ℕ -> Set where
  i : ∀ ..{n} -> (x : Fin n) -> Term n
  leaf : ∀ ..{n} -> Term n
  _fork_ : ∀ ..{n} -> (s t : Term n) -> Term n
-}
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

alist≥ : ∀ m n → AList m n → m Data.Nat.≥ n
alist≥ m .m anil = {!!}
alist≥ .(suc _) n (x asnoc t' / x₁) with alist≥ _ _ x
… | r = {!!}

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






{-
open import Data.Fin using (Fin; suc; zero)
open import Data.Nat hiding (_≤_)
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Function
open import Relation.Nullary
open import Data.Product renaming (map to _***_)
open import Data.Empty
-}
open import Data.Maybe using (maybe; maybe′; nothing; just; monad; Maybe)
open import Data.Sum
--open import Unify
open import Data.List renaming (_++_ to _++L_)
open ≡-Reasoning
open import Category.Functor
open import Category.Monad
import Level as L
--open RawMonad (Data.Maybe.monad {L.zero})

record Σ₁ (A : Set1) (F : A -> Set) : Set1 where
  field
    π₁ : A
    π₂ : F π₁

_,,_ : ∀ {A F} (x : A) -> F x -> Σ₁ A F
x ,, b = record{ π₁ = x; π₂ = b }

open Σ₁

Property⋆ : (m : ℕ) -> Set1
Property⋆ m = ∀ {n} -> (Fin m -> Term n) -> Set

Extensional : {m : ℕ} -> Property⋆ m -> Set
Extensional P = ∀ {m f g} -> f ≐ g -> P {m} f -> P g

Property : (m : ℕ) -> Set1
Property m = Σ₁ (Property⋆ m) Extensional

prop-id : ∀ {m n} {f : _ ~> n} {P : Property m} -> π₁ P f -> π₁ P (i ◇ f)
prop-id {_} {_} {f} {P'} Pf = π₂ P' (λ x → sym (Sub.fact1 (f x))) Pf

Unifies⋆ : ∀ {m} (s t : Term m) -> Property⋆ m
Unifies⋆ s t f = f ◃ s ≡ f ◃ t

Unifies : ∀ {m} (s t : Term m) -> Property m
Unifies s t = (λ {_} -> Unifies⋆ s t) ,, λ {_} {f} {g} f≐g f◃s=f◃t ->
  begin
    g ◃ s
  ≡⟨ sym (◃ext f≐g s) ⟩
    f ◃ s
  ≡⟨ f◃s=f◃t ⟩
    f ◃ t
  ≡⟨ ◃ext f≐g t ⟩
    g ◃ t
  ∎


_∧⋆_ : ∀{m} -> (P Q : Property⋆ m) -> Property⋆ m
P ∧⋆ Q = (λ f -> P f × Q f)

_∧_ : ∀{m} -> (P Q : Property m) -> Property m
P ∧ Q = (λ {_} f -> π₁ P f × π₁ Q f) ,, λ {_} {_} {_} f≐g Pf×Qf -> π₂ P f≐g (proj₁ Pf×Qf) , π₂ Q f≐g (proj₂ Pf×Qf)


_⇔⋆_ : ∀{m} -> (P Q : Property⋆ m) -> Set
P ⇔⋆ Q = ∀ {n} f -> (P {n} f -> Q f) × (Q f -> P f)

_⇔_ : ∀{m} -> (P Q : Property m) -> Set
P ⇔ Q = ∀ {n} f -> (π₁ P {n} f -> π₁ Q f) × (π₁ Q f -> π₁ P f)

switch⋆ : ∀ {m} (P Q : Property⋆ m) -> P ⇔⋆ Q -> Q ⇔⋆ P
switch⋆ _ _ P⇔Q f = proj₂ (P⇔Q f) , proj₁ (P⇔Q f)

switch : ∀ {m} (P Q : Property m) -> P ⇔ Q -> Q ⇔ P
switch _ _ P⇔Q f = proj₂ (P⇔Q f) , proj₁ (P⇔Q f)

Nothing⋆ : ∀{m} -> (P : Property⋆ m) -> Set
Nothing⋆ P = ∀{n} f -> P {n} f -> ⊥

Nothing : ∀{m} -> (P : Property m) -> Set
Nothing P = ∀{n} f -> π₁ P {n} f -> ⊥

_[-◇⋆_] : ∀{m n} (P : Property⋆ m) (f : Fin m -> Term n) -> Property⋆ n
(P [-◇⋆ f ]) g = P (g ◇ f)

_[-◇_] : ∀{m n} (P : Property m) (f : Fin m -> Term n) -> Property n
P [-◇ f ] = (λ {_} g -> π₁ P (g ◇ f)) ,, λ {_} {f'} {g'} f'≐g' Pf'◇f -> π₂ P (◃ext f'≐g' ∘ f)  Pf'◇f

module Properties where
  fact1 : ∀ {m} {s t : Term m} -> (Unifies s t) ⇔ (Unifies t s)
  fact1 _ = sym , sym


  fact1'⋆ : ∀ {m} {s1 s2 t1 t2 : Term m}
         -> Unifies⋆ (s1 fork s2) (t1 fork t2) ⇔⋆ (Unifies⋆ s1 t1 ∧⋆ Unifies⋆ s2 t2)
  fact1'⋆ f = deconstr _ _ _ _ , uncurry (cong₂ _fork_)
    where deconstr : ∀ {m} (s1 s2 t1 t2 : Term m)
                   -> (s1 fork s2) ≡ (t1 fork t2)
                   -> (s1 ≡ t1) × (s2 ≡ t2)
          deconstr s1 s2 .s1 .s2 refl = refl , refl

  fact1' : ∀ {m} {s1 s2 t1 t2 : Term m}
         -> Unifies (s1 fork s2) (t1 fork t2) ⇔ (Unifies s1 t1 ∧ Unifies s2 t2)
  fact1' f = deconstr _ _ _ _ , uncurry (cong₂ _fork_)
    where deconstr : ∀ {m} (s1 s2 t1 t2 : Term m)
                   -> (s1 fork s2) ≡ (t1 fork t2)
                   -> (s1 ≡ t1) × (s2 ≡ t2)
          deconstr s1 s2 .s1 .s2 refl = refl , refl


  fact2⋆ : ∀ {m} (P Q : Property⋆ m) -> P ⇔⋆ Q -> Nothing⋆ P -> Nothing⋆ Q
  fact2⋆ P Q iff notp f q with iff f
  ...                        | (p2q , q2p) = notp f (q2p q)

  fact2 : ∀ {m} (P Q : Property m) -> P ⇔ Q -> Nothing P -> Nothing Q
  fact2 P Q iff notp f q with iff f
  ...                       | (p2q , q2p) = notp f (q2p q)


  fact3 : ∀ {m} {P : Property m} -> P ⇔ (P [-◇ i ])
  fact3 f = id , id

  fact4 : ∀{m n} {P : Property m} (f : _ -> Term n)
          -> Nothing P -> Nothing (P [-◇ f ])
  fact4 f nop g = nop (g ◇ f)

  fact5⋆ : ∀{m n} (P Q : Property⋆ _) (f : m ~> n) -> P ⇔⋆ Q -> (P [-◇⋆ f ]) ⇔⋆ (Q [-◇⋆ f ])
  fact5⋆ _ _ f P⇔Q f' = P⇔Q (f' ◇ f)

  fact5 : ∀{m n} (P Q : Property _) (f : m ~> n) -> P ⇔ Q -> (P [-◇ f ]) ⇔ (Q [-◇ f ])
  fact5 _ _ f P⇔Q f' = P⇔Q (f' ◇ f)

  fact6 : ∀{m n} P {f g : m ~> n} -> f ≐ g -> (P [-◇ f ]) ⇔ (P [-◇ g ])
  fact6 P f≐g h = π₂ P (≐-cong h f≐g) , π₂ P (≐-sym (≐-cong h f≐g))
{-
  fact5 : ∀ {l m n} {f : Fin n -> Term l} {g : Fin m -> Term n}
            {P : Property _ }
        -> (P [-◇ g ]) [-◇ f ] ⇔ P [-◇ (f ◇ g) ]
  fact5 h = {!!} , {!!}
-}

_≤_ : ∀ {m n n'} (f : Fin m -> Term n) (g : Fin m -> Term n') -> Set
f ≤ g = ∃ λ f' -> f ≐ (f' ◇ g)

module Order where

  reflex : ∀ {m n} {f : Fin m -> Term n} -> f ≤ f
  reflex = i  , λ _ -> sym (Sub.fact1 _)

  transitivity : ∀ {l m n o} {f : Fin l -> Term m}{g : _ -> Term n}
                             {h : _ -> Term o}
                   -> f ≤ g -> g ≤ h -> f ≤ h
  transitivity {l} {_} {_} {_} {f} {g} {h} (fg , pfg) (gh , pgh) =
                   fg ◇ gh , proof
    where
      proof : (x : Fin l) → f x ≡ (λ x' → fg ◃ (gh x')) ◃ (h x)
      proof x = trans z (sym (Sub.fact2 fg gh (h x)))
        where z = trans (pfg x) (cong (fg ◃) (pgh x))

  i-max : ∀ {m n} (f : Fin m -> Term n) -> f ≤ i
  i-max f = f , λ _ -> refl

  dist : ∀{l m n o}{f : Fin l -> Term m}{g : _ -> Term n}(h : Fin o -> _) -> f ≤ g -> (f ◇ h) ≤ (g ◇ h)
  dist h (fg , pfg) = fg  , λ x -> trans (◃ext pfg (h x)) (Sub.fact2 _ _ (h x))

Max⋆ : ∀ {m} (P : Property⋆ m) -> Property⋆ m
Max⋆ P f = P f × (∀ {n} f' -> P {n} f' -> f' ≤ f)

Max : ∀ {m} (P : Property m) -> Property m
Max P' = (λ {_} → Max⋆ P) ,, λ {_} {_} {_} -> lemma1
  where
    open Σ₁ P' renaming (π₁ to P; π₂ to Peq)
    lemma1 : {m : ℕ} {f : Fin _ → Term m} {g : Fin _ → Term m} →
             f ≐ g →
             P f × ({n : ℕ} (f' : Fin _ → Term n) → P f' → f' ≤ f) →
             P g × ({n : ℕ} (f' : Fin _ → Term n) → P f' → f' ≤ g)
    lemma1 {_} {f} {g} f≐g (Pf , MaxPf) = Peq f≐g Pf , λ {_} -> lemma2
      where
        lemma2 : ∀ {n} f' → P {n} f' → ∃ λ f0 → f' ≐ (f0 ◇ g)
        lemma2 f' Pf' = f0 , λ x -> trans (f'≐f0◇f x) (cong (f0 ◃) (f≐g x))
              where
                f0 = proj₁ (MaxPf f' Pf')
                f'≐f0◇f = proj₂ (MaxPf f' Pf')


module Max where
  fact : ∀{m}(P Q : Property m) -> P ⇔ Q -> Max P ⇔ Max Q
  fact {m} P Q a f =
   (λ maxp → pq (proj₁ maxp) , λ f' → proj₂ maxp f' ∘ qp)
    , λ maxq → qp (proj₁ maxq) , λ f'  → proj₂ maxq f' ∘ pq
    where
      pq : {n : ℕ} {f0 : Fin m → Term n} → (π₁ P f0 → π₁ Q f0)
      pq {_} {f} =  proj₁ (a f)
      qp : {n : ℕ} {f0 : Fin m → Term n} → (π₁ Q f0 → π₁ P f0)
      qp {_} {f} = proj₂ (a f)

DClosed : ∀{m} (P : Property m) -> Set
DClosed P = ∀ {n} f {o} g -> f ≤ g -> π₁ P {o} g -> π₁ P {n} f


module DClosed where

  fact1 : ∀ {m} s t -> DClosed {m} (Unifies s t)
  fact1 s t f g (f≤g , p) gs=gt =
         begin
         f ◃ s
         ≡⟨ ◃ext' p s ⟩
         f≤g ◃ (g ◃ s)
         ≡⟨ cong (f≤g ◃) gs=gt ⟩
         f≤g ◃ (g ◃ t)
         ≡⟨ sym (◃ext' p t) ⟩
         f ◃ t
         ∎

optimist : ∀ {l m n o} (a : Fin _ -> Term n) (p : Fin _ -> Term o)
                 (q : Fin _ -> Term l) (P Q : Property m)
           -> DClosed P -> π₁ (Max (P [-◇ a ])) p
           -> π₁ (Max (Q [-◇ (p ◇ a) ])) q
           -> π₁ (Max ((P ∧ Q) [-◇ a ])) (q ◇ p)
optimist a p q P' Q' DCP (Ppa , pMax) (Qqpa , qMax) =
     (Peq (sym ∘ (Sub.fact2 _ _) ∘ a) (DCP (q ◇ (p ◇ a)) (p ◇ a) (q , λ _ -> refl) Ppa)
      , Qeq (sym ∘ (Sub.fact2 _ _) ∘ a) Qqpa )
     , λ {_} -> aux
  where
    open Σ₁ P' renaming (π₁ to P; π₂ to Peq)
    open Σ₁ Q' renaming (π₁ to Q; π₂ to Qeq)
    aux : ∀ {n} (f : _ -> Term n) -> P (f ◇ a) × Q (f ◇ a) -> f ≤ (q ◇ p)
    aux f (Pfa , Qfa) = h ,
                        λ x -> trans (f≐g◇p x) (◃ext' g≐h◇q (p x))
      where
        one = pMax f Pfa
        g = proj₁ one
        f≐g◇p = proj₂ one
        Qgpa : Q (g ◇ (p ◇ a))
        Qgpa = Qeq (λ x -> ◃ext' f≐g◇p (a x)) Qfa
        g≤q = qMax g Qgpa
        h = proj₁ g≤q
        g≐h◇q = proj₂ g≤q


module failure-propagation where

  first⋆ : ∀ {m n} (a : _ ~> n) (P Q : Property⋆ m) ->
         Nothing⋆ (P [-◇⋆ a ]) -> Nothing⋆ ((P ∧⋆ Q) [-◇⋆ a ])
  first⋆ a P' Q' noP-a f (Pfa , Qfa) = noP-a f Pfa

  first : ∀ {m n} (a : _ ~> n) (P Q : Property m) ->
         Nothing (P [-◇ a ]) -> Nothing ((P ∧ Q) [-◇ a ])
  first a P' Q' noP-a f (Pfa , Qfa) = noP-a f Pfa
{-
  second⋆ : ∀ {m n o} (a : _ ~> n) (p : _ ~> o)(P Q : Property⋆ m) ->
             (Max⋆ (P [-◇⋆ a ])) p -> Nothing⋆ (Q [-◇⋆ (p ◇ a)])
             -> Nothing⋆ ((P ∧⋆ Q) [-◇⋆ a ])
  second⋆ a p P' Q' (Ppa , pMax) noQ-p◇a f (Pfa , Qfa) = noQ-p◇a g Qgpa
       where
         f≤p = pMax f Pfa
         g = proj₁ f≤p
         f≐g◇p = proj₂ f≤p
         Qgpa : Q' (g ◇ (p ◇ a))
         Qgpa = {!!}
  {-
                                                      noQ-p◇a g Qgpa
       where
         f≤p = pMax f Pfa
         g = proj₁ f≤p
         f≐g◇p = proj₂ f≤p
         Qgpa : π₁ Q' (g ◇ (p ◇ a))
         Qgpa = π₂ Q' (◃ext' f≐g◇p ∘ a)  Qfa
  -}
-}
  second⋆ : ∀ {m n o} (a : _ ~> n) (p : _ ~> o)(P : Property⋆ m)(Q : Property m) ->
             (Max⋆ (P [-◇⋆ a ])) p -> Nothing⋆ (π₁ Q [-◇⋆ (p ◇ a)])
             -> Nothing⋆ ((P ∧⋆ π₁ Q) [-◇⋆ a ])
  second⋆ a p P' Q' (Ppa , pMax) noQ-p◇a f (Pfa , Qfa) = noQ-p◇a g Qgpa
       where
         f≤p = pMax f Pfa
         g = proj₁ f≤p
         f≐g◇p = proj₂ f≤p
         Qgpa : π₁ Q' (g ◇ (p ◇ a))
         Qgpa = π₂ Q' (◃ext' f≐g◇p ∘ a)  Qfa

  second : ∀ {m n o} (a : _ ~> n) (p : _ ~> o)(P Q : Property m) ->
             π₁ (Max (P [-◇ a ])) p -> Nothing (Q [-◇ (p ◇ a)])
             -> Nothing ((P ∧ Q) [-◇ a ])
  second a p P' Q' (Ppa , pMax) noQ-p◇a f (Pfa , Qfa) =
                                                      noQ-p◇a g Qgpa
       where
         f≤p = pMax f Pfa
         g = proj₁ f≤p
         f≐g◇p = proj₂ f≤p
         Qgpa : π₁ Q' (g ◇ (p ◇ a))
         Qgpa = π₂ Q' (◃ext' f≐g◇p ∘ a)  Qfa


trivial-problem : ∀ {m n t} {f : m ~> n} -> π₁ (Max ((Unifies t t) [-◇ f ])) i
trivial-problem = refl , λ f' _ → f' , λ _ → refl


var-elim : ∀ {m} (x : Fin (suc m)) (t' : Term _)
              -> π₁ (Max ((Unifies (i x) ((▹ (thin x) ◃) t')))) (t' for x)
var-elim x t' = first , \{_} -> second
  where
    lemma : ∀{m}(x : Fin (suc m)) t → i ≐ ((t for x) ◇ (▹ (thin x)))
    lemma x t x' = sym (cong (maybe i t) (Thick.half2 x _ x' refl))
    first = begin
             (t' for x) ◃ (i x) ≡⟨ cong (maybe i t') (Thick.half1 x) ⟩
             t'                 ≡⟨ sym (Sub.fact1 t') ⟩
             i ◃ t'             ≡⟨ ◃ext' (lemma x t') t' ⟩
             (t' for x) ◃ ((▹ (thin x) ◃) t') ∎

    second : ∀ {n} (f : _ ~> n) → f x ≡ f ◃ ((▹ (thin x) ◃) t') → f ≤ (t' for x)
    second f Unifiesf = (f ∘ thin x) , third
        where
          third : ((x' : Fin _) →  f x' ≡ (f ∘ thin x) ◃ (maybe′ i t' (thick x x')))
          third x' with thick x x' | Thick.fact1 x x' (thick x x') refl
          third .x | .nothing | inj₁ (refl , refl)  =
                                       sym (begin
                                           (f ∘ thin x) ◃ t'  ≡⟨ cong (λ g -> (g ◃) t') (sym (Sub.fact3 f (thin x))) ⟩
                                           (f ◇ (▹ (thin x))) ◃ t' ≡⟨ Sub.fact2 f (▹ (thin x)) t' ⟩
                                           f ◃ ((▹ (thin x) ◃) t') ≡⟨ sym Unifiesf ⟩
                                           f x ∎)
          third x' | .(just y) | inj₂ (y , ( thinxy≡x' , refl))  = sym (cong f thinxy≡x')

var-elim-i : ∀ {m} (x : Fin (suc m)) (t' : Term _)
              -> π₁ (Max ((Unifies (i x) ((▹ (thin x) ◃) t')))) (i ◇ (t' for x))
var-elim-i {m} x t = prop-id {_} {_} {t for x} {Max (Unifies (i x) ((▹ (thin x) ◃) t))} (var-elim {m} x t)

var-elim-i-≡ : ∀ {m} {t'} (x : Fin (suc m)) t1  -> t1 ≡ (i ∘ thin x) ◃ t' -> π₁ (Max (Unifies (i x) t1)) (i ◇ (t' for x))
var-elim-i-≡ {_} {t'} x .((i ∘ thin x) ◃ t') refl = var-elim-i x t'

data Step (n : ℕ) : Set where
  left : Term n -> Step n
  right : Term n -> Step n

fmapS : ∀ {n m} (f : Term n -> Term m) (s : Step n) -> Step m
fmapS f (left x) = left (f x)
fmapS f (right x) = right (f x)

_⊹_ : ∀ {n} (ps : List (Step n)) (t : Term n) -> Term n
[] ⊹ t             = t
(left r ∷ ps) ⊹ t  = (ps ⊹ t) fork r
(right l ∷ ps) ⊹ t = l fork (ps ⊹ t)

_◃S : ∀ {n m} (f : n ~> m) -> List (Step n) -> List (Step m)
_◃S f = Data.List.map (fmapS (f ◃))

map-[] : ∀ {n m} (f : n ~> m) ps -> (f ◃S) ps ≡ [] -> ps ≡ []
map-[] f [] _ = refl
map-[] f (x ∷ xs) ()

module StepM where

  lemma1 : ∀ {n} (x : Step n) xs t -> [ x ] ⊹ ( xs ⊹ t ) ≡ (x ∷ xs) ⊹ t
  lemma1 (left y) xs t = refl
  lemma1 (right y) xs t = refl

  lemma2 : ∀ {n} {r} {t} {xs} (x : Step n) -> xs ⊹ t ≡ r -> ((x ∷ xs) ⊹ t ) ≡ [ x ] ⊹ r
  lemma2 (left y) eq = cong (λ t -> t fork y) eq
  lemma2 (right y) eq = cong (λ t -> y fork t) eq

  fact1 : ∀ {n} ps qs (t : Term n) -> (ps ++L qs) ⊹ t ≡ ps ⊹ (qs ⊹ t)
  fact1 [] qs t = refl
  fact1 (p ∷ ps) qs t = begin (p ∷ (ps ++L qs)) ⊹ t ≡⟨ lemma2 p (fact1 ps qs t) ⟩
                              [ p ] ⊹ (ps ⊹ (qs ⊹ t)) ≡⟨ lemma1 p ps (qs ⊹ t)  ⟩
                              (p ∷ ps) ⊹ (qs ⊹ t) ∎

  fact2 : ∀ {m n} (f : m ~> n) t ps ->
               f ◃ (ps ⊹ t) ≡ (f ◃S) ps ⊹ (f ◃ t)
  fact2 f t [] = refl
  fact2 f t (left y ∷ xs) = cong (λ t -> t fork (f ◃ y)) (fact2 f t xs)
  fact2 f t (right y ∷ xs) = cong (λ t -> (f ◃ y) fork t) (fact2 f t xs)


check-prop : ∀ {m} (x : Fin (suc m)) t ->
           (∃ λ t' -> t ≡ (▹ (thin x) ◃) t' × check x t ≡ just t')
           ⊎ (∃ λ ps -> t ≡ (ps ⊹ i x) × check x t ≡ nothing)
check-prop x (i x') with Thick.fact1 x x' (thick x x') refl
check-prop x (i .x) | inj₁ (refl , e) = inj₂ ([] , refl , cong (_<$>_ i) e)
... | inj₂ (y , thinxy≡x' , thickxx'≡justy')
    = inj₁ (i y
           , cong i (sym (thinxy≡x'))
           , cong (_<$>_ i) thickxx'≡justy' )
check-prop x leaf = inj₁ (leaf , (refl , refl))
check-prop x (s fork t)
 with check-prop x s                     | check-prop x t
... | inj₁ (s' , s≡thinxs' , checkxs≡s') | inj₁ (t' , t≡thinxt' , checkxt≡t')
    = inj₁ (s' fork t' , cong₂ _fork_ s≡thinxs' t≡thinxt'
           , cong₂ (λ a b -> _fork_ <$> a ⊛ b) checkxs≡s' checkxt≡t' )
... | inj₂ (ps , s≡ps+ix , checkxs≡no )  | _
    = inj₂ (left t ∷ ps , cong (λ s -> s fork t) s≡ps+ix
           , cong (λ a -> _fork_ <$> a ⊛ check x t) checkxs≡no )
... | _                                  | inj₂ (ps , s≡ps+ix , checkxs≡no )
    = inj₂ (right s ∷ ps , cong (λ t -> s fork t) s≡ps+ix
           , trans (cong (λ a -> _fork_ <$> check x s ⊛ a) checkxs≡no) (lemma (_fork_ <$> check x s)))
  where
    lemma : ∀ {a b : Set} {y : b} (x : Maybe a) -> maybe (λ _ → y) y x ≡ y
    lemma (just x') = refl
    lemma nothing = refl

fork++ : ∀ {m} {s t : Term m} ps ->
              (ps ⊹ (s fork t) ≡ (ps ++L [ left t ]) ⊹ s)
              × (ps ⊹ (s fork t) ≡ (ps ++L [ right s ]) ⊹ t)
fork++ [] = refl , refl
fork++ (left y' ∷ xs') = (cong (λ a -> a fork y') *** cong (λ a -> a fork y')) (fork++ xs')
fork++ (right y' ∷ xs') = (cong (λ a -> y' fork a) *** cong (λ a -> y' fork a)) (fork++ xs')

No-Cycle : ∀{m} (t : Term m) ps -> t ≡ ps ⊹ t -> ps ≡ []
No-Cycle _ [] refl = refl
No-Cycle (i x) (left _ ∷ xs) ()
No-Cycle leaf (left y ∷ xs) ()
No-Cycle {m} (s fork t) (left y ∷ xs) r = proof
  where f : Term m -> Term m
        f (s fork t) = s
        f _ = s
        hyp : xs ++L [ left t ] ≡ []
        hyp = No-Cycle s (xs ++L [ left t ]) (trans (cong f r) (proj₁ (fork++ xs)))
        proof : left y ∷ xs ≡ []
        proof = case (_,_ {B = λ x → x ++L _ ≡ _} xs hyp) of λ { ([] , ()) ; (_ ∷ _ , ()) }
No-Cycle (i x) (right _ ∷ xs) ()
No-Cycle leaf (right _ ∷ xs) ()
No-Cycle {m} (s fork t) (right y ∷ xs) r = proof
  where f : Term m -> Term m
        f (s fork t) = t
        f _ = s
        hyp = No-Cycle t (xs ++L [ right s ]) (trans (cong f r) (proj₂ (fork++ xs)))
        proof : right y ∷ xs ≡ []
        proof = case (_,_ {B = λ x → x ++L _ ≡ _} xs hyp) of λ { ([] , ()) ; (_ ∷ _ , ()) }


module Step2 where
  fact : ∀{m} (x : Fin m) p ps -> Nothing (Unifies (i x) ((p ∷ ps) ⊹ i x))
  fact x p ps f r with No-Cycle (f x) ((f ◃S) (p ∷ ps)) (trans r (StepM.fact2 f (i x) (p ∷ ps)))
  ... | ()


◇-assoc : ∀ {l m n o} (f : l ~> m) (g : n ~> _) (h : o ~> _) ->
               (f ◇ (g ◇ h)) ≐ ((f ◇ g) ◇ h)
◇-assoc f g h x = sym (Sub.fact2 f g (h x))

bind-assoc : ∀ {l m n o} (f : l ~> m) (g : n ~> _) (h : o ~> _) t -> (f ◇ g) ◃ (h ◃ t) ≡ (f ◇ (g ◇ h)) ◃ t
bind-assoc f g h t = sym (begin
           (f ◇ (g ◇ h)) ◃ t  ≡⟨ ◃ext (◇-assoc f g h) t ⟩
           ((f ◇ g) ◇ h) ◃ t  ≡⟨ Sub.fact2 (f ◇ g) h t ⟩
           (f ◇ g) ◃ (h  ◃ t)
                              ∎)

step-prop : ∀ {m n} (s t : Term (suc m)) (σ : AList m n) r z ->
          (Unifies s t [-◇ sub (σ asnoc r / z) ]) ⇔ (Unifies ((r for z) ◃ s) ((r for z) ◃ t) [-◇ sub σ ])
step-prop s t σ r z f = to , from
  where
    lemma1 : ∀ t -> (f ◇ sub σ) ◃ ((r for z) ◃ t) ≡ (f ◇ (sub σ ◇ (r for z))) ◃ t
    lemma1 t = bind-assoc f (sub σ) (r for z) t
    to = λ a → begin
                 (f ◇ sub σ) ◃ ((r for z) ◃ s) ≡⟨ lemma1 s ⟩
                 (f ◇ (sub σ ◇ (r for z))) ◃ s ≡⟨ a ⟩
                 (f ◇ (sub σ ◇ (r for z))) ◃ t ≡⟨ sym (lemma1 t) ⟩
                 (f ◇ sub σ) ◃ ((r for z) ◃ t) ∎
    from = λ a → begin
                   (f ◇ (sub σ ◇ (r for z))) ◃ s ≡⟨ sym (lemma1 s) ⟩
                   (f ◇ sub σ) ◃ ((r for z) ◃ s) ≡⟨ a ⟩
                   (f ◇ sub σ) ◃ ((r for z) ◃ t) ≡⟨ lemma1 t ⟩
                   (f ◇ (sub σ ◇ (r for z))) ◃ t ∎




-- We use a view so that we need to handle fewer cases in the main proof
data Amgu : {m : ℕ} -> (s t : Term m) -> ∃ (AList m) -> Maybe (∃ (AList m)) -> Set where
  Flip : ∀ {m s t acc} -> amgu t s acc ≡ amgu s t acc ->
    Amgu {m} t s acc (amgu t s acc) -> Amgu         s            t            acc        (amgu s t acc)
  leaf-leaf : ∀ {m acc} ->             Amgu {m}     leaf         leaf         acc        (just acc)
  leaf-fork : ∀ {m s t acc} ->         Amgu {m}     leaf         (s fork t)   acc        nothing
  fork-fork : ∀ {m s1 s2 t1 t2 acc} -> Amgu {m}     (s1 fork s2) (t1 fork t2) acc        (amgu s2 t2 =<< amgu s1 t1 acc)
  var-var   : ∀ {m x y} ->             Amgu         (i x)        (i y)        (m , anil) (just (flexFlex x y))
  var-t : ∀ {m x t} -> i x ≢ t ->      Amgu         (i x)        t            (m , anil) (flexRigid x t)
  s-t : ∀{m s t n σ r z} ->            Amgu {suc m} s            t            (n , σ asnoc r / z) ((λ σ -> σ ∃asnoc r / z) <$>
                                                                                                     amgu ((r for z) ◃ s) ((r for z) ◃ t) (n , σ))

view : ∀ {m : ℕ} -> (s t : Term m) -> (acc : ∃ (AList m)) -> Amgu s t acc (amgu s t acc)
view leaf         leaf         acc        = leaf-leaf
view leaf         (s fork t)   acc        = leaf-fork
view (s fork t)   leaf         acc        = Flip refl leaf-fork
view (s1 fork s2) (t1 fork t2) acc        = fork-fork
view (i x)        (i y)        (m , anil) = var-var
view (i x)        leaf         (m , anil) = var-t (λ ())
view (i x)        (s fork t)   (m , anil) = var-t (λ ())
view leaf         (i x)        (m , anil) = Flip refl (var-t (λ ()))
view (s fork t)   (i x)        (m , anil) = Flip refl (var-t (λ ()))
view (i x)        (i x')       (n , σ asnoc r / z) = s-t
view (i x)        leaf         (n , σ asnoc r / z) = s-t
view (i x)        (s fork t)   (n , σ asnoc r / z) = s-t
view leaf         (i x)        (n , σ asnoc r / z) = s-t
view (s fork t)   (i x)        (n , σ asnoc r / z) = s-t

amgu-Correctness : {m : ℕ} -> (s t : Term m) -> ∃ (AList m) -> Set
amgu-Correctness s t (l , ρ) =
    (∃ λ n → ∃ λ σ → π₁ (Max (Unifies s t [-◇ sub ρ ])) (sub σ) × amgu s t (l , ρ) ≡ just (n , σ ++ ρ ))
  ⊎ (Nothing ((Unifies s t) [-◇ sub ρ ]) ×  amgu s t (l , ρ) ≡ nothing)

amgu-Correctness⋆ : {m : ℕ} -> (s t : Term m) -> ∃ (AList m) -> Set
amgu-Correctness⋆ s t (l , ρ) =
    (∃ λ n → ∃ λ σ → π₁ (Max (Unifies s t [-◇ sub ρ ])) (sub σ) × amgu s t (l , ρ) ≡ just (n , σ ++ ρ ))
  ⊎ (Nothing ((Unifies s t) [-◇ sub ρ ]) ×  amgu s t (l , ρ) ≡ nothing)

amgu-Ccomm : ∀ {m} s t acc -> amgu {m} s t acc ≡ amgu t s acc -> amgu-Correctness s t acc -> amgu-Correctness t s acc
amgu-Ccomm s t (l , ρ) st≡ts = lemma
  where
    Unst = (Unifies s t) [-◇ sub ρ ]
    Unts = (Unifies t s) [-◇ sub ρ ]

    Unst⇔Unts : ((Unifies s t) [-◇ sub ρ ]) ⇔ ((Unifies t s) [-◇ sub ρ ])
    Unst⇔Unts = Properties.fact5 (Unifies s t) (Unifies t s) (sub ρ) (Properties.fact1 {_} {s} {t})

    lemma : amgu-Correctness s t (l , ρ) -> amgu-Correctness t s (l , ρ)
    lemma (inj₁ (n , σ , MaxUnst , amgu≡just)) =
      inj₁ (n , σ , proj₁ (Max.fact Unst Unts Unst⇔Unts (sub σ)) MaxUnst , trans (sym st≡ts) amgu≡just)
    lemma (inj₂ (NoUnst , amgu≡nothing)) =
      inj₂ ((λ {_} → Properties.fact2 Unst Unts Unst⇔Unts NoUnst) , trans (sym st≡ts) amgu≡nothing)

amgu-Ccomm⋆ : ∀ {m} s t acc -> amgu {m} s t acc ≡ amgu t s acc -> amgu-Correctness⋆ s t acc -> amgu-Correctness⋆ t s acc
amgu-Ccomm⋆ s t (l , ρ) st≡ts = lemma
  where
    Unst = (Unifies s t) [-◇ sub ρ ]
    Unts = (Unifies t s) [-◇ sub ρ ]

    Unst⇔Unts : ((Unifies s t) [-◇ sub ρ ]) ⇔ ((Unifies t s) [-◇ sub ρ ])
    Unst⇔Unts = Properties.fact5 (Unifies s t) (Unifies t s) (sub ρ) (Properties.fact1 {_} {s} {t})

    lemma : amgu-Correctness s t (l , ρ) -> amgu-Correctness t s (l , ρ)
    lemma (inj₁ (n , σ , MaxUnst , amgu≡just)) =
      inj₁ (n , σ , proj₁ (Max.fact Unst Unts Unst⇔Unts (sub σ)) MaxUnst , trans (sym st≡ts) amgu≡just)
    lemma (inj₂ (NoUnst , amgu≡nothing)) =
      inj₂ ((λ {_} → Properties.fact2 Unst Unts Unst⇔Unts NoUnst) , trans (sym st≡ts) amgu≡nothing)

amgu-c : ∀ {m s t l ρ} -> Amgu s t (l , ρ) (amgu s t (l , ρ)) ->
           (∃ λ n → ∃ λ σ → π₁ (Max ((Unifies s t) [-◇ sub ρ ])) (sub σ) × amgu {m} s t (l , ρ) ≡ just (n , σ ++ ρ ))
         ⊎ (Nothing ((Unifies s t) [-◇ sub ρ ])                          × amgu {m} s t (l , ρ) ≡ nothing)
amgu-c {m} {s} {t} {l} {ρ} amg with amgu s t (l , ρ)
amgu-c {l = l} {ρ} leaf-leaf | ._
  = inj₁ (l , anil , trivial-problem {_} {_} {leaf} {sub ρ} , cong (λ x -> just (l , x)) (sym (SubList.anil-id-l ρ)) )
amgu-c leaf-fork | .nothing = inj₂ ((λ _ () ) , refl)
amgu-c {m} {s1 fork s2} {t1 fork t2} {l} {ρ} fork-fork | ._
  with amgu s1 t1 (l , ρ)  | amgu-c $ view s1 t1 (l , ρ)
...  | .nothing            | inj₂ (nounify , refl) = inj₂ ((λ {_} -> No[Q◇ρ]→No[P◇ρ] No[Q◇ρ]) , refl)
  where
    P = Unifies (s1 fork s2) (t1 fork t2)
    Q = (Unifies s1 t1 ∧ Unifies s2 t2)
    Q⇔P : Q ⇔ P
    Q⇔P = switch P Q (Properties.fact1' {_} {s1} {s2} {t1} {t2})
    No[Q◇ρ]→No[P◇ρ] : Nothing (Q [-◇ sub ρ ]) -> Nothing (P [-◇ sub ρ ])
    No[Q◇ρ]→No[P◇ρ] = Properties.fact2 (Q [-◇ sub ρ ]) (P [-◇ sub ρ ]) (Properties.fact5 Q P (sub ρ) Q⇔P)
    No[Q◇ρ] : Nothing (Q [-◇ sub ρ ])
    No[Q◇ρ] = failure-propagation.first (sub ρ) (Unifies s1 t1) (Unifies s2 t2) nounify

... | .(just (n , σ ++ ρ)) | inj₁ (n , σ , a , refl)
 with amgu s2 t2 (n , σ ++ ρ) | amgu-c (view s2 t2 (n , (σ ++ ρ)))
... | .nothing                | inj₂ (nounify , refl) = inj₂ ( (λ {_} -> No[Q◇ρ]→No[P◇ρ] No[Q◇ρ]) , refl)
    where
    P = Unifies (s1 fork s2) (t1 fork t2)
    Q = (Unifies s1 t1 ∧ Unifies s2 t2)
    Q⇔P : Q ⇔ P
    Q⇔P = switch P Q (Properties.fact1' {_} {s1} {s2} {t1} {t2})
    No[Q◇ρ]→No[P◇ρ] : Nothing (Q [-◇ sub ρ ]) -> Nothing (P [-◇ sub ρ ])
    No[Q◇ρ]→No[P◇ρ] = Properties.fact2 (Q [-◇ sub ρ ]) (P [-◇ sub ρ ]) (Properties.fact5 Q P (sub ρ) Q⇔P)
    No[Q◇ρ] : Nothing (Q [-◇ sub ρ ])
    No[Q◇ρ] = failure-propagation.second (sub ρ) (sub σ) (Unifies s1 t1) (Unifies s2 t2) a
       (λ f Unifs2t2-f◇σ◇ρ → nounify f (π₂ (Unifies s2 t2) (λ t → cong (f ◃) (sym (SubList.fact1 σ ρ t))) Unifs2t2-f◇σ◇ρ))

... | .(just (n1 , σ1 ++ (σ ++ ρ))) | inj₁ (n1 , σ1 , b , refl)
    = inj₁ (n1 , σ1 ++ σ , Max[P∧Q◇ρ][σ1++σ] , cong (λ σ -> just (n1 , σ)) (++-assoc σ1 σ ρ))
    where
      P = Unifies s1 t1
      Q = Unifies s2 t2
      P∧Q = P ∧ Q
      C = Unifies (s1 fork s2) (t1 fork t2)
      Max[C◇ρ]⇔Max[P∧Q◇ρ] : Max (C [-◇ sub ρ ]) ⇔ Max (P∧Q [-◇ sub ρ ])
      Max[C◇ρ]⇔Max[P∧Q◇ρ] = Max.fact (C [-◇ sub ρ ]) (P∧Q [-◇ sub ρ ]) (Properties.fact5 C P∧Q (sub ρ)
                      (Properties.fact1' {_} {s1} {s2} {t1} {t2}))
      Max[Q◇σ++ρ]⇔Max[Q◇σ◇ρ] : Max (Q [-◇ sub (σ ++ ρ)]) ⇔ Max (Q [-◇ sub σ ◇ sub ρ ])
      Max[Q◇σ++ρ]⇔Max[Q◇σ◇ρ] = Max.fact (Q [-◇ sub (σ ++ ρ)]) (Q [-◇ sub σ ◇ sub ρ ]) (Properties.fact6 Q (SubList.fact1 σ ρ))
      Max[P∧Q◇ρ][σ1++σ] : π₁ (Max (C [-◇ sub ρ ])) (sub (σ1 ++ σ))
      Max[P∧Q◇ρ][σ1++σ] = π₂ (Max (C [-◇ sub ρ ])) (≐-sym (SubList.fact1 σ1 σ))
               (proj₂ (Max[C◇ρ]⇔Max[P∧Q◇ρ] (sub σ1 ◇ sub σ))
                      (optimist (sub ρ) (sub σ) (sub σ1) P Q (DClosed.fact1 s1 t1) a (proj₁ (Max[Q◇σ++ρ]⇔Max[Q◇σ◇ρ] (sub σ1)) b)))

amgu-c {suc l} {i x} {i y} (var-var) | .(just (flexFlex x y))
   with thick x y | Thick.fact1 x y (thick x y) refl
...  | .(just y') | inj₂ (y' , thinxy'≡y , refl )
  = inj₁ (l , anil asnoc i y' / x , var-elim-i-≡ x (i y) (sym (cong i thinxy'≡y)) , refl )
...  | .nothing | inj₁ ( x≡y , refl ) rewrite sym x≡y
  = inj₁ (suc l , anil , trivial-problem {_} {_} {i x} {sub anil} , refl)
amgu-c {suc l} {i x} {t} (var-t ix≢t) | .(flexRigid x t)
 with check x t | check-prop x t
... | .nothing  | inj₂ ( ps , r , refl) = inj₂ ( (λ {_} -> No-Unifier )  , refl)
  where
    No-Unifier : {n : ℕ} (f : Fin (suc l) → Term n) → f x ≡ f ◃ t → ⊥
    No-Unifier f fx≡f◃t = ix≢t (sym (trans r (cong (λ ps -> ps ⊹ i x) ps≡[])))
          where
            ps≡[] : ps ≡ []
            ps≡[] = map-[] f ps (No-Cycle (f x) ((f ◃S) ps)
                  (begin f x             ≡⟨ fx≡f◃t ⟩
                         f ◃ t           ≡⟨ cong (f ◃) r ⟩
                         f ◃ (ps ⊹ i x)  ≡⟨ StepM.fact2 f (i x) ps ⟩
                         (f ◃S) ps ⊹ f x ∎))


... | .(just t') | inj₁ (t' , r , refl) = inj₁ ( l , anil asnoc t' / x , var-elim-i-≡ x t r , refl )

amgu-c {suc m} {s} {t} {l} {ρ asnoc r / z} s-t
  | .((λ x' → x' ∃asnoc r / z) <$>
      (amgu ((r for z) ◃ s) ((r for z) ◃ t) (l , ρ)))
  with amgu-c (view ((r for z) ◃ s) ((r for z) ◃ t) (l , ρ))
... | inj₂ (nounify , ra) = inj₂ ( (λ {_} -> NoQ→NoP nounify) , cong (_<$>_ (λ x' → x' ∃asnoc r / z)) ra )
      where
        P = Unifies s t [-◇ sub (ρ asnoc r / z) ]
        Q = Unifies ((r for z) ◃ s) ((r for z) ◃ t) [-◇ sub ρ ]
        NoQ→NoP : Nothing Q → Nothing P
        NoQ→NoP = Properties.fact2 Q P (switch P Q (step-prop s t ρ r z))
... | inj₁ (n , σ , a , ra)  = inj₁ (n , σ , proj₂ (MaxP⇔MaxQ (sub σ)) a , cong (_<$>_ (λ x' → x' ∃asnoc r / z)) ra)
      where
        P = Unifies s t [-◇ sub (ρ asnoc r / z) ]
        Q = Unifies ((r for z) ◃ s) ((r for z) ◃ t) [-◇ sub ρ ]
        MaxP⇔MaxQ : Max P ⇔ Max Q
        MaxP⇔MaxQ = Max.fact P Q (step-prop s t ρ r z)
amgu-c {m} {s} {t} {l} {ρ} (Flip amguts≡amgust amguts) | ._ = amgu-Ccomm t s (l , ρ) amguts≡amgust (amgu-c amguts)
amgu-c {zero} {i ()}  _ | _



amgu-c⋆ : ∀ {m s t l ρ} -> Amgu s t (l , ρ) (amgu s t (l , ρ)) ->
           (∃ λ n → ∃ λ σ → (Max⋆ ((Unifies⋆ s t) [-◇⋆ sub ρ ])) (sub σ) × amgu {m} s t (l , ρ) ≡ just (n , σ ++ ρ ))
         ⊎ (Nothing⋆ ((Unifies⋆ s t) [-◇⋆ sub ρ ])                       × amgu {m} s t (l , ρ) ≡ nothing)
amgu-c⋆ {m} {s} {t} {l} {ρ} amg with amgu s t (l , ρ)
amgu-c⋆ {l = l} {ρ} leaf-leaf | ._
  = inj₁ (l , anil , trivial-problem {_} {_} {leaf} {sub ρ} , cong (λ x -> just (l , x)) (sym (SubList.anil-id-l ρ)) )
amgu-c⋆ leaf-fork | .nothing = inj₂ ((λ _ () ) , refl)
amgu-c⋆ {m} {s1 fork s2} {t1 fork t2} {l} {ρ} fork-fork | ._
  with amgu s1 t1 (l , ρ)  | amgu-c⋆ $ view s1 t1 (l , ρ)
...  | .nothing            | inj₂ (nounify , refl) = inj₂ ((λ {_} -> No[Q◇ρ]→No[P◇ρ] No[Q◇ρ]) , refl)
  where
    P = Unifies⋆ (s1 fork s2) (t1 fork t2)
    Q = (Unifies⋆ s1 t1 ∧⋆ Unifies⋆ s2 t2)
    Q⇔P : Q ⇔⋆ P
    Q⇔P = switch⋆ P Q (Properties.fact1' {_} {s1} {s2} {t1} {t2})
    No[Q◇ρ]→No[P◇ρ] : Nothing⋆ (Q [-◇⋆ sub ρ ]) -> Nothing⋆ (P [-◇⋆ sub ρ ])
    No[Q◇ρ]→No[P◇ρ] = Properties.fact2⋆ (Q [-◇⋆ sub ρ ]) (P [-◇⋆ sub ρ ]) (Properties.fact5⋆ Q P (sub ρ) Q⇔P)
    No[Q◇ρ] : Nothing⋆ (Q [-◇⋆ sub ρ ])
    No[Q◇ρ] = failure-propagation.first⋆ (sub ρ) (Unifies⋆ s1 t1) (Unifies⋆ s2 t2) nounify

... | .(just (n , σ ++ ρ)) | inj₁ (n , σ , a , refl)
 with amgu s2 t2 (n , σ ++ ρ) | amgu-c⋆ (view s2 t2 (n , (σ ++ ρ)))
... | .nothing                | inj₂ (nounify , refl) = inj₂ ( (λ {_} -> No[Q◇ρ]→No[P◇ρ]⋆ No[Q◇ρ]⋆) , refl)
    where
    P⋆ = Unifies⋆ (s1 fork s2) (t1 fork t2)
    Q⋆ = (Unifies⋆ s1 t1 ∧⋆ Unifies⋆ s2 t2)
    Q⇔P⋆ : Q⋆ ⇔⋆ P⋆
    Q⇔P⋆ = switch⋆ P⋆ Q⋆ (Properties.fact1'⋆ {_} {s1} {s2} {t1} {t2})
    No[Q◇ρ]→No[P◇ρ]⋆ : Nothing⋆ (Q⋆ [-◇⋆ sub ρ ]) -> Nothing⋆ (P⋆ [-◇⋆ sub ρ ])
    No[Q◇ρ]→No[P◇ρ]⋆ = Properties.fact2⋆ (Q⋆ [-◇⋆ sub ρ ]) (P⋆ [-◇⋆ sub ρ ]) (Properties.fact5⋆ Q⋆ P⋆ (sub ρ) Q⇔P⋆)
    No[Q◇ρ]⋆ : Nothing⋆ (Q⋆ [-◇⋆ sub ρ ])
    No[Q◇ρ]⋆ = failure-propagation.second⋆ (sub ρ) (sub σ) (Unifies⋆ s1 t1) (Unifies s2 t2) a
       (λ f → nounify f ∘ π₂ (Unifies s2 t2) (cong (f ◃) ∘ sym ∘ SubList.fact1 σ ρ))
{-
    No[Q◇ρ]⋆ = failure-propagation.second (sub ρ) (sub σ) (Unifies s1 t1) (Unifies s2 t2) a
--       (λ f Unifs2t2-f◇σ◇ρ → nounify f ((π₂ (Unifies s2 t2) (λ t → cong (f ◃) (sym (SubList.fact1 σ ρ t))) Unifs2t2-f◇σ◇ρ)))
--       (λ f → nounify f ∘ π₂ (Unifies s2 t2) (λ t → cong (f ◃) (sym (SubList.fact1 σ ρ t))))
       (λ f → nounify f ∘ π₂ (Unifies s2 t2) (cong (f ◃) ∘ sym ∘ SubList.fact1 σ ρ))
-}
    P = Unifies (s1 fork s2) (t1 fork t2)
    Q = (Unifies s1 t1 ∧ Unifies s2 t2)
    Q⇔P : Q ⇔ P
    Q⇔P = switch P Q (Properties.fact1' {_} {s1} {s2} {t1} {t2})
    No[Q◇ρ]→No[P◇ρ] : Nothing (Q [-◇ sub ρ ]) -> Nothing (P [-◇ sub ρ ])
    No[Q◇ρ]→No[P◇ρ] = Properties.fact2 (Q [-◇ sub ρ ]) (P [-◇ sub ρ ]) (Properties.fact5 Q P (sub ρ) Q⇔P)
    No[Q◇ρ] : Nothing (Q [-◇ sub ρ ])
    No[Q◇ρ] = failure-propagation.second (sub ρ) (sub σ) (Unifies s1 t1) (Unifies s2 t2) a
       (λ f Unifs2t2-f◇σ◇ρ → nounify f (π₂ (Unifies s2 t2) (λ t → cong (f ◃) (sym (SubList.fact1 σ ρ t))) Unifs2t2-f◇σ◇ρ))

... | .(just (n1 , σ1 ++ (σ ++ ρ))) | inj₁ (n1 , σ1 , b , refl)
    = inj₁ (n1 , σ1 ++ σ , Max[P∧Q◇ρ][σ1++σ] , cong (λ σ -> just (n1 , σ)) (++-assoc σ1 σ ρ))
    where
      P = Unifies s1 t1
      Q = Unifies s2 t2
      P∧Q = P ∧ Q
      C = Unifies (s1 fork s2) (t1 fork t2)
      Max[C◇ρ]⇔Max[P∧Q◇ρ] : Max (C [-◇ sub ρ ]) ⇔ Max (P∧Q [-◇ sub ρ ])
      Max[C◇ρ]⇔Max[P∧Q◇ρ] = Max.fact (C [-◇ sub ρ ]) (P∧Q [-◇ sub ρ ]) (Properties.fact5 C P∧Q (sub ρ)
                      (Properties.fact1' {_} {s1} {s2} {t1} {t2}))
      Max[Q◇σ++ρ]⇔Max[Q◇σ◇ρ] : Max (Q [-◇ sub (σ ++ ρ)]) ⇔ Max (Q [-◇ sub σ ◇ sub ρ ])
      Max[Q◇σ++ρ]⇔Max[Q◇σ◇ρ] = Max.fact (Q [-◇ sub (σ ++ ρ)]) (Q [-◇ sub σ ◇ sub ρ ]) (Properties.fact6 Q (SubList.fact1 σ ρ))
      Max[P∧Q◇ρ][σ1++σ] : π₁ (Max (C [-◇ sub ρ ])) (sub (σ1 ++ σ))
      Max[P∧Q◇ρ][σ1++σ] = π₂ (Max (C [-◇ sub ρ ])) (≐-sym (SubList.fact1 σ1 σ))
               (proj₂ (Max[C◇ρ]⇔Max[P∧Q◇ρ] (sub σ1 ◇ sub σ))
                      (optimist (sub ρ) (sub σ) (sub σ1) P Q (DClosed.fact1 s1 t1) a (proj₁ (Max[Q◇σ++ρ]⇔Max[Q◇σ◇ρ] (sub σ1)) b)))

amgu-c⋆ {suc l} {i x} {i y} (var-var) | .(just (flexFlex x y))
   with thick x y | Thick.fact1 x y (thick x y) refl
...  | .(just y') | inj₂ (y' , thinxy'≡y , refl )
  = inj₁ (l , anil asnoc i y' / x , var-elim-i-≡ x (i y) (sym (cong i thinxy'≡y)) , refl )
...  | .nothing | inj₁ ( x≡y , refl ) rewrite sym x≡y
  = inj₁ (suc l , anil , trivial-problem {_} {_} {i x} {sub anil} , refl)
amgu-c⋆ {suc l} {i x} {t} (var-t ix≢t) | .(flexRigid x t)
 with check x t | check-prop x t
... | .nothing  | inj₂ ( ps , r , refl) = inj₂ ( (λ {_} -> No-Unifier )  , refl)
  where
    No-Unifier : {n : ℕ} (f : Fin (suc l) → Term n) → f x ≡ f ◃ t → ⊥
    No-Unifier f fx≡f◃t = ix≢t (sym (trans r (cong (λ ps -> ps ⊹ i x) ps≡[])))
          where
            ps≡[] : ps ≡ []
            ps≡[] = map-[] f ps (No-Cycle (f x) ((f ◃S) ps)
                  (begin f x             ≡⟨ fx≡f◃t ⟩
                         f ◃ t           ≡⟨ cong (f ◃) r ⟩
                         f ◃ (ps ⊹ i x)  ≡⟨ StepM.fact2 f (i x) ps ⟩
                         (f ◃S) ps ⊹ f x ∎))


... | .(just t') | inj₁ (t' , r , refl) = inj₁ ( l , anil asnoc t' / x , var-elim-i-≡ x t r , refl )

amgu-c⋆ {suc m} {s} {t} {l} {ρ asnoc r / z} s-t
  | .((λ x' → x' ∃asnoc r / z) <$>
      (amgu ((r for z) ◃ s) ((r for z) ◃ t) (l , ρ)))
  with amgu-c⋆ (view ((r for z) ◃ s) ((r for z) ◃ t) (l , ρ))
... | inj₂ (nounify , ra) = inj₂ ( (λ {_} -> NoQ→NoP nounify) , cong (_<$>_ (λ x' → x' ∃asnoc r / z)) ra )
      where
        P = Unifies s t [-◇ sub (ρ asnoc r / z) ]
        Q = Unifies ((r for z) ◃ s) ((r for z) ◃ t) [-◇ sub ρ ]
        NoQ→NoP : Nothing Q → Nothing P
        NoQ→NoP = Properties.fact2 Q P (switch P Q (step-prop s t ρ r z))
... | inj₁ (n , σ , a , ra)  = inj₁ (n , σ , proj₂ (MaxP⇔MaxQ (sub σ)) a , cong (_<$>_ (λ x' → x' ∃asnoc r / z)) ra)
      where
        P = Unifies s t [-◇ sub (ρ asnoc r / z) ]
        Q = Unifies ((r for z) ◃ s) ((r for z) ◃ t) [-◇ sub ρ ]
        MaxP⇔MaxQ : Max P ⇔ Max Q
        MaxP⇔MaxQ = Max.fact P Q (step-prop s t ρ r z)
amgu-c⋆ {m} {s} {t} {l} {ρ} (Flip amguts≡amgust amguts) | ._ = amgu-Ccomm⋆ t s (l , ρ) amguts≡amgust (amgu-c⋆ amguts)
amgu-c⋆ {zero} {i ()}  _ | _



mgu-c : ∀ {m} (s t : Term m) ->
          (∃ λ n → ∃ λ σ → π₁ (Max (Unifies s t)) (sub σ) × mgu s t ≡ just (n , σ))
        ⊎ (Nothing (Unifies s t)                          × mgu s t ≡ nothing)
mgu-c {m} s t = amgu-c (view s t (m , anil))

mgu-c⋆ : ∀ {m} (s t : Term m) ->
           (∃ λ n → ∃ λ σ → (Max⋆ (Unifies⋆ s t)) (sub σ) × mgu s t ≡ just (n , σ))
         ⊎ (Nothing⋆ (Unifies⋆ s t)                         × mgu s t ≡ nothing)
mgu-c⋆ {m} s t = amgu-c (view s t (m , anil))

data SidedTerm (n : ℕ) : Set where
  i-left : (x : Fin n) -> 2 * Data.Fin.toℕ x Data.Nat.≤ n → SidedTerm n
  i-right : (x : Fin n) -> n + Data.Fin.toℕ x Data.Nat.≤ 2 * n → SidedTerm n
  leaf : SidedTerm n
  _fork_ : (s t : SidedTerm n) -> SidedTerm n

data dTerm (n : ℕ) : Term (2 * n) → Set where
--  i :

l1 : ∀ m → Data.Fin.toℕ (Data.Fin.fromℕ m) ≡ m
l1 zero = refl
l1 (suc m) = cong suc (l1 m)

l2 : ∀ m → m ≡ m + 0
l2 zero = refl
l2 (suc m) = cong suc (l2 m)

fixup : ∀ m → Fin (Data.Fin.toℕ (Data.Fin.fromℕ m) + m) → Fin (m + (m + 0))
fixup m x rewrite l1 m | sym (l2 m) = x

revise-down : ∀ {m} → Fin m → Fin (2 * m)
revise-down {m} x = Data.Fin.inject+ (m + 0) x

revise-up : ∀ {m} → Fin m → Fin (2 * m)
revise-up {m} x = fixup m (Data.Fin.fromℕ m Data.Fin.+ x)

{-
reduce* : ∀ {m n} (i : Fin (m * 2)) → Fin m
reduce* {zero}  i       i≥m       = i
reduce* {suc m} zero    ()
reduce* {suc m} (suc i) (s≤s i≥m) = reduce≥ i i≥m
-}

downFin : ∀ {m} {x : Fin (2 * m)} → suc (Data.Fin.toℕ x) Data.Nat.≤ m → Fin m
downFin {zero} {()} p₁
downFin {suc m} {zero} (s≤s p₁) = zero
downFin {suc zero} {suc zero} (s≤s p₁) = zero
downFin {suc zero} {suc (suc ())} (s≤s p₁)
downFin {suc (suc m)} {suc zero} (s≤s x<m) = suc zero
downFin {suc (suc m)} {suc (suc x)} (s≤s (s≤s x<m)) = suc ((downFin {suc m} {x = subst Fin (foo m) x} (s≤s {!x<m!}))) where
  foo : ∀ m → m + suc (suc (m + zero)) ≡ suc (m + suc (m + zero))
  foo zero = refl
  foo (suc m) rewrite foo m = cong suc {!refl!}


combineSubs : ∀ {m a} {A : Set a} → (Fin m → A) → (Fin m → A) → Fin (2 * m) → A
combineSubs {m} fl fr x with suc (Data.Fin.toℕ x) ≤? m
… | yes p = fl (downFin {x = x} p)
… | no _ = fr {!!}

write-variable-down : ∀ {m} → Term m → Term (2 * m)
write-variable-down {m} (i l) = i $ revise-down l
write-variable-down {m} leaf = leaf
write-variable-down {m} (s fork t) = write-variable-down s fork write-variable-down t

write-variable-up : ∀ {m} → Term m → Term (2 * m)
write-variable-up {m} (i r) = i (revise-up r)
write-variable-up {m} leaf = leaf
write-variable-up {m} (s fork t) = write-variable-up s fork write-variable-up t

write-variables-apart : ∀ {m} (s t : Term m) → Term (2 * m) × Term (2 * m)
write-variables-apart s t = write-variable-down s , write-variable-up t

separate-substitutions-down : ∀ {m n} → (Fin (2 * m) → Term n) → Fin m → Term n
separate-substitutions-down {m} f x = f $ revise-down x

separate-substitutions-up : ∀ {m n} → (Fin (2 * m) → Term n) → Fin m → Term n
separate-substitutions-up {m} f x = f $ revise-up x

separate-substitutions : ∀ {m n} → (Fin (2 * m) → Term n) → (Fin m → Term n) × (Fin m → Term n)
separate-substitutions {m} x = separate-substitutions-down {m} x , separate-substitutions-up {m} x

Property⋆2 : (m : ℕ) -> Set1
Property⋆2 m = ∀ {n} -> (Fin m -> Term n) × (Fin m -> Term n) -> Set

Nothing⋆2 : ∀{m} -> (P : Property⋆2 m) -> Set
Nothing⋆2 P = ∀{n} f -> P {n} f -> ⊥

Unifies⋆2 : ∀ {m} (s t : Term m) -> Property⋆2 m
Unifies⋆2 s t (f₁ , f₂) = f₁ ◃ s ≡ f₂ ◃ t

_≤2_ : ∀ {m n n'} (f : (Fin m -> Term n) × (Fin m -> Term n)) (g : (Fin m -> Term n') × (Fin m -> Term n')) -> Set
(f₁ , f₂) ≤2 (g₁ , g₂) = ∃ λ f' -> f₁ ≐ (f' ◇ g₁) × f₂ ≐ (f' ◇ g₂)

Max⋆2 : ∀ {m} (P : Property⋆2 m) -> Property⋆2 m
Max⋆2 P f = P f × (∀ {n} f' -> P {n} f' -> f' ≤2 f)

pair-mgu : ∀ {m} -> (s t : Term m) -> Maybe (∃ (AList m))
pair-mgu {m} s t = {!!} -- amgu s t (m , anil)


write≡separate : ∀ {m n} (σ : AList (2 * m) n) (t : Term m) → (sub σ ◃) (write-variable-down t) ≡ ((separate-substitutions-down $ sub σ) ◃) t
write≡separate {zero} {.0} anil (i x) = refl
write≡separate {suc m} {.(suc (m + suc (m + 0)))} anil (i x) = refl
write≡separate {suc m} {n} (σ asnoc t' / x) (i x₁) = refl
write≡separate σ leaf = refl
write≡separate σ (t₁ fork t₂) = cong₂ _fork_ (write≡separate σ t₁) (write≡separate σ t₂)

write≡separate' : ∀ {m n} (σ : AList (2 * m) n) (t : Term m) → (sub σ ◃) (write-variable-down t) ≡ ((separate-substitutions-down $ sub σ) ◃) t
write≡separate' {zero} {.0} anil (i x) = refl
write≡separate' {suc m} {.(suc (m + suc (m + 0)))} anil (i x) = refl
write≡separate' {suc m} {n} (σ asnoc t' / x) (i x₁) = refl
write≡separate' σ leaf = refl
write≡separate' σ (t₁ fork t₂) = cong₂ _fork_ (write≡separate σ t₁) (write≡separate σ t₂)

{-
(sub σ ◃) (write-variable-down s') ≡ (sub σ ◃) (write-variable-up t') →
((separate-substitutions-down $ sub σ) ◃) s' ≡ ((separate-substitutions-up $ sub σ) ◃) t'
-}

pair-mgu-c⋆! : ∀ {m} (s' t' : Term m) (let (s , t) = write-variables-apart s' t') ->
                (∃ λ n → ∃ λ σ → ∃ λ σ₁ → ∃ λ σ₂ → (σ₁ , σ₂) ≡ separate-substitutions (sub σ) × (Max⋆2 (Unifies⋆2 s' t')) (σ₁ , σ₂) × mgu s t ≡ just (n , σ))
              ⊎ (Nothing⋆2 (Unifies⋆2 s t)                       × mgu s t ≡ nothing)
pair-mgu-c⋆! {m} s' t'
  with write-variable-down s' | inspect write-variable-down s' | write-variable-up t' | inspect write-variable-up t'
… | s | Reveal_·_is_.[_] refl | t | Reveal_·_is_.[_] refl with amgu-c⋆ (view s t (2 * m , anil))
… | (inj₁ (n , σ , (s-un-t , s-un-t-correct) , amgu=nσ)) = inj₁ (_ , σ , ((separate-substitutions-down $ sub σ) , ((separate-substitutions-up $ sub σ) , (refl , (({!trans (sym $ write≡separate σ s') s-un-t!} , (λ {(fl , fr) x → ((proj₁ ∘ s-un-t-correct (combineSubs fl fr)) {!(proj₂ ∘ s-un-t-correct (combineSubs fl fr)) !}) , ({!!} , {!!})})) , amgu=nσ))))) where
… | (inj₂ (s-not-un-t , amgu=nothing)) = inj₂ {!!}

-- pair-mgu-c⋆ : ∀ {m} (s' t' : Term m) (let (s , t) = write-variables-apart s' t') ->
--                 (∃ λ n → ∃ λ σ → ∃ λ σ₁ → ∃ λ σ₂ → (σ₁ , σ₂) ≡ separate-substitutions {m} {n} (sub {2 * m} {n} σ) × (Max⋆2 (Unifies⋆2 s t)) (σ₁ , σ₂) × mgu s t ≡ just (n , σ))
--               ⊎ (Nothing⋆2 (Unifies⋆2 s t)                       × mgu s t ≡ nothing)
-- pair-mgu-c⋆ {m} s' t'
--   with write-variables-apart s' t'
-- … | (s , t) with amgu-c⋆ (view s t (2 * m , anil))
-- pair-mgu-c⋆ {m} s' t' | s , t | (inj₁ (n , σ , (s-un-t , s-un-t-correct) , amgu=nσ)) = inj₁ ({!!} , {!!})
-- pair-mgu-c⋆ {m} s' t' | s , t | (inj₂ (s-not-un-t , amgu=nothing)) = inj₂ {!!}

-- -- pair-mgu-c⋆ {m} s t = {!!} -- amgu-c (view s t (m , anil))
-- {-
-- Goal: Σ ℕ
--       (λ n₁ →
--          Σ (AList (m + (m + 0)) n₁)
--          (λ σ₁ →
--             Σ (Fin (m + (m + 0)) → Term n₁)
--             (λ σ₂ →
--                Σ (Fin (m + (m + 0)) → Term n₁)
--                (λ σ₃ →
--                   Σ ((σ₂ , σ₃) ≡ (?8 (sub σ₁) , ?9 (sub σ₁)))
--                   (λ x →
--                      Σ
--                      (Σ ((σ₂ ◃) s ≡ (σ₃ ◃) t)
--                       (λ x₁ →
--                          {n = n₂ : ℕ}
--                          (f'
--                           : Σ (Fin (m + (m + 0)) → Term n₂)
--                             (λ x₂ → Fin (m + (m + 0)) → Term n₂)) →
--                          (proj₁ f' ◃) s ≡ (proj₂ f' ◃) t →
--                          Σ (Fin n₁ → Term n₂)
--                          (λ f'' →
--                             Σ ((x₂ : Fin (m + (m + 0))) → proj₁ f' x₂ ≡ (f'' ◃) (σ₂ x₂))
--                             (λ x₂ →
--                                (x₃ : Fin (m + (m + 0))) → proj₂ f' x₃ ≡ (f'' ◃) (σ₃ x₃)))))
--                      (λ x₁ → amgu s t (m + (m + 0) , anil) ≡ just (n₁ , σ₁)))))))
--       ⊎
--       Σ
--       ({n = n₁ : ℕ}
--        (f
--         : Σ (Fin (m + (m + 0)) → Term n₁)
--           (λ x → Fin (m + (m + 0)) → Term n₁)) →
--        (proj₁ f ◃) s ≡ (proj₂ f ◃) t → ⊥)
--       (λ x → amgu s t (m + (m + 0) , anil) ≡ nothing)
-- ————————————————————————————————————————————————————————————
-- t'      : Term m
-- s'      : Term m
-- amgu=nσ : amgu s t (m + (m + 0) , anil) ≡ just (n , σ)
-- s-un-t-correct
--         : {n = n₁ : ℕ} (f' : Fin (m + (m + 0)) → Term n₁) →
--           (f' ◃) s ≡ (f' ◃) t →
--           Σ (Fin n → Term n₁)
--           (λ f'' → (x : Fin (m + (m + 0))) → f' x ≡ (f'' ◃) (sub σ x))
-- s-un-t  : (sub σ ◃) s ≡ (sub σ ◃) t
-- σ       : AList (m + (m + 0)) n
-- n       : ℕ
-- t       : Term (m + (m + 0))
-- s       : Term (m + (m + 0))
-- m       : ℕ
-- -}
