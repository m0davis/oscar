
module UnifyTermL (A : Set) where

open import Data.Fin using (Fin; suc; zero)
open import Data.Nat using (ℕ; suc; zero)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong₂; cong; sym; trans)
open import Function using (_∘_)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.Product using (∃; _,_; _×_)
open import Data.Empty using (⊥-elim)

data Term (n : ℕ) : Set where
  i : (x : Fin n) -> Term n
  leaf : A → Term n
  _fork_ : (s t : Term n) -> Term n

Term-leaf-inj : ∀ {n l₁ l₂} → leaf {n} l₁ ≡ leaf l₂ → l₁ ≡ l₂
Term-leaf-inj refl = refl

_~>_ : (m n : ℕ) -> Set
m ~> n = Fin m -> Term n

▹ : ∀ {m n} -> (r : Fin m -> Fin n) -> Fin m -> Term n
▹ r = i ∘ r

_◃_ : ∀ {m n} -> (f : m ~> n) -> Term m -> Term n
f ◃ i x = f x
f ◃ (leaf l) = leaf l
f ◃ (s fork t) = (f ◃ s) fork (f ◃ t)

_≐_ : {m n : ℕ} -> (Fin m -> Term n) -> (Fin m -> Term n) -> Set
f ≐ g = ∀ x -> f x ≡ g x

◃ext : ∀ {m n} {f g : Fin m -> Term n} -> f ≐ g -> ∀ t -> f ◃ t ≡ g ◃ t
◃ext p (i x) = p x
◃ext p (leaf l) = refl
◃ext p (s fork t) = cong₂ _fork_ (◃ext p s) (◃ext p t)

_◇_ : ∀ {l m n : ℕ } -> (f : Fin m -> Term n) (g : Fin l -> Term m) -> Fin l -> Term n
f ◇ g = (f ◃_) ∘ g

≐-cong : ∀ {m n o} {f : m ~> n} {g} (h : _ ~> o) -> f ≐ g -> (h ◇ f) ≐ (h ◇ g)
≐-cong h f≐g t = cong (h ◃_) (f≐g t)

≐-sym : ∀ {m n} {f : m ~> n} {g} -> f ≐ g -> g ≐ f
≐-sym f≐g = sym ∘ f≐g

module Sub where
  fact1 : ∀ {n} -> (t : Term n) -> i ◃ t ≡ t
  fact1 (i x) = refl
  fact1 (leaf l) = refl
  fact1 (s fork t) = cong₂ _fork_ (fact1 s) (fact1 t)

  fact2 : ∀ {l m n} -> (f : Fin m -> Term n) (g : _) (t : Term l)
    -> (f ◇ g) ◃ t ≡ f ◃ (g ◃ t)
  fact2 f g (i x) = refl
  fact2 f g (leaf l) = refl
  fact2 f g (s fork t) = cong₂ _fork_ (fact2 f g s) (fact2 f g t)

  fact3 : ∀ {l m n} (f : Fin m -> Term n) (r : Fin l -> Fin m) -> (f ◇ (▹ r)) ≡ (f ∘ r)
  fact3 f r = refl -- ext (λ _ -> refl)

◃ext' : ∀ {m n o} {f : Fin m -> Term n}{g : Fin m -> Term o}{h} -> f ≐ (h ◇ g) -> ∀ t -> f ◃ t ≡ h ◃ (g ◃ t)
◃ext' p t = trans (◃ext p t) (Sub.fact2 _ _ t)

open import Data.Maybe
open import Category.Functor
open import Category.Monad
import Level
open RawMonad (Data.Maybe.monad {Level.zero})

open import UnifyFin

check : ∀{n} (x : Fin (suc n)) (t : Term (suc n)) -> Maybe (Term n)
check x (i y) = i <$> thick x y
check x (leaf l) = just (leaf l)
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
