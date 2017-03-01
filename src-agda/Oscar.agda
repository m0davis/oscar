
module Oscar (FunctionName : Set) where

open import Oscar.Data.Fin using (Fin; zero; suc; thick?)

open import Data.Nat using (ℕ; suc; zero)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong₂; cong; sym; trans)
open import Function using (_∘_; flip)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.Product using (∃; _,_; _×_)
open import Data.Empty using (⊥-elim)
open import Data.Vec using (Vec; []; _∷_)

data Term (n : ℕ) : Set where
  i : (x : Fin n) -> Term n
  leaf : Term n
  _fork_ : (s t : Term n) -> Term n
  function : FunctionName → ∀ {f} → Vec (Term n) f → Term n

Term-function-inj-FunctionName : ∀ {fn₁ fn₂} {n N₁ N₂} {ts₁ : Vec (Term n) N₁} {ts₂ : Vec (Term n) N₂} → Term.function fn₁ ts₁ ≡ Term.function fn₂ ts₂ → fn₁ ≡ fn₂
Term-function-inj-FunctionName refl = refl

Term-function-inj-VecSize : ∀ {fn₁ fn₂} {n N₁ N₂} {ts₁ : Vec (Term n) N₁} {ts₂ : Vec (Term n) N₂} → Term.function fn₁ ts₁ ≡ Term.function fn₂ ts₂ → N₁ ≡ N₂
Term-function-inj-VecSize refl = refl

Term-function-inj-Vector : ∀ {fn₁ fn₂} {n N} {ts₁ : Vec (Term n) N} {ts₂ : Vec (Term n) N} → Term.function fn₁ ts₁ ≡ Term.function fn₂ ts₂ → ts₁ ≡ ts₂
Term-function-inj-Vector refl = refl

Term-fork-inj-left : ∀ {n} {l₁ r₁ l₂ r₂ : Term n} → l₁ fork r₁ ≡ l₂ fork r₂ → l₁ ≡ l₂
Term-fork-inj-left refl = refl

Term-fork-inj-right : ∀ {n} {l₁ r₁ l₂ r₂ : Term n} → l₁ fork r₁ ≡ l₂ fork r₂ → r₁ ≡ r₂
Term-fork-inj-right refl = refl

open import Relation.Binary.HeterogeneousEquality using (_≅_; refl)

Term-function-inj-HetVector : ∀ {fn₁ fn₂} {n N₁ N₂} {ts₁ : Vec (Term n) N₁} {ts₂ : Vec (Term n) N₂} → Term.function fn₁ ts₁ ≡ Term.function fn₂ ts₂ → ts₁ ≅ ts₂
Term-function-inj-HetVector refl = refl

_~>_ : (m n : ℕ) -> Set
m ~> n = Fin m -> Term n

▹ : ∀ {m n} -> (r : Fin m -> Fin n) -> Fin m -> Term n
▹ r = i ∘ r

record Substitution (T : ℕ → Set) : Set where
  field
    _◃_ : ∀ {m n} -> (f : m ~> n) -> T m -> T n

open Substitution ⦃ … ⦄ public

{-# DISPLAY Substitution._◃_ _ = _◃_ #-}

mutual

  instance SubstitutionTerm : Substitution Term
  Substitution._◃_ SubstitutionTerm = _◃′_ where
    _◃′_ : ∀ {m n} -> (f : m ~> n) -> Term m -> Term n
    f ◃′ i x = f x
    f ◃′ leaf = leaf
    f ◃′ (s fork t) = (f ◃ s) fork (f ◃ t)
    f ◃′ (function fn ts) = function fn (f ◃ ts)

  instance SubstitutionVecTerm : ∀ {N} → Substitution (flip Vec N ∘ Term )
  Substitution._◃_ (SubstitutionVecTerm {N}) = _◃′_ where
    _◃′_ : ∀ {m n} -> (f : m ~> n) -> Vec (Term m) N -> Vec (Term n) N
    f ◃′ [] = []
    f ◃′ (t ∷ ts) = f ◃ t ∷ f ◃ ts

_≐_ : {m n : ℕ} -> (Fin m -> Term n) -> (Fin m -> Term n) -> Set
f ≐ g = ∀ x -> f x ≡ g x

record SubstitutionExtensionality (T : ℕ → Set) ⦃ _ : Substitution T ⦄ : Set₁ where
  field
    ◃ext : ∀ {m n} {f g : Fin m -> Term n} -> f ≐ g -> (t : T m) -> f ◃ t ≡ g ◃ t

open SubstitutionExtensionality ⦃ … ⦄ public

mutual

  instance SubstitutionExtensionalityTerm : SubstitutionExtensionality Term
  SubstitutionExtensionality.◃ext SubstitutionExtensionalityTerm = ◃ext′ where
    ◃ext′ : ∀ {m n} {f g : Fin m -> Term n} -> f ≐ g -> ∀ t -> f ◃ t ≡ g ◃ t
    ◃ext′ p (i x) = p x
    ◃ext′ p leaf = refl
    ◃ext′ p (s fork t) = cong₂ _fork_ (◃ext p s) (◃ext p t)
    ◃ext′ p (function fn ts) = cong (function fn) (◃ext p ts)

  instance SubstitutionExtensionalityVecTerm : ∀ {N} → SubstitutionExtensionality (flip Vec N ∘ Term)
  SubstitutionExtensionality.◃ext (SubstitutionExtensionalityVecTerm {N}) = λ x → ◃ext′ x where
    ◃ext′ : ∀ {m n} {f g : Fin m -> Term n} -> f ≐ g -> ∀ {N} (t : Vec (Term m) N) -> f ◃ t ≡ g ◃ t
    ◃ext′ p [] = refl
    ◃ext′ p (t ∷ ts) = cong₂ _∷_ (◃ext p t) (◃ext p ts)

_◇_ : ∀ {l m n : ℕ } -> (f : Fin m -> Term n) (g : Fin l -> Term m) -> Fin l -> Term n
f ◇ g = (f ◃_) ∘ g

≐-cong : ∀ {m n o} {f : m ~> n} {g} (h : _ ~> o) -> f ≐ g -> (h ◇ f) ≐ (h ◇ g)
≐-cong h f≐g t = cong (h ◃_) (f≐g t)

≐-sym : ∀ {m n} {f : m ~> n} {g} -> f ≐ g -> g ≐ f
≐-sym f≐g = sym ∘ f≐g

module Sub where
  record Fact1 (T : ℕ → Set) ⦃ _ : Substitution T ⦄ : Set where
    field
      fact1 : ∀ {n} -> (t : T n) -> i ◃ t ≡ t

  open Fact1 ⦃ … ⦄ public

  mutual

    instance Fact1Term : Fact1 Term
    Fact1.fact1 Fact1Term (i x) = refl
    Fact1.fact1 Fact1Term leaf = refl
    Fact1.fact1 Fact1Term (s fork t) = cong₂ _fork_ (fact1 s) (fact1 t)
    Fact1.fact1 Fact1Term (function fn ts) = cong (function fn) (fact1 ts)

    instance Fact1TermVec : ∀ {N} → Fact1 (flip Vec N ∘ Term)
    Fact1.fact1 Fact1TermVec [] = refl
    Fact1.fact1 Fact1TermVec (t ∷ ts) = cong₂ _∷_ (fact1 t) (fact1 ts)

  record Fact2 (T : ℕ → Set) ⦃ _ : Substitution T ⦄ : Set where
    field
      -- ⦃ s ⦄ : Substitution T
      fact2 : ∀ {l m n} -> {f : Fin m -> Term n} {g : _} (t : T l) → (f ◇ g) ◃ t ≡ f ◃ (g ◃ t)

  open Fact2 ⦃ … ⦄ public

  mutual

    instance Fact2Term : Fact2 Term
    -- Fact2.s Fact2Term = SubstitutionTerm
    Fact2.fact2 Fact2Term (i x) = refl
    Fact2.fact2 Fact2Term leaf = refl
    Fact2.fact2 Fact2Term (s fork t) = cong₂ _fork_ (fact2 s) (fact2 t)
    Fact2.fact2 Fact2Term {f = f} {g = g} (function fn ts) = cong (function fn) (fact2 {f = f} {g = g} ts) -- fact2 ts

    instance Fact2TermVec : ∀ {N} → Fact2 (flip Vec N ∘ Term)
    -- Fact2.s Fact2TermVec = SubstitutionVecTerm
    Fact2.fact2 Fact2TermVec [] = refl
    Fact2.fact2 Fact2TermVec (t ∷ ts) = cong₂ _∷_ (fact2 t) (fact2 ts)

  fact3 : ∀ {l m n} (f : Fin m -> Term n) (r : Fin l -> Fin m) -> (f ◇ (▹ r)) ≡ (f ∘ r)
  fact3 f r = refl

◃ext' : ∀ {m n o} {f : Fin m -> Term n}{g : Fin m -> Term o}{h} -> f ≐ (h ◇ g) -> ∀ (t : Term _) -> f ◃ t ≡ h ◃ (g ◃ t)
◃ext' p t = trans (◃ext p t) (Sub.fact2 t)

open import Data.Maybe using (Maybe; nothing; just; functor; maybe′)
open import Category.Monad
import Level
open RawMonad (Data.Maybe.monad {Level.zero})

record Check (T : ℕ → Set) : Set where
  field
    check : ∀{n} (x : Fin (suc n)) (t : T (suc n)) -> Maybe (T n)

open Check ⦃ … ⦄ public

_<*>_ = _⊛_

mutual

  instance CheckTerm : Check Term
  Check.check CheckTerm x (i y) = i <$> thick? x y
  Check.check CheckTerm x leaf = just leaf
  Check.check CheckTerm x (s fork t) = _fork_ <$> check x s ⊛ check x t
  Check.check CheckTerm x (function fn ts) = ⦇ (function fn) (check x ts) ⦈

  instance CheckTermVec : ∀ {N} → Check (flip Vec N ∘ Term)
  Check.check CheckTermVec x [] = just []
  Check.check CheckTermVec x (t ∷ ts) = ⦇ check x t ∷ check x ts ⦈

_for_ : ∀ {n} (t' : Term n) (x : Fin (suc n)) -> Fin (suc n) -> Term n
(t' for x) y = maybe′ i t' (thick? x y)

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
      ◃-assoc = Sub.fact2 t

_∃asnoc_/_ : ∀ {m} (a : ∃ (AList m)) (t' : Term m) (x : Fin (suc m))
  -> ∃ (AList (suc m))
(n , σ) ∃asnoc t' / x = n , σ asnoc t' / x

flexFlex : ∀ {m} (x y : Fin m) -> ∃ (AList m)
flexFlex {suc m} x y with thick? x y
...              | just y' = m , anil asnoc i y' / x
...              | nothing = suc m , anil
flexFlex {zero} () _

flexRigid : ∀ {m} (x : Fin m) (t : Term m) -> Maybe (∃(AList m))
flexRigid {suc m} x t with check x t
...                   | just t' = just (m , anil asnoc t' / x)
...                   | nothing = nothing
flexRigid {zero} () _
