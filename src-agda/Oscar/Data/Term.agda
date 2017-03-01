
module Oscar.Data.Term (FunctionName : Set) where

open import Oscar.Data.Fin using (Fin; zero; suc; thick?; Check; check; thin; module Thick)

open import Data.Fin using (Fin; suc; zero)
open import Data.Nat hiding (_≤_)
open import Relation.Binary.PropositionalEquality renaming ([_] to [[_]])
open import Function using (_∘_; id; case_of_; _$_; flip)
open import Relation.Nullary
open import Data.Product renaming (map to _***_)
open import Data.Empty
open import Data.Maybe
open import Category.Functor
open import Category.Monad
import Level
open RawMonad (Data.Maybe.monad {Level.zero})
open import Data.Sum
open import Data.Maybe using (maybe; maybe′; nothing; just; monad; Maybe)
open import Data.List renaming (_++_ to _++L_)
open ≡-Reasoning
open import Data.Vec using (Vec; []; _∷_) renaming (_++_ to _++V_; map to mapV)

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

open import Data.Maybe using (Maybe; nothing; just; functor; maybe′; maybe)
open import Category.Monad
import Level
--open RawMonad (Data.Maybe.monad {Level.zero})
open import Data.Nat using (ℕ)

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

open import Data.Product using () renaming (Σ to Σ₁)
open Σ₁ renaming (proj₁ to π₁; proj₂ to π₂)

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

Unifies⋆V : ∀ {m N} (ss ts : Vec (Term m) N) -> Property⋆ m
Unifies⋆V ss ts f = f ◃ ss ≡ f ◃ ts

open import Relation.Binary.PropositionalEquality renaming ([_] to [[_]])
open ≡-Reasoning

Unifies : ∀ {m} (s t : Term m) -> Property m
Unifies s t = (λ {_} -> Unifies⋆ s t) , λ {_} {f} {g} f≐g f◃s=f◃t ->
  begin
    g ◃ s
  ≡⟨ sym (◃ext f≐g s) ⟩
    f ◃ s
  ≡⟨ f◃s=f◃t ⟩
    f ◃ t
  ≡⟨ ◃ext f≐g t ⟩
    g ◃ t
  ∎

UnifiesV : ∀ {m} {N} (s t : Vec (Term m) N) -> Property m
UnifiesV s t = (λ {_} -> Unifies⋆V s t) , λ {_} {f} {g} f≐g f◃s=f◃t ->
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

-- open import Data.Product renaming (map to _***_)
open import Data.Product using (Σ)
open Σ

_∧_ : ∀{m} -> (P Q : Property m) -> Property m
P ∧ Q = (λ {_} f -> π₁ P f × π₁ Q f) , λ {_} {_} {_} f≐g Pf×Qf -> π₂ P f≐g (proj₁ Pf×Qf) , π₂ Q f≐g (proj₂ Pf×Qf)


_⇔⋆_ : ∀{m} -> (P Q : Property⋆ m) -> Set
P ⇔⋆ Q = ∀ {n} f -> (P {n} f -> Q f) × (Q f -> P f)

_⇔_ : ∀{m} -> (P Q : Property m) -> Set
P ⇔ Q = ∀ {n} f -> (π₁ P {n} f -> π₁ Q f) × (π₁ Q f -> π₁ P f)

switch⋆ : ∀ {m} (P Q : Property⋆ m) -> P ⇔⋆ Q -> Q ⇔⋆ P
switch⋆ _ _ P⇔Q f = proj₂ (P⇔Q f) , proj₁ (P⇔Q f)

switch : ∀ {m} (P Q : Property m) -> P ⇔ Q -> Q ⇔ P
switch _ _ P⇔Q f = proj₂ (P⇔Q f) , proj₁ (P⇔Q f)

open import Data.Empty

Nothing⋆ : ∀{m} -> (P : Property⋆ m) -> Set
Nothing⋆ P = ∀{n} f -> P {n} f -> ⊥

Nothing : ∀{m} -> (P : Property m) -> Set
Nothing P = ∀{n} f -> π₁ P {n} f -> ⊥

_[-◇⋆_] : ∀{m n} (P : Property⋆ m) (f : Fin m -> Term n) -> Property⋆ n
(P [-◇⋆ f ]) g = P (g ◇ f)

_[-◇_] : ∀{m n} (P : Property m) (f : Fin m -> Term n) -> Property n
P [-◇ f ] = (λ {_} g -> π₁ P (g ◇ f)) , λ {_} {f'} {g'} f'≐g' Pf'◇f -> π₂ P (◃ext f'≐g' ∘ f)  Pf'◇f

open import Function using (_∘_; id; case_of_; _$_; flip)
open import Data.Product using (curry; uncurry)

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

  fact1'V : ∀ {m} {t₁ t₂ : Term m} {N} {ts₁ ts₂ : Vec (Term m) N}
         -> UnifiesV (t₁ ∷ ts₁) (t₂ ∷ ts₂) ⇔ (Unifies t₁ t₂ ∧ UnifiesV ts₁ ts₂)
  fact1'V f = deconstr _ _ _ _ , uncurry (cong₂ _∷_)
    where deconstr : ∀ {m} (t₁ t₂ : Term m) {N} (ts₁ ts₂ : Vec (Term m) N)
                   -> (t₁ Vec.∷ ts₁) ≡ (t₂ ∷ ts₂)
                   -> (t₁ ≡ t₂) × (ts₁ ≡ ts₂)
          deconstr s1 _ s2! _ refl = refl , refl -- refl , refl


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
      proof x = trans z (sym (Sub.fact2 (h x)))
        where z = trans (pfg x) (cong (fg ◃_) (pgh x))

  i-max : ∀ {m n} (f : Fin m -> Term n) -> f ≤ i
  i-max f = f , λ _ -> refl

  dist : ∀{l m n o}{f : Fin l -> Term m}{g : _ -> Term n}(h : Fin o -> _) -> f ≤ g -> (f ◇ h) ≤ (g ◇ h)
  dist h (fg , pfg) = fg  , λ x -> trans (◃ext pfg (h x)) (Sub.fact2 (h x))

Max⋆ : ∀ {m} (P : Property⋆ m) -> Property⋆ m
Max⋆ P f = P f × (∀ {n} f' -> P {n} f' -> f' ≤ f)

Max : ∀ {m} (P : Property m) -> Property m
Max P' = (λ {_} → Max⋆ P) , λ {_} {_} {_} -> lemma1
  where
    open Σ₁ P' renaming (proj₁ to P; proj₂ to Peq)
    lemma1 : {m : ℕ} {f : Fin _ → Term m} {g : Fin _ → Term m} →
             f ≐ g →
             P f × ({n : ℕ} (f' : Fin _ → Term n) → P f' → f' ≤ f) →
             P g × ({n : ℕ} (f' : Fin _ → Term n) → P f' → f' ≤ g)
    lemma1 {_} {f} {g} f≐g (Pf , MaxPf) = Peq f≐g Pf , λ {_} -> lemma2
      where
        lemma2 : ∀ {n} f' → P {n} f' → ∃ λ f0 → f' ≐ (f0 ◇ g)
        lemma2 f' Pf' = f0 , λ x -> trans (f'≐f0◇f x) (cong (f0 ◃_) (f≐g x))
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
         ≡⟨ cong (f≤g ◃_) gs=gt ⟩
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
     (Peq (sym ∘ Sub.fact2 ∘ a) (DCP (q ◇ (p ◇ a)) (p ◇ a) (q , λ _ -> refl) Ppa)
      , Qeq (sym ∘ Sub.fact2 ∘ a) Qqpa )
     , λ {_} -> aux
  where
    open Σ₁ P' renaming (proj₁ to P; proj₂ to Peq)
    open Σ₁ Q' renaming (proj₁ to Q; proj₂ to Qeq)
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
  second a p P' Q' (Ppa , pMax) noQ-p◇a f (Pfa , Qfa) = noQ-p◇a g Qgpa
       where
         f≤p = pMax f Pfa
         g = proj₁ f≤p
         f≐g◇p = proj₂ f≤p
         Qgpa : π₁ Q' (g ◇ (p ◇ a))
         Qgpa = π₂ Q' (◃ext' f≐g◇p ∘ a)  Qfa


trivial-problem : ∀ {m n t} {f : m ~> n} -> (Max⋆ ((Unifies⋆ t t) [-◇⋆ f ])) i
trivial-problem = refl , λ f' _ → f' , λ _ → refl

trivial-problemV : ∀ {m n N} {t : Vec (Term _) N} {f : m ~> n} -> (Max⋆ ((Unifies⋆V t t) [-◇⋆ f ])) i
trivial-problemV = refl , λ f' _ → f' , λ _ → refl

open import Data.Sum

var-elim : ∀ {m} (x : Fin (suc m)) (t' : Term _)
              -> π₁ (Max ((Unifies (i x) ((▹ (thin x) ◃_) t')))) (t' for x)
var-elim x t' = first , \{_} -> second
  where
    lemma : ∀{m}(x : Fin (suc m)) t → i ≐ ((t for x) ◇ (▹ (thin x)))
    lemma x t x' = sym (cong (maybe i t) (Thick.half2 x _ x' refl))
    first = begin
             (t' for x) ◃ (i x) ≡⟨ cong (maybe i t') (Thick.half1 x) ⟩
             t'                 ≡⟨ sym (Sub.fact1 t') ⟩
             i ◃ t'             ≡⟨ ◃ext' (lemma x t') t' ⟩
             (t' for x) ◃ ((▹ (thin x) ◃_) t') ∎

    second : ∀ {n} (f : _ ~> n) → f x ≡ f ◃ ((▹ (thin x) ◃_) t') → f ≤ (t' for x)
    second f Unifiesf = (f ∘ thin x) , third
        where
          third : ((x' : Fin _) →  f x' ≡ (f ∘ thin x) ◃ (maybe′ i t' (thick? x x')))
          third x' with thick? x x' | Thick.fact1 x x' (thick? x x') refl
          third .x | .nothing | inj₁ (refl , refl)  =
                                       sym (begin
                                           (f ∘ thin x) ◃ t'  ≡⟨ cong (λ g -> (g ◃_) t') (sym (Sub.fact3 f (thin x))) ⟩
                                           (f ◇ (▹ (thin x))) ◃ t' ≡⟨ Sub.fact2 {-f (▹ (thin x))-} t' ⟩
                                           f ◃ ((▹ (thin x) ◃_) t') ≡⟨ sym Unifiesf ⟩
                                           f x ∎)
          third x' | .(just y) | inj₂ (y , ( thinxy≡x' , refl))  = sym (cong f thinxy≡x')

var-elim-i : ∀ {m} (x : Fin (suc m)) (t' : Term _)
              -> π₁ (Max ((Unifies (i x) ((▹ (thin x) ◃_) t')))) (i ◇ (t' for x))
var-elim-i {m} x t = prop-id {_} {_} {t for x} {Max (Unifies (i x) ((▹ (thin x) ◃_) t))} (var-elim {m} x t)

var-elim-i-≡ : ∀ {m} {t'} (x : Fin (suc m)) t1  -> t1 ≡ (i ∘ thin x) ◃ t' -> π₁ (Max (Unifies (i x) t1)) (i ◇ (t' for x))
var-elim-i-≡ {_} {t'} x .((i ∘ thin x) ◃ t') refl = var-elim-i x t'

◇-assoc : ∀ {l m n o} (f : l ~> m) (g : n ~> _) (h : o ~> _) ->
               (f ◇ (g ◇ h)) ≐ ((f ◇ g) ◇ h)
◇-assoc f g h x = sym (Sub.fact2 (h x))

bind-assoc : ∀ {l m n o} (f : l ~> m) (g : n ~> _) (h : o ~> _) t -> (f ◇ g) ◃ (h ◃ t) ≡ (f ◇ (g ◇ h)) ◃ t
bind-assoc f g h t = sym (begin
           (f ◇ (g ◇ h)) ◃ t  ≡⟨ ◃ext (◇-assoc f g h) t ⟩
           ((f ◇ g) ◇ h) ◃ t  ≡⟨ Sub.fact2 ⦃ SubstitutionTerm ⦄ ⦃ Sub.Fact2Term ⦄ {f = (f ◇ g)} {g = h} {-(f ◇ g) h-} t ⟩
           (f ◇ g) ◃ (h  ◃ t)
                              ∎)
