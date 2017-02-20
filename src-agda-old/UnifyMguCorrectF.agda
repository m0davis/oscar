open import Relation.Binary using (IsDecEquivalence)
open import Agda.Builtin.Equality

module UnifyMguCorrectF (FunctionName : Set) ⦃ isDecEquivalenceA : IsDecEquivalence (_≡_ {A = FunctionName}) ⦄ where

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

open import UnifyTermF FunctionName
open import UnifyMguF FunctionName

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

record Σ₁ (A : Set1) (F : A -> Set) : Set1 where
  field
    π₁ : A
    π₂ : F π₁

_,,_ : ∀ {A F} (x : A) -> F x -> Σ₁ A F
x ,, b = record{ π₁ = x; π₂ = b }

open Σ₁ public

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

UnifiesV : ∀ {m} {N} (s t : Vec (Term m) N) -> Property m
UnifiesV s t = (λ {_} -> Unifies⋆V s t) ,, λ {_} {f} {g} f≐g f◃s=f◃t ->
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
          third : ((x' : Fin _) →  f x' ≡ (f ∘ thin x) ◃ (maybe′ i t' (thick x x')))
          third x' with thick x x' | Thick.fact1 x x' (thick x x') refl
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

data Step (n : ℕ) : Set where
  left : Term n -> Step n
  right : Term n -> Step n
  function : FunctionName → ∀ {L} → Vec (Term n) L → ∀ {R} → Vec (Term n) R → Step n

fmapS : ∀ {n m} (f : Term n -> Term m) (s : Step n) -> Step m
fmapS f (left x) = left (f x)
fmapS f (right x) = right (f x)
fmapS f (function fn ls rs) = function fn (mapV f ls) (mapV f rs)

_⊹_ : ∀ {n} (ps : List (Step n)) (t : Term n) -> Term n
[] ⊹ t             = t
(left r ∷ ps) ⊹ t  = (ps ⊹ t) fork r
(right l ∷ ps) ⊹ t = l fork (ps ⊹ t)
(function fn ls rs ∷ ps) ⊹ t = function fn (ls ++V (ps ⊹ t) ∷ rs)

data Fixpoint⊹ {n} : List (Step n) → Term n → Set where
  [] : ∀ t → Fixpoint⊹ [] t
  left : ∀ t r ps → Fixpoint⊹ (left r ∷ ps) ((ps ⊹ t) fork r)
  right : ∀ t l ps → Fixpoint⊹ (right l ∷ ps) (l fork (ps ⊹ t))
  function : ∀ t fn L (ls : Vec (Term _) L) R (rs : Vec (Term _) R) ps → Fixpoint⊹ (function fn ls rs ∷ ps) (function fn (ls ++V (ps ⊹ t) ∷ rs))

fixpoint⊹ : ∀{m} (t : Term m) ps (eq : t ≡ ps ⊹ t) → Fixpoint⊹ ps t
fixpoint⊹ t [] eq = [] _
fixpoint⊹ (i x) (left r ∷ ps) ()
fixpoint⊹ leaf (left r ∷ ps) ()
fixpoint⊹ (l fork r) (left _ ∷ ps) eq rewrite Term-fork-inj-left eq | Term-fork-inj-right eq = left _ _ _
fixpoint⊹ (function x x₁) (left r ∷ ps) ()
fixpoint⊹ (i x) (right l ∷ ps) ()
fixpoint⊹ leaf (right l ∷ ps) ()
fixpoint⊹ (t fork t₁) (right l ∷ ps) eq rewrite Term-fork-inj-left eq | Term-fork-inj-right eq = right _ _ _
fixpoint⊹ (function x x₁) (right l ∷ ps) ()
fixpoint⊹ (i x) (function fn ls rs ∷ ps) ()
fixpoint⊹ leaf (function fn ls rs ∷ ps) ()
fixpoint⊹ (t fork t₁) (function fn ls rs ∷ ps) ()
fixpoint⊹ (function fn' ts) (function fn ls rs ∷ ps) eq with Term-function-inj-VecSize eq
… | refl with Term-function-inj-Vector eq
… | veq rewrite Term-function-inj-FunctionName eq | veq = function _ _ _ _ _ _ _

fork++ : ∀ {m} {s t : Term m} ps ->
              (ps ⊹ (s fork t) ≡ (ps ++L [ left t ]) ⊹ s)
              × (ps ⊹ (s fork t) ≡ (ps ++L [ right s ]) ⊹ t)
fork++ [] = refl , refl
fork++ (left y' ∷ xs') = (cong (λ a -> a fork y') *** cong (λ a -> a fork y')) (fork++ xs')
fork++ (right y' ∷ xs') = (cong (λ a -> y' fork a) *** cong (λ a -> y' fork a)) (fork++ xs')
fork++ {s = s} {t} (function fn ls rs ∷ xs') =
  (cong (λ a → function fn (ls ++V a ∷ rs)) *** cong (λ a → function fn (ls ++V a ∷ rs))) (fork++ xs')

function++ : ∀ {m} {fn} {t : Term m} {L} {ls : Vec (Term m) L} {R} {rs : Vec (Term m) R} ps →
               ps ⊹ (function fn (ls ++V t ∷ rs)) ≡ (ps ++L [ function fn ls rs ]) ⊹ t
function++ [] = refl
function++ (left x ∷ ps) = cong (_fork x) (function++ ps)
function++ (right x ∷ ps) = cong (x fork_) (function++ ps)
function++ (function fn ls rs ∷ ps) = cong (λ a → function fn (ls ++V a ∷ rs)) (function++ ps)

{-
inj-⊹ : ∀ {m} ps (t₁ t₂ : Term m) → ps ⊹ t₁ ≡ ps ⊹ t₂ → t₁ ≡ t₂
inj-⊹ [] t₁ t₂ eq = eq
inj-⊹ (left r ∷ ps) t₁ t₂ eq = inj-⊹ ps t₁ t₂ (Term-fork-inj-left eq)
inj-⊹ (right l ∷ ps) t₁ t₂ eq = inj-⊹ ps t₁ t₂ (Term-fork-inj-right eq)
inj-⊹ (function fn ls rs ∷ ps) t₁ t₂ eq = inj-⊹ ps t₁ t₂ {!Term-function-inj-Vector eq!}

mutual

  sizeOfTerm : ∀{m} (t : Term m) → ℕ
  sizeOfTerm (i x) = 1
  sizeOfTerm leaf = 1
  sizeOfTerm (l fork r) = suc (sizeOfTerm l) + suc (sizeOfTerm r)
  sizeOfTerm (function fn ts) = suc (sizeOfTerms ts)

  sizeOfTerms : ∀{m N} (t : Vec (Term m) N) → ℕ
  sizeOfTerms [] = 0
  sizeOfTerms (t ∷ ts) = sizeOfTerm t + sizeOfTerms ts

growingSize : ∀ {m} (st : (Term m)) → (sp : Step m) (sps : List (Step m)) → sizeOfTerm ((sp ∷ sps) ⊹ st) > sizeOfTerm st
growingSize st (left r) [] = auto -- auto
growingSize st (right l) [] = auto -- auto
growingSize {m} st (function fn ls rs) [] = {!map-++-commute sizeOfTerm ls {ys = st ∷ rs}!} -- rewrite to-≡ (map-++-commute proj₁ ls {ys = st ∷ rs}) | Data.Vec.Properties.sum-++-commute (mapV proj₁ ls) {ys = mapV proj₁ (st ∷ rs)} = auto
growingSize st (left x) (p₂ ∷ ps) = by (growingSize st p₂ ps)
growingSize st (right x) (p₂ ∷ ps) = by (growingSize st p₂ ps)
growingSize st (function fn ls rs) (p₂ ∷ ps) = {!!} -- rewrite to-≡ (map-++-commute proj₁ ls {ys = ((p₂ ∷ ps) Sized⊹ st) ∷ rs}) | Data.Vec.Properties.sum-++-commute (mapV proj₁ ls) {ys = mapV proj₁ (((p₂ ∷ ps) Sized⊹ st) ∷ rs)} = by (growingSize st p₂ ps)



No-Cycle' : ∀{m} (t : Term m) ps -> (eq : t ≡ ps ⊹ t) → ps ≡ []
No-Cycle' t [] eq = refl
No-Cycle' (i x) (left r ∷ ps) ()
No-Cycle' leaf (left r ∷ ps) ()
No-Cycle' (l fork r) (left l' ∷ ps) eq with Term-fork-inj-left eq | sym (Term-fork-inj-right eq)
… | leq | refl = {!cong sizeOfTerm (trans leq (proj₁ (fork++ ps)))!}
No-Cycle' (function x x₁) (left r ∷ ps) ()
No-Cycle' t (right l ∷ ps) eq = {!!}
No-Cycle' t (function fn ls rs ∷ ps) eq = {!!}
-}

_◃S_ : ∀ {n m} (f : n ~> m) -> List (Step n) -> List (Step m)
_◃S_ f = Data.List.map (fmapS (f ◃_))

map-[] : ∀ {n m} (f : n ~> m) ps -> f ◃S ps ≡ [] -> ps ≡ []
map-[] f [] _ = refl
map-[] f (x ∷ xs) ()

module StepM where

  lemma1 : ∀ {n} (x : Step n) xs t -> [ x ] ⊹ ( xs ⊹ t ) ≡ (x ∷ xs) ⊹ t
  lemma1 (left y) xs t = refl
  lemma1 (right y) xs t = refl
  lemma1 (function fn ls rs) xs t = refl

  lemma2 : ∀ {n} {r} {t} {xs} (x : Step n) -> xs ⊹ t ≡ r -> ((x ∷ xs) ⊹ t ) ≡ [ x ] ⊹ r
  lemma2 (left y) eq = cong (λ t -> t fork y) eq
  lemma2 (right y) eq = cong (λ t -> y fork t) eq
  lemma2 (function fn ls rs) eq = cong (λ t → function fn (ls ++V t ∷ rs)) eq

  fact1 : ∀ {n} ps qs (t : Term n) -> (ps ++L qs) ⊹ t ≡ ps ⊹ (qs ⊹ t)
  fact1 [] qs t = refl
  fact1 (p ∷ ps) qs t = begin (p ∷ (ps ++L qs)) ⊹ t ≡⟨ lemma2 p (fact1 ps qs t) ⟩
                              [ p ] ⊹ (ps ⊹ (qs ⊹ t)) ≡⟨ lemma1 p ps (qs ⊹ t)  ⟩
                              (p ∷ ps) ⊹ (qs ⊹ t) ∎

  ◃-fact1 : ∀ {m n} (f : m ~> n) {N} (rs : Vec (Term m) N) → f ◃ rs ≡ mapV (f ◃_) rs
  ◃-fact1 f [] = refl
  ◃-fact1 f (x ∷ rs) rewrite ◃-fact1 f rs = refl

  ◃-fact2 : ∀ {m n} (f : m ~> n) {L} (ls : Vec (Term m) L) {R} (rs : Vec (Term m) R) → f ◃ (ls ++V rs) ≡ (f ◃ ls) ++V (f ◃ rs)
  ◃-fact2 f [] rs = refl
  ◃-fact2 f (l ∷ ls) rs = cong ((f ◃ l) ∷_) (◃-fact2 f ls rs)


  fact2 : ∀ {m n} (f : m ~> n) t ps ->
               f ◃ (ps ⊹ t) ≡ (f ◃S ps) ⊹ (f ◃ t)
  fact2 f t [] = refl
  fact2 f t (left y ∷ xs) = cong (λ t -> t fork (f ◃ y)) (fact2 f t xs)
  fact2 f t (right y ∷ xs) = cong (λ t -> (f ◃ y) fork t) (fact2 f t xs)
  fact2 f t (function fn ls rs ∷ xs) rewrite sym (◃-fact1 f ls) | sym (◃-fact1 f rs) = cong (function fn) (trans (◃-fact2 f ls ((xs ⊹ t) ∷ rs)) (cong ((f ◃ ls) ++V_) (cong (_∷ (f ◃ rs)) (fact2 f t xs))))

open IsDecEquivalence isDecEquivalenceA using () renaming (_≟_ to _≟F_) public
import Relation.Binary.HeterogeneousEquality as H

unMaybe : ∀ {A : Set} {x y : A} {B : Set} {m : Maybe B} → maybe (λ _ → x) y m ≡ y → x ≢ y → m ≡ nothing
unMaybe {m = just x₁} x₂ x₃ = ⊥-elim (x₃ x₂)
unMaybe {m = nothing} x₁ x₂ = refl

unMaybe' : ∀ {A : Set} {y : A} {B : Set} {x : B → A} {m : Maybe B} → maybe (λ b → x b) y m ≡ y → (∀ b → x b ≢ y) → m ≡ nothing
unMaybe' {m = just x₁} x₂ x₃ = ⊥-elim (x₃ x₁ x₂)
unMaybe' {m = nothing} x₁ x₂ = refl

just≢nothing : ∀ {A B : Set} → (x : B → A) → ∀ b → Maybe.just (x b) ≢ nothing
just≢nothing x b ()

unMaybeJust' : ∀ {A B : Set} {P : B → A} {m : Maybe B} {n : A} {x : B} → maybe (λ b → P b) n m ≡ P x → (∀ b → P b ≢ n) → (∀ {y y'} → P y ≡ P y' → y ≡ y') → m ≡ just x
unMaybeJust' {m = just x} x₂ x₃ inj rewrite inj x₂ = refl
unMaybeJust' {m = nothing} x₁ x₂ _ = ⊥-elim (x₂ _ (sym x₁))

mutual

  check-props : ∀ {m} (x : Fin (suc m)) {N} (ts : Vec (Term (suc m)) N) fn ->
                 (∃ λ (ts' : Vec (Term m) N) -> ts ≡ ▹ (thin x) ◃ ts' × check x ts ≡ just ts')
                 ⊎ (∃ λ ps -> function fn ts ≡ (ps ⊹ i x) × check x ts ≡ nothing)
  check-props x [] fn = inj₁ ([] , refl , refl)
  check-props x (t ∷ ts) fn with check-prop x t
  … | inj₂ (ps , t=ps+ix , checkxt=no) rewrite t=ps+ix | checkxt=no = inj₂ (function fn [] ts ∷ ps , refl , refl)
  … | inj₁ (t' , t=thinxt' , checkxt=t') rewrite checkxt=t' with check-props x ts fn
  … | inj₁ (ts' , ts=thinxts' , checkxts=ts') rewrite t=thinxt' | ts=thinxts' | checkxts=ts' = inj₁ (_ , refl , refl)
  … | inj₂ ([] , () , checkxts=no)
  … | inj₂ (left _ ∷ ps , () , checkxts=no)
  … | inj₂ (right _ ∷ ps , () , checkxts=no)
  … | inj₂ (function fn' ls rs ∷ ps , ts=ps+ix , checkxts=no) with Term-function-inj-VecSize ts=ps+ix
  … | refl with Term-function-inj-Vector ts=ps+ix
  … | refl rewrite checkxts=no = inj₂ (function fn (t ∷ ls) rs ∷ ps , refl , refl)

  check-prop : ∀ {m} (x : Fin (suc m)) t ->
                (∃ λ t' -> t ≡ ▹ (thin x) ◃ t' × check x t ≡ just t')
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
  check-prop x (function fn ts) with check-props x ts fn
  … | inj₁ (t' , t=thinxt' , checkxt=t') rewrite checkxt=t' = inj₁ (function fn t' , cong (function fn) t=thinxt' , refl)
  … | inj₂ (ps , t=ps+ix , checkxt=no) rewrite checkxt=no = inj₂ (ps , t=ps+ix , refl)

data SizedTerm (n : ℕ) : ℕ → Set where
  i : (x : Fin n) -> SizedTerm n (suc zero)
  leaf : SizedTerm n (suc zero)
  _fork_ : (s : ∃ (SizedTerm n)) (t : ∃ (SizedTerm n)) -> SizedTerm n (suc (proj₁ s + proj₁ t))
  function : FunctionName → ∀ {f} → (ts : Vec (∃ (SizedTerm n)) f) → SizedTerm n (suc (Data.Vec.sum (Data.Vec.map proj₁ ts)))

data SizedStep (n : ℕ) : Set where
  left : ∃ (SizedTerm n) -> SizedStep n
  right : ∃ (SizedTerm n) -> SizedStep n
  function : FunctionName → ∀ {L} → Vec (∃ (SizedTerm n)) L → ∀ {R} → Vec (∃ (SizedTerm n)) R → SizedStep n

mutual

  toSizedTerm : ∀ {n} → Term n → ∃ (SizedTerm n)
  toSizedTerm (i x) = suc zero , i x
  toSizedTerm leaf = suc zero , leaf
  toSizedTerm (l fork r) with toSizedTerm l | toSizedTerm r
  … | L , sl | R , sr = (suc (L + R)) , ((L , sl) fork (R , sr))
  toSizedTerm (function fn ts) with toSizedTerms ts
  … | sts = suc (Data.Vec.sum (Data.Vec.map proj₁ sts)) , SizedTerm.function fn sts

  fromSizedTerm : ∀ {n} → ∃ (SizedTerm n) → Term n
  fromSizedTerm (_ , i x) = i x
  fromSizedTerm (_ , leaf) = leaf
  fromSizedTerm (_ , (_fork_ t₁ t₂)) = (fromSizedTerm t₁ fork fromSizedTerm t₂)
  fromSizedTerm (_ , function fn ts) = function fn (fromSizedTerms ts)

  toSizedTerms : ∀ {n N} → Vec (Term n) N → Vec (∃ (SizedTerm n)) N
  toSizedTerms [] = []
  toSizedTerms (t ∷ ts) = toSizedTerm t ∷ toSizedTerms ts

  fromSizedTerms : ∀ {n N} → Vec (∃ (SizedTerm n)) N → Vec (Term n) N
  fromSizedTerms [] = []
  fromSizedTerms (t ∷ ts) = fromSizedTerm t ∷ fromSizedTerms ts

mutual

  isoSizedTerm : ∀ {n} → (st : ∃ (SizedTerm n)) → st ≡ toSizedTerm (fromSizedTerm st)
  isoSizedTerm (._ , i x) = refl
  isoSizedTerm (._ , leaf) = refl
  isoSizedTerm (.(suc (proj₁ s + proj₁ t)) , (s fork t)) rewrite sym (isoSizedTerm s) | sym (isoSizedTerm t) = refl
  isoSizedTerm (._ , function x ts) rewrite sym (isoSizedTerms ts) = refl

  isoSizedTerms : ∀ {n N} → (st : Vec (∃ (SizedTerm n)) N) → st ≡ toSizedTerms (fromSizedTerms st)
  isoSizedTerms [] = refl
  isoSizedTerms (t ∷ ts) rewrite sym (isoSizedTerm t) | sym (isoSizedTerms ts) = refl

mutual

  isoTerm : ∀ {n} → (t : Term n) → t ≡ fromSizedTerm (toSizedTerm t)
  isoTerm (i x) = refl
  isoTerm leaf = refl
  isoTerm (s fork t) rewrite sym (isoTerm s) | sym (isoTerm t) = refl
  isoTerm (function fn ts) rewrite sym (isoTerms ts) = refl

  isoTerms : ∀ {n N} → (t : Vec (Term n) N) → t ≡ fromSizedTerms (toSizedTerms t)
  isoTerms [] = refl
  isoTerms (t ∷ ts) rewrite sym (isoTerm t) | sym (isoTerms ts) = refl

toSizedStep : ∀ {n} → Step n → SizedStep n
toSizedStep (left r) = left (toSizedTerm r)
toSizedStep (right l) = right (toSizedTerm l)
toSizedStep (function fn ls rs) = function fn (toSizedTerms ls) (toSizedTerms rs)

fromSizedStep : ∀ {n} → SizedStep n → Step n
fromSizedStep (left r) = left (fromSizedTerm r)
fromSizedStep (right l) = right (fromSizedTerm l)
fromSizedStep (function fn ls rs) = function fn (fromSizedTerms ls) (fromSizedTerms rs)

isoSizedStep : ∀ {n} → (ss : SizedStep n) → ss ≡ toSizedStep (fromSizedStep ss)
isoSizedStep (left r) rewrite sym (isoSizedTerm r) = refl
isoSizedStep (right l) rewrite sym (isoSizedTerm l) = refl
isoSizedStep (function fn ls rs) rewrite sym (isoSizedTerms ls) | sym (isoSizedTerms rs) = refl

isoStep : ∀ {n} → (s : Step n) → s ≡ fromSizedStep (toSizedStep s)
isoStep (left r) rewrite sym (isoTerm r) = refl
isoStep (right l) rewrite sym (isoTerm l) = refl
isoStep (function fn ls rs) rewrite sym (isoTerms ls) | sym (isoTerms rs) = refl

toSizedSteps : ∀ {n} → List (Step n) → List (SizedStep n)
toSizedSteps [] = []
toSizedSteps (s ∷ ss) = toSizedStep s ∷ toSizedSteps ss

fromSizedSteps : ∀ {n} → List (SizedStep n) → List (Step n)
fromSizedSteps [] = []
fromSizedSteps (s ∷ ss) = fromSizedStep s ∷ fromSizedSteps ss

isoSizedSteps : ∀ {n} → (ss : List (SizedStep n)) → ss ≡ toSizedSteps (fromSizedSteps ss)
isoSizedSteps [] = refl
isoSizedSteps (s ∷ ss) rewrite sym (isoSizedStep s) | sym (isoSizedSteps ss) = refl

isoSteps : ∀ {n} → (s : List (Step n)) → s ≡ fromSizedSteps (toSizedSteps s)
isoSteps [] = refl
isoSteps (s ∷ ss) rewrite sym (isoStep s) | sym (isoSteps ss) = refl

_Sized⊹_ : ∀ {n} (ps : List (SizedStep n)) (t : ∃ (SizedTerm n)) -> ∃ (SizedTerm n)
[] Sized⊹ t = t
(left r ∷ ps) Sized⊹ t = _ , (ps Sized⊹ t) SizedTerm.fork r
(right l ∷ ps) Sized⊹ t = _ , l SizedTerm.fork (ps Sized⊹ t)
(function fn ls rs ∷ ps) Sized⊹ t = _ , function fn (ls ++V (ps Sized⊹ t) ∷ rs)

fromSizedTerms-commute : ∀ {n} {L R} → (ls : Vec (∃ (SizedTerm n)) L) (rs : Vec (∃ (SizedTerm n)) R) → fromSizedTerms (ls ++V rs) ≡ fromSizedTerms ls ++V fromSizedTerms rs
fromSizedTerms-commute [] rs = refl
fromSizedTerms-commute (l ∷ ls) rs rewrite fromSizedTerms-commute ls rs = refl

toSizedTerms-commute : ∀ {n} {L R} → (ls : Vec (Term n) L) (rs : Vec (Term n) R) → toSizedTerms (ls ++V rs) ≡ toSizedTerms ls ++V toSizedTerms rs
toSizedTerms-commute [] rs = refl
toSizedTerms-commute (l ∷ ls) rs rewrite toSizedTerms-commute ls rs = refl

isoSized⊹ : ∀ {n} (ps : List (SizedStep n)) (t : ∃ (SizedTerm n)) → fromSizedTerm (ps Sized⊹ t) ≡ fromSizedSteps ps ⊹ fromSizedTerm t
isoSized⊹ [] t = refl
isoSized⊹ (left r ∷ ps) t rewrite isoSized⊹ ps t = refl
isoSized⊹ (right l ∷ ps) t rewrite isoSized⊹ ps t = refl
isoSized⊹ (function fn ls rs ∷ ps) t rewrite sym (isoSized⊹ ps t) | fromSizedTerms-commute ls ((ps Sized⊹ t) ∷ rs) = refl

iso⊹ : ∀ {n} (ps : List (Step n)) (t : Term n) → toSizedTerm (ps ⊹ t) ≡ toSizedSteps ps Sized⊹ toSizedTerm t
iso⊹ [] t = refl
iso⊹ (left r ∷ ps) t rewrite iso⊹ ps t = refl
iso⊹ (right l ∷ ps) t rewrite iso⊹ ps t = refl
iso⊹ (function fn ls rs ∷ ps) t rewrite sym (iso⊹ ps t) | toSizedTerms-commute ls ((ps ⊹ t) ∷ rs) = refl

import Data.Vec.Properties
import Relation.Binary.PropositionalEquality as PE
open Data.Vec.Properties.UsingVectorEquality (PE.setoid ℕ)
import Data.Vec.Equality
open Data.Vec.Equality.PropositionalEquality using (to-≡)

growingSize : ∀ {m} (st : ∃ (SizedTerm m)) → (sp : SizedStep m) (sps : List (SizedStep m)) → proj₁ ((sp ∷ sps) Sized⊹ st) > proj₁ st
growingSize st (left r) [] = auto
growingSize st (right l) [] = auto
growingSize {m} st (function fn ls rs) [] rewrite to-≡ (map-++-commute proj₁ ls {ys = st ∷ rs}) | Data.Vec.Properties.sum-++-commute (mapV proj₁ ls) {ys = mapV proj₁ (st ∷ rs)} = auto
growingSize st (left x) (p₂ ∷ ps) = by (growingSize st p₂ ps)
growingSize st (right x) (p₂ ∷ ps) = by (growingSize st p₂ ps)
growingSize st (function fn ls rs) (p₂ ∷ ps) rewrite to-≡ (map-++-commute proj₁ ls {ys = ((p₂ ∷ ps) Sized⊹ st) ∷ rs}) | Data.Vec.Properties.sum-++-commute (mapV proj₁ ls) {ys = mapV proj₁ (((p₂ ∷ ps) Sized⊹ st) ∷ rs)} = by (growingSize st p₂ ps)

No-Cycle : ∀{m} (t : Term m) ps -> (eq : t ≡ ps ⊹ t) → ps ≡ []
No-Cycle t [] eq = refl
No-Cycle t (p ∷ ps) eq = refute (subst (λ v → v > proj₁ (toSizedTerm t)) (sym (trans same iso)) growth) where
  same : proj₁ (toSizedTerm t) ≡ proj₁ (toSizedTerm ((p ∷ ps) ⊹ t))
  growth : proj₁ ((toSizedStep p ∷ toSizedSteps ps) Sized⊹ toSizedTerm t) > proj₁ (toSizedTerm t)
  iso : proj₁ (toSizedTerm ((p ∷ ps) ⊹ t)) ≡ proj₁ ((toSizedStep p ∷ toSizedSteps ps) Sized⊹ toSizedTerm t)
  growth = growingSize (toSizedTerm t) (toSizedStep p) (toSizedSteps ps)
  same = cong (proj₁ ∘ toSizedTerm) eq
  iso = cong proj₁ (iso⊹ (p ∷ ps) t)

module Step2 where
  fact : ∀{m} (x : Fin m) p ps -> Nothing (Unifies (i x) ((p ∷ ps) ⊹ i x))
  fact x p ps f r with No-Cycle (f x) (f ◃S (p ∷ ps)) (trans r (StepM.fact2 f (i x) (p ∷ ps)))
  ... | ()


◇-assoc : ∀ {l m n o} (f : l ~> m) (g : n ~> _) (h : o ~> _) ->
               (f ◇ (g ◇ h)) ≐ ((f ◇ g) ◇ h)
◇-assoc f g h x = sym (Sub.fact2 (h x))

bind-assoc : ∀ {l m n o} (f : l ~> m) (g : n ~> _) (h : o ~> _) t -> (f ◇ g) ◃ (h ◃ t) ≡ (f ◇ (g ◇ h)) ◃ t
bind-assoc f g h t = sym (begin
           (f ◇ (g ◇ h)) ◃ t  ≡⟨ ◃ext (◇-assoc f g h) t ⟩
           ((f ◇ g) ◇ h) ◃ t  ≡⟨ Sub.fact2 ⦃ SubstitutionTerm ⦄ ⦃ Sub.Fact2Term ⦄ {f = (f ◇ g)} {g = h} {-(f ◇ g) h-} t ⟩
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

mutual

  -- We use a view so that we need to handle fewer cases in the main proof
  data AmguT : {m : ℕ} -> (s t : Term m) -> ∃ (AList m) -> Maybe (∃ (AList m)) -> Set where
    Flip : ∀ {m s t acc} -> amgu t s acc ≡ amgu s t acc ->
      AmguT {m} t s acc (amgu t s acc) -> AmguT         s            t            acc        (amgu s t acc)
    leaf-leaf : ∀ {m acc} ->             AmguT {m}     leaf         leaf         acc        (just acc)
    fn-name   : ∀ {m fn₁ fn₂ N₁ N₂ acc} {ts₁ : Vec (Term m) N₁} {ts₂ : Vec (Term m) N₂} →
                  fn₁ ≢ fn₂ →
                                         AmguT {m}     (function fn₁ ts₁)
                                                                   (function fn₂ ts₂)
                                                                                acc        nothing
    fn-size   : ∀ {m fn₁ fn₂ N₁ N₂ acc} {ts₁ : Vec (Term m) N₁} {ts₂ : Vec (Term m) N₂} →
                  N₁ ≢ N₂ →
                                         AmguT {m}     (function fn₁ ts₁)
                                                                   (function fn₂ ts₂)
                                                                                 acc        nothing
    fn-fn     : ∀ {m fn N acc} {ts₁ ts₂ : Vec (Term m) N} →
                                         AmguT {m}     (function fn ts₁)
                                                                   (function fn ts₂)
                                                                                acc        (amgu ts₁ ts₂ acc)
    leaf-fork : ∀ {m s t acc} ->         AmguT {m}     leaf         (s fork t)   acc        nothing
    leaf-fn   : ∀ {m fn N} {ts : Vec (Term _) N} {acc} ->       AmguT {m}     leaf         (function fn ts)   acc        nothing
    fork-fn   : ∀ {m s t fn N} {ts : Vec (Term _) N} {acc} ->   AmguT {m}     (s fork t)   (function fn ts)   acc        nothing
    fork-fork : ∀ {m s1 s2 t1 t2 acc} -> AmguT {m}     (s1 fork s2) (t1 fork t2) acc        (amgu s2 t2 =<< amgu s1 t1 acc)
    var-var   : ∀ {m x y} ->             AmguT         (i x)        (i y)        (m , anil) (just (flexFlex x y))
    var-t : ∀ {m x t} -> i x ≢ t ->      AmguT         (i x)        t            (m , anil) (flexRigid x t)
    s-t : ∀{m s t n σ r z} ->            AmguT {suc m} s            t            (n , σ asnoc r / z) ((λ σ -> σ ∃asnoc r / z) <$>
                                                                                                       amgu ((r for z) ◃ s) ((r for z) ◃ t) (n , σ))


  data AmguTV : {m : ℕ} -> ∀ {N} (ss ts : Vec (Term m) N) -> ∃ (AList m) -> Maybe (∃ (AList m)) -> Set where
    fn0-fn0   : ∀ {m acc} →
                                         AmguTV {m}     ([])
                                                                   ([])
                                                                                acc        (just acc)

    fns-fns   : ∀ {m N acc} {t₁ t₂ : Term m} {ts₁ ts₂ : Vec (Term m) N} →
                                         AmguTV {m}     ((t₁ ∷ ts₁))
                                                                   ((t₂ ∷ ts₂))
                                                                                acc        (amgu ts₁ ts₂ =<< amgu t₁ t₂ acc)

view : ∀ {m : ℕ} -> (s t : Term m) -> (acc : ∃ (AList m)) -> AmguT s t acc (amgu s t acc)
view leaf         leaf         acc        = leaf-leaf
view leaf         (s fork t)   acc        = leaf-fork
view (s fork t)   leaf         acc        = Flip refl leaf-fork
view (s1 fork s2) (t1 fork t2) acc        = fork-fork
view (function fn₁ {n₁} ts₁) (function fn₂ {n₂} ts₂) acc  with
 fn₁ ≟F fn₂
… | no neq = fn-name neq
… | yes refl with n₁ ≟ n₂
… | yes refl = fn-fn
… | no neq = fn-size neq
view leaf         (function fn ts) acc    = leaf-fn
view (function fn ts) leaf         acc    = Flip refl leaf-fn
view (function fn ts) (_ fork _)   acc    = Flip refl fork-fn
view (s fork t)   (function fn ts) acc    = fork-fn
view (i x)        (i y)        (m , anil) = var-var
view (i x)        leaf         (m , anil) = var-t (λ ())
view (i x)        (s fork t)   (m , anil) = var-t (λ ())
view (i x)        (function fn ts)   (m , anil) = var-t (λ ())
view leaf         (i x)        (m , anil) = Flip refl (var-t (λ ()))
view (s fork t)   (i x)        (m , anil) = Flip refl (var-t (λ ()))
view (function fn ts) (i x)    (m , anil) = Flip refl (var-t (λ ()))
view (i x)        (i x')       (n , σ asnoc r / z) = s-t
view (i x)        leaf         (n , σ asnoc r / z) = s-t
view (i x)        (s fork t)   (n , σ asnoc r / z) = s-t
view leaf         (i x)        (n , σ asnoc r / z) = s-t
view (s fork t)   (i x)        (n , σ asnoc r / z) = s-t
view (function fn ts)   (i x)        (n , σ asnoc r / z) = s-t
view (i x) (function fn ts)          (n , σ asnoc r / z) = s-t

viewV : ∀ {m : ℕ} {N} -> (ss ts : Vec (Term m) N) -> (acc : ∃ (AList m)) -> AmguTV ss ts acc (amgu ss ts acc)
viewV []         []         acc        = fn0-fn0
viewV (t ∷ ts₁) (t₂ ∷ ts₂) acc         = fns-fns

amgu-Correctness : {m : ℕ} -> (s t : Term m) -> ∃ (AList m) -> Set
amgu-Correctness s t (l , ρ) =
    (∃ λ n → ∃ λ σ → π₁ (Max (Unifies s t [-◇ sub ρ ])) (sub σ) × amgu s t (l , ρ) ≡ just (n , σ ++ ρ ))
  ⊎ (Nothing ((Unifies s t) [-◇ sub ρ ]) ×  amgu s t (l , ρ) ≡ nothing)

amgu-Correctness⋆ : {m : ℕ} -> (s t : Term m) -> ∃ (AList m) -> Set
amgu-Correctness⋆ s t (l , ρ) =
    (∃ λ n → ∃ λ σ → π₁ (Max (Unifies s t [-◇ sub ρ ])) (sub σ) × amgu s t (l , ρ) ≡ just (n , σ ++ ρ ))
  ⊎ (Nothing ((Unifies s t) [-◇ sub ρ ]) ×  amgu s t (l , ρ) ≡ nothing)

amgu-Ccomm : ∀ {m} s t acc -> amgu {m = m} s t acc ≡ amgu t s acc -> amgu-Correctness s t acc -> amgu-Correctness t s acc
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

amgu-Ccomm⋆ : ∀ {m} s t acc -> amgu {m = m} s t acc ≡ amgu t s acc -> amgu-Correctness⋆ s t acc -> amgu-Correctness⋆ t s acc
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

NothingForkLeft : ∀ {m l} (s1 t1 : Term m) (ρ : AList m l) (s2 t2 : Term m) →
               Nothing⋆ $ Unifies⋆ s1 t1 [-◇⋆ sub ρ ] →
               Nothing⋆ $ Unifies⋆ (s1 fork s2) (t1 fork t2) [-◇⋆ sub ρ ]
NothingForkLeft s1 t1 ρ s2 t2 nounify = No[Q◇ρ]→No[P◇ρ] No[Q◇ρ]
  where
    P = Unifies⋆ (s1 fork s2) (t1 fork t2)
    Q = (Unifies⋆ s1 t1 ∧⋆ Unifies⋆ s2 t2)
    Q⇔P : Q ⇔⋆ P
    Q⇔P = switch⋆ P Q (Properties.fact1' {_} {s1} {s2} {t1} {t2})
    No[Q◇ρ]→No[P◇ρ] : Nothing⋆ (Q [-◇⋆ sub ρ ]) -> Nothing⋆ (P [-◇⋆ sub ρ ])
    No[Q◇ρ]→No[P◇ρ] = Properties.fact2⋆ (Q [-◇⋆ sub ρ ]) (P [-◇⋆ sub ρ ]) (Properties.fact5⋆ Q P (sub ρ) Q⇔P)
    No[Q◇ρ] : Nothing⋆ (Q [-◇⋆ sub ρ ])
    No[Q◇ρ] = failure-propagation.first⋆ (sub ρ) (Unifies⋆ s1 t1) (Unifies⋆ s2 t2) nounify

NothingForkRight : ∀ {m l n} (σ : AList l n)
                  (s1 s2 : Term m)
                  (t1 t2 : Term m) →
                  (ρ : AList m l) →
                  Max⋆ (Unifies⋆ s1 t1 [-◇⋆ sub ρ ]) $ sub σ →
                  Nothing⋆ $ Unifies⋆ s2 t2 [-◇⋆ sub (σ ++ ρ) ] →
                  Nothing⋆ $ Unifies⋆ (s1 fork s2) (t1 fork t2) [-◇⋆ sub ρ ]
NothingForkRight σ s1 s2 t1 t2 ρ a nounify = No[Q◇ρ]→No[P◇ρ]⋆ No[Q◇ρ]⋆
    where
    P⋆ = Unifies⋆ (s1 fork s2) (t1 fork t2)
    Q⋆ = (Unifies⋆ s1 t1 ∧⋆ Unifies⋆ s2 t2)
    Q⇔P⋆ : Q⋆ ⇔⋆ P⋆
    Q⇔P⋆ = switch⋆ P⋆ Q⋆ (Properties.fact1'⋆ {_} {s1} {s2} {t1} {t2})
    No[Q◇ρ]→No[P◇ρ]⋆ : Nothing⋆ (Q⋆ [-◇⋆ sub ρ ]) -> Nothing⋆ (P⋆ [-◇⋆ sub ρ ])
    No[Q◇ρ]→No[P◇ρ]⋆ = Properties.fact2⋆ (Q⋆ [-◇⋆ sub ρ ]) (P⋆ [-◇⋆ sub ρ ]) (Properties.fact5⋆ Q⋆ P⋆ (sub ρ) Q⇔P⋆)
    No[Q◇ρ]⋆ : Nothing⋆ (Q⋆ [-◇⋆ sub ρ ])
    No[Q◇ρ]⋆ = failure-propagation.second⋆ (sub ρ) (sub σ) (Unifies⋆ s1 t1) (Unifies s2 t2) a
       (λ f → nounify f ∘ π₂ (Unifies s2 t2) (cong (f ◃_) ∘ sym ∘ SubList.fact1 σ ρ))

MaxFork : ∀ {m l n n1} (s1 s2 t1 t2 : Term m)
                       (ρ : AList m l) (σ : AList l n) →
                     Max⋆ (Unifies⋆ s1 t1 [-◇⋆ sub ρ ]) $ sub σ →
                     (σ1 : AList n n1) →
                     Max⋆ (Unifies⋆ s2 t2 [-◇⋆ sub (σ ++ ρ) ]) $ sub σ1 →
                     Max⋆ (Unifies⋆ (s1 fork s2) (t1 fork t2) [-◇⋆ sub ρ ]) $ sub (σ1 ++ σ)
MaxFork s1 s2 t1 t2 ρ σ a σ1 b = Max[P∧Q◇ρ][σ1++σ]
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

NothingVecHead : ∀ {m l} (t₁ t₂ : Term m) (ρ : AList m l) {N} (ts₁ ts₂ : Vec (Term m) N) →
               Nothing⋆ $ Unifies⋆ t₁ t₂ [-◇⋆ sub ρ ] →
               Nothing⋆ $ Unifies⋆V (t₁ ∷ ts₁) (t₂ ∷ ts₂) [-◇⋆ sub ρ ]
NothingVecHead t₁ t₂ ρ ts₁ ts₂ nounify = No[Q◇ρ]→No[P◇ρ] No[Q◇ρ]
  where
    P = Unifies⋆V (t₁ ∷ ts₁) (t₂ ∷ ts₂)
    Q = (Unifies⋆ t₁ t₂ ∧⋆ Unifies⋆V ts₁ ts₂)
    Q⇔P : Q ⇔⋆ P
    Q⇔P = switch⋆ P Q (Properties.fact1'V {_} {t₁} {t₂} {_} {ts₁} {ts₂})
    No[Q◇ρ]→No[P◇ρ] : Nothing⋆ (Q [-◇⋆ sub ρ ]) -> Nothing⋆ (P [-◇⋆ sub ρ ])
    No[Q◇ρ]→No[P◇ρ] = Properties.fact2⋆ (Q [-◇⋆ sub ρ ]) (P [-◇⋆ sub ρ ]) (Properties.fact5⋆ Q P (sub ρ) Q⇔P)
    No[Q◇ρ] : Nothing⋆ (Q [-◇⋆ sub ρ ])
    No[Q◇ρ] = failure-propagation.first⋆ (sub ρ) (Unifies⋆ t₁ t₂) (Unifies⋆V ts₁ ts₂) nounify

NothingVecTail : ∀ {m l n} (σ : AList l n)
                  (t₁ t₂ : Term m)
                  {N}
                  (ts₁ ts₂ : Vec (Term m) N) →
                  (ρ : AList m l) →
                  Max⋆ (Unifies⋆ t₁ t₂ [-◇⋆ sub ρ ]) $ sub σ →
                  Nothing⋆ $ Unifies⋆V ts₁ ts₂ [-◇⋆ sub (σ ++ ρ) ] →
                  Nothing⋆ $ Unifies⋆V (t₁ ∷ ts₁) (t₂ ∷ ts₂) [-◇⋆ sub ρ ]
NothingVecTail σ t₁ t₂ ts₁ ts₂ ρ a nounify = No[Q◇ρ]→No[P◇ρ]⋆ No[Q◇ρ]⋆
    where
    P⋆ = Unifies⋆V (t₁ ∷ ts₁) (t₂ ∷ ts₂)
    Q⋆ = (Unifies⋆ t₁ t₂ ∧⋆ Unifies⋆V ts₁ ts₂)
    Q⇔P⋆ : Q⋆ ⇔⋆ P⋆
    Q⇔P⋆ = switch⋆ P⋆ Q⋆ (Properties.fact1'V {_} {t₁} {t₂} {_} {ts₁} {ts₂})
--    Q⇔P⋆ = switch⋆ P⋆ Q⋆ (Properties.fact1'⋆ {_} {s1} {s2} {t1} {t2})
    No[Q◇ρ]→No[P◇ρ]⋆ : Nothing⋆ (Q⋆ [-◇⋆ sub ρ ]) -> Nothing⋆ (P⋆ [-◇⋆ sub ρ ])
    No[Q◇ρ]→No[P◇ρ]⋆ = Properties.fact2⋆ (Q⋆ [-◇⋆ sub ρ ]) (P⋆ [-◇⋆ sub ρ ]) (Properties.fact5⋆ Q⋆ P⋆ (sub ρ) Q⇔P⋆)
    No[Q◇ρ]⋆ : Nothing⋆ (Q⋆ [-◇⋆ sub ρ ])
    No[Q◇ρ]⋆ = failure-propagation.second⋆ (sub ρ) (sub σ) (Unifies⋆ t₁ t₂) (UnifiesV ts₁ ts₂) a
       (λ f → nounify f ∘ π₂ (UnifiesV ts₁ ts₂) (cong (f ◃_) ∘ sym ∘ SubList.fact1 σ ρ))

MaxVec : ∀ {m l n n1} (t₁ t₂ : Term m) {N} (ts₁ ts₂ : Vec (Term m) N)
                       (ρ : AList m l) (σ : AList l n) →
                     Max⋆ (Unifies⋆ t₁ t₂ [-◇⋆ sub ρ ]) $ sub σ →
                     (σ1 : AList n n1) →
                     Max⋆ (Unifies⋆V ts₁ ts₂ [-◇⋆ sub (σ ++ ρ) ]) $ sub σ1 →
                     Max⋆ (Unifies⋆V (t₁ ∷ ts₁) (t₂ ∷ ts₂) [-◇⋆ sub ρ ]) $ sub (σ1 ++ σ)
MaxVec t₁ t₂ ts₁ ts₂ ρ σ a σ1 b = Max[P∧Q◇ρ][σ1++σ]
    where
      P = Unifies t₁ t₂
      Q = UnifiesV ts₁ ts₂
      P∧Q = P ∧ Q
      C = UnifiesV (t₁ ∷ ts₁) (t₂ ∷ ts₂)
      Max[C◇ρ]⇔Max[P∧Q◇ρ] : Max (C [-◇ sub ρ ]) ⇔ Max (P∧Q [-◇ sub ρ ])
      Max[C◇ρ]⇔Max[P∧Q◇ρ] = Max.fact (C [-◇ sub ρ ]) (P∧Q [-◇ sub ρ ]) (Properties.fact5 C P∧Q (sub ρ)
                      (Properties.fact1'V {_} {t₁} {t₂} {_} {ts₁} {ts₂}))
      Max[Q◇σ++ρ]⇔Max[Q◇σ◇ρ] : Max (Q [-◇ sub (σ ++ ρ)]) ⇔ Max (Q [-◇ sub σ ◇ sub ρ ])
      Max[Q◇σ++ρ]⇔Max[Q◇σ◇ρ] = Max.fact (Q [-◇ sub (σ ++ ρ)]) (Q [-◇ sub σ ◇ sub ρ ]) (Properties.fact6 Q (SubList.fact1 σ ρ))
      Max[P∧Q◇ρ][σ1++σ] : π₁ (Max (C [-◇ sub ρ ])) (sub (σ1 ++ σ))
      Max[P∧Q◇ρ][σ1++σ] = π₂ (Max (C [-◇ sub ρ ])) (≐-sym (SubList.fact1 σ1 σ))
               (proj₂ (Max[C◇ρ]⇔Max[P∧Q◇ρ] (sub σ1 ◇ sub σ))
                      (optimist (sub ρ) (sub σ) (sub σ1) P Q (DClosed.fact1 t₁ t₂) a (proj₁ (Max[Q◇σ++ρ]⇔Max[Q◇σ◇ρ] (sub σ1)) b)))

NothingStep : ∀ {l} (x : Fin (suc l)) (t : Term (suc l)) →
              i x ≢ t →
              (ps : List (Step (suc l))) →
              t ≡ (ps ⊹ i x) →
              ∀ {n} (f : Fin (suc l) → Term n) → f x ≢ (f ◃ t)
NothingStep {l} x t ix≢t ps r = No-Unifier
  where
    No-Unifier : {n : ℕ} (f : Fin (suc l) → Term n) → f x ≢ f ◃ t
    No-Unifier f fx≡f◃t = ix≢t (sym (trans r (cong (λ ps -> ps ⊹ i x) ps≡[])))
          where
            ps≡[] : ps ≡ []
            ps≡[] = map-[] f ps (No-Cycle (f x) (f ◃S ps)
                  (begin f x             ≡⟨ fx≡f◃t ⟩
                         f ◃ t           ≡⟨ cong (f ◃_) r ⟩
                         f ◃ (ps ⊹ i x)  ≡⟨ StepM.fact2 f (i x) ps ⟩
                         (f ◃S ps) ⊹ f x ∎))

NothingFor→NothingComposition : ∀ {m l} (s t : Term (suc m)) (ρ : AList m l)
             (r : Term m) (z : Fin (suc m)) →
           Nothing⋆ (Unifies⋆ ((r for z) ◃ s) ((r for z) ◃ t) [-◇⋆ sub ρ ]) →
           Nothing⋆ (Unifies⋆ s t [-◇⋆ sub (ρ asnoc r / z) ])
NothingFor→NothingComposition s t ρ r z nounify = NoQ→NoP nounify
      where
        P = Unifies s t [-◇ sub (ρ asnoc r / z) ]
        Q = Unifies ((r for z) ◃ s) ((r for z) ◃ t) [-◇ sub ρ ]
        NoQ→NoP : Nothing Q → Nothing P
        NoQ→NoP = Properties.fact2 Q P (switch P Q (step-prop s t ρ r z))

MaxFor→MaxComposition : ∀ {m l n} (s t : Term (suc m)) (ρ : AList m l)
              (r : Term m) (z : Fin (suc m)) (σ : AList l n) →
            Max⋆ (Unifies⋆ ((r for z) ◃ s) ((r for z) ◃ t) [-◇⋆ sub ρ ]) $ sub σ →
            Max⋆ (Unifies⋆ s t [-◇⋆ sub (ρ asnoc r / z) ]) $ sub σ
MaxFor→MaxComposition s t ρ r z σ a = proj₂ (MaxP⇔MaxQ (sub σ)) a
      where
        P = Unifies s t [-◇ sub (ρ asnoc r / z) ]
        Q = Unifies ((r for z) ◃ s) ((r for z) ◃ t) [-◇ sub ρ ]
        MaxP⇔MaxQ : Max P ⇔ Max Q
        MaxP⇔MaxQ = Max.fact P Q (step-prop s t ρ r z)

mutual

  amguV-c : ∀ {m N} {ss ts : Vec (Term m) N} {l ρ} -> AmguTV ss ts (l , ρ) (amgu ss ts (l , ρ)) ->
              (∃ λ n → ∃ λ σ → Max⋆ (Unifies⋆V ss ts [-◇⋆ sub ρ ]) (sub σ) × amgu {m = m} ss ts (l , ρ) ≡ just (n , σ ++ ρ ))
            ⊎ (Nothing⋆ (Unifies⋆V ss ts [-◇⋆ sub ρ ])                     × amgu {m = m} ss ts (l , ρ) ≡ nothing)
  amguV-c {m} {N} {ss} {ts} {l} {ρ} amg with amgu ss ts (l , ρ)
  amguV-c {m} {0} {.[]} {.[]} {l} {ρ} fn0-fn0 | .(just (l , ρ)) = inj₁ (_ , anil , trivial-problemV {_} {_} {_} {[]} {sub ρ} , cong (just ∘ _,_ l) (sym (SubList.anil-id-l ρ)))
  amguV-c {m} {.(suc _)} {(t₁ ∷ ts₁)} {(t₂ ∷ ts₂)} {l} {ρ} fns-fns | _  with amgu t₁ t₂ (l , ρ)  | amgu-c $ view t₁ t₂ (l , ρ)
  amguV-c {m} {.(suc _)} {(t₁ ∷ ts₁)} {(t₂ ∷ ts₂)} {l} {ρ} fns-fns | _ | am | inj₂ (nounify , refl) = inj₂ ((λ {_} → NothingVecHead t₁ t₂ ρ _ _ nounify) , refl)
  amguV-c {m} {.(suc _)} {(t₁ ∷ ts₁)} {(t₂ ∷ ts₂)} {l} {ρ} fns-fns | _ | am | inj₁ (n , σ , a , refl)
   with amgu ts₁ ts₂ (n , σ ++ ρ) | amguV-c (viewV (ts₁) (ts₂) (n , (σ ++ ρ)))
  … | _ | inj₂ (nounify , refl) = inj₂ ((λ {_} → NothingVecTail σ t₁ t₂ _ _ ρ a nounify) , refl)
  … | _ | inj₁ (n1 , σ1 , a1 , refl) = inj₁ (n1 , σ1 ++ σ , MaxVec t₁ t₂ _ _ ρ σ a σ1 a1 , cong (λ σ -> just (n1 , σ)) (++-assoc σ1 σ ρ))

  amgu-c : ∀ {m s t l ρ} -> AmguT s t (l , ρ) (amgu s t (l , ρ)) ->
             (∃ λ n → ∃ λ σ → Max⋆ (Unifies⋆ s t [-◇⋆ sub ρ ]) (sub σ) × amgu {m = m} s t (l , ρ) ≡ just (n , σ ++ ρ ))
           ⊎ (Nothing⋆ (Unifies⋆ s t [-◇⋆ sub ρ ])                     × amgu {m = m} s t (l , ρ) ≡ nothing)
  amgu-c {m} {s} {t} {l} {ρ} amg with amgu s t (l , ρ)
  amgu-c {l = l} {ρ} leaf-leaf | ._
    = inj₁ (l , anil , trivial-problem {_} {_} {leaf} {sub ρ} , cong (λ x -> just (l , x)) (sym (SubList.anil-id-l ρ)) )
  amgu-c (fn-name neq) | _ = inj₂ ((λ f x → neq (Term-function-inj-FunctionName x)) , refl)
  amgu-c (fn-size neq) | _ = inj₂ ((λ f x → neq (Term-function-inj-VecSize x)) , refl)
  amgu-c {s = function fn ts₁} {t = function .fn ts₂} {l = l} {ρ = ρ} fn-fn | _ with amgu ts₁ ts₂ | amguV-c (viewV ts₁ ts₂ (l , ρ))
  … | _ | inj₂ (nounify , refl!) rewrite refl! = inj₂ ((λ {_} f feq → nounify f (Term-function-inj-Vector feq)) , refl)
  … | _ | inj₁ (n , σ , (b , c) , refl!) rewrite refl! = inj₁ (_ , _ , ((cong (function fn) b) , (λ {_} f' feq → c f' (Term-function-inj-Vector feq))) , refl )
  amgu-c leaf-fork | .nothing = inj₂ ((λ _ () ) , refl)
  amgu-c leaf-fn | _ = inj₂ ((λ _ () ) , refl)
  amgu-c fork-fn | _ = inj₂ ((λ _ () ) , refl)
  amgu-c {m} {s1 fork s2} {t1 fork t2} {l} {ρ} fork-fork | ._
   with amgu s1 t1 (l , ρ)  | amgu-c $ view s1 t1 (l , ρ)
  … | .nothing             | inj₂ (nounify , refl) = inj₂ ((λ {_} -> NothingForkLeft s1 t1 ρ s2 t2 nounify) , refl)
  … | .(just (n , σ ++ ρ)) | inj₁ (n , σ , a , refl)
   with amgu s2 t2 (n , σ ++ ρ) | amgu-c (view s2 t2 (n , (σ ++ ρ)))
  … | .nothing                | inj₂ (nounify , refl) = inj₂ ( (λ {_} -> NothingForkRight σ s1 s2 t1 t2 ρ a nounify) , refl)
  … | .(just (n1 , σ1 ++ (σ ++ ρ))) | inj₁ (n1 , σ1 , b , refl)
      = inj₁ (n1 , σ1 ++ σ , MaxFork s1 s2 t1 t2 ρ σ a σ1 b , cong (λ σ -> just (n1 , σ)) (++-assoc σ1 σ ρ))
  amgu-c {suc l} {i x} {i y} (var-var) | .(just (flexFlex x y))
   with thick x y | Thick.fact1 x y (thick x y) refl
  …  | .(just y') | inj₂ (y' , thinxy'≡y , refl )
    = inj₁ (l , anil asnoc i y' / x , var-elim-i-≡ x (i y) (sym (cong i thinxy'≡y)) , refl )
  …  | .nothing | inj₁ ( x≡y , refl ) rewrite sym x≡y
    = inj₁ (suc l , anil , trivial-problem {_} {_} {i x} {sub anil} , refl)
  amgu-c {suc l} {i x} {t} (var-t ix≢t) | .(flexRigid x t)
   with check x t | check-prop x t
  … | .nothing  | inj₂ ( ps , r , refl) = inj₂ ( (λ {_} -> NothingStep x t ix≢t ps r )  , refl)
  … | .(just t') | inj₁ (t' , r , refl) = inj₁ ( l , anil asnoc t' / x , var-elim-i-≡ x t r , refl )
  amgu-c {suc m} {s} {t} {l} {ρ asnoc r / z} s-t
    | .((λ x' → x' ∃asnoc r / z) <$>
        (amgu ((r for z) ◃ s) ((r for z) ◃ t) (l , ρ)))
   with amgu-c (view ((r for z) ◃ s) ((r for z) ◃ t) (l , ρ))
  … | inj₂ (nounify , ra) = inj₂ ( (λ {_} -> NothingFor→NothingComposition s t ρ r z nounify) , cong (_<$>_ (λ x' → x' ∃asnoc r / z)) ra )
  … | inj₁ (n , σ , a , ra)  = inj₁ (n , σ , MaxFor→MaxComposition s t ρ r z σ a , cong (_<$>_ (λ x' → x' ∃asnoc r / z)) ra)
  amgu-c {m} {s} {t} {l} {ρ} (Flip amguts≡amgust amguts) | ._ = amgu-Ccomm⋆ t s (l , ρ) amguts≡amgust (amgu-c amguts)
  amgu-c {zero} {i ()} _ | _

mgu-c : ∀ {m} (s t : Term m) ->
           (∃ λ n → ∃ λ σ → (Max⋆ (Unifies⋆ s t)) (sub σ) × mgu s t ≡ just (n , σ))
         ⊎ (Nothing⋆ (Unifies⋆ s t)                       × mgu s t ≡ nothing)
mgu-c {m} s t = amgu-c (view s t (m , anil))

unify : ∀ {m} (s t : Term m) ->
           (∃ λ n → ∃ λ (σ : AList m n) → Max⋆ (Unifies⋆ s t) $ sub σ)
           ⊎ Nothing⋆ (Unifies⋆ s t)
unify {m} s t with amgu-c (view s t (m , anil))
unify {m} s₁ t | inj₁ (proj₃ , proj₄ , proj₅ , proj₆) = inj₁ (proj₃ , proj₄ , proj₅)
unify {m} s t | inj₂ (proj₃ , _) = inj₂ proj₃

unifyV : ∀ {m N} (s t : Vec (Term m) N) ->
           (∃ λ n → ∃ λ (σ : AList m n) → Max⋆ (Unifies⋆V s t) $ sub σ)
           ⊎ Nothing⋆ (Unifies⋆V s t)
unifyV {m} {N} s t with amguV-c (viewV s t (m , anil))
… | inj₁ (proj₃ , proj₄ , proj₅ , proj₆) = inj₁ (proj₃ , proj₄ , proj₅)
… | inj₂ (proj₃ , _) = inj₂ proj₃
