{- https://lists.chalmers.se/pipermail/agda/2013/006033.html http://code.haskell.org/~Saizan/unification/ 18-Nov-2013 Andrea Vezzosi -}
module UnifyProof where

open import Data.Fin using (Fin; suc; zero)
open import Data.Nat hiding (_≤_)
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Function
open import Relation.Nullary
open import Data.Product renaming (map to _***_)
open import Data.Empty
open import Data.Maybe using (maybe; maybe′; nothing; just; monad; Maybe)
open import Data.Sum
open import Unify
open import Data.List renaming (_++_ to _++L_)
open ≡-Reasoning
open import Category.Functor
open import Category.Monad
import Level as L
open RawMonad (Data.Maybe.monad {L.zero})

record Σ₁ (A : Set1) (F : A -> Set) : Set1 where
  field
    π₁ : A
    π₂ : F π₁

_,,_ : ∀ {A F} (x : A) -> F x -> Σ₁ A F
x ,, b = record{ π₁ = x; π₂ = b }

open Σ₁


Property : (m : ℕ) -> Set1
Property m = Σ₁ (∀ {n} -> (Fin m -> Term n) -> Set) λ P → ∀ {m f g} -> f ≐ g -> P {m} f -> P g

prop-id : ∀ {m n} {f : _ ~> n} {P : Property m} -> π₁ P f -> π₁ P (i ◇ f)
prop-id {_} {_} {f} {P'} Pf = π₂ P' (λ x → sym (Sub.fact1 (f x))) Pf


Unifies : ∀ {m} (s t : Term m) -> Property m
Unifies s t = (λ {_} f -> f ◃ s ≡ f ◃ t) ,, λ {_} {f} {g} f≐g f◃s=f◃t ->
  begin
    g ◃ s
  ≡⟨ sym (◃ext f≐g s) ⟩
    f ◃ s
  ≡⟨ f◃s=f◃t ⟩
    f ◃ t
  ≡⟨ ◃ext f≐g t ⟩
    g ◃ t
  ∎


_∧_ : ∀{m} -> (P Q : Property m) -> Property m
P ∧ Q = (λ {_} f -> π₁ P f × π₁ Q f) ,, λ {_} {_} {_} f≐g Pf×Qf -> π₂ P f≐g (proj₁ Pf×Qf) , π₂ Q f≐g (proj₂ Pf×Qf)


_⇔_ : ∀{m} -> (P Q : Property m) -> Set
P ⇔ Q = ∀ {n} f -> (π₁ P {n} f -> π₁ Q f) × (π₁ Q f -> π₁ P f)

switch : ∀ {m} (P Q : Property m) -> P ⇔ Q -> Q ⇔ P
switch _ _ P⇔Q f = proj₂ (P⇔Q f) , proj₁ (P⇔Q f)


Nothing : ∀{m} -> (P : Property m) -> Set
Nothing P = ∀{n} f -> π₁ P {n} f -> ⊥

_[-◇_] : ∀{m n} (P : Property m) (f : Fin m -> Term n) -> Property n
P [-◇ f ] = (λ {_} g -> π₁ P (g ◇ f)) ,, λ {_} {f'} {g'} f'≐g' Pf'◇f -> π₂ P (◃ext f'≐g' ∘ f)  Pf'◇f

module Properties where
  fact1 : ∀ {m} {s t : Term m} -> (Unifies s t) ⇔ (Unifies t s)
  fact1 _ = sym , sym


  fact1' : ∀ {m} {s1 s2 t1 t2 : Term m}
         -> Unifies (s1 fork s2) (t1 fork t2) ⇔ (Unifies s1 t1 ∧ Unifies s2 t2)
  fact1' f = deconstr _ _ _ _ , uncurry (cong₂ _fork_)
    where deconstr : ∀ {m} (s1 s2 t1 t2 : Term m)
                   -> (s1 fork s2) ≡ (t1 fork t2)
                   -> (s1 ≡ t1) × (s2 ≡ t2)
          deconstr s1 s2 .s1 .s2 refl = refl , refl


  fact2 : ∀ {m} (P Q : Property m) -> P ⇔ Q -> Nothing P -> Nothing Q
  fact2 P Q iff notp f q with iff f
  ...                       | (p2q , q2p) = notp f (q2p q)


  fact3 : ∀ {m} {P : Property m} -> P ⇔ (P [-◇ i ])
  fact3 f = id , id

  fact4 : ∀{m n} {P : Property m} (f : _ -> Term n)
          -> Nothing P -> Nothing (P [-◇ f ])
  fact4 f nop g = nop (g ◇ f)

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

Max : ∀ {m} (P : Property m) -> Property m
Max P' = (λ {_} f → P f × (∀ {n} f' -> P {n} f' -> f' ≤ f)) ,, λ {_} {_} {_} -> lemma1
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

  first : ∀ {m n} (a : _ ~> n) (P Q : Property m) ->
         Nothing (P [-◇ a ]) -> Nothing ((P ∧ Q) [-◇ a ])
  first a P' Q' noP-a f (Pfa , Qfa) = noP-a f Pfa

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
