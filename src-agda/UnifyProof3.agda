{- https://lists.chalmers.se/pipermail/agda/2013/006033.html http://code.haskell.org/~Saizan/unification/ 18-Nov-2013 Andrea Vezzosi -}
-- try simplifying by ignoring extentionality requirement of Property
module UnifyProof3 where

open import Data.Fin using (Fin; suc; zero)
open import Data.Nat hiding (_≤_)
open import Relation.Binary.PropositionalEquality
open import Function
open import Relation.Nullary
open import Data.Product renaming (map to _***_)
open import Data.Empty
open import Data.Maybe using (maybe; nothing; just; monad; Maybe)
open import Data.Sum
open import Unify
open import UnifyProof
open Σ₁
open import Data.List renaming (_++_ to _++L_)
open ≡-Reasoning
open import Category.Functor
open import Category.Monad
import Level
open RawMonad (Data.Maybe.monad {Level.zero})

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
