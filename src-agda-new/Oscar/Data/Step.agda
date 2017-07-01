
module Oscar.Data.Step {𝔣} (FunctionName : Set 𝔣) where

open import Data.Nat using (ℕ; suc; zero)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong₂; cong; sym; trans)
open import Function using (_∘_; flip)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.Product using (∃; _,_; _×_)
open import Data.Empty using (⊥-elim)
open import Data.Vec using (Vec; []; _∷_)

open import Oscar.Data.Fin
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

open import Oscar.Data.Term FunctionName

data Step (n : ℕ) : Set 𝔣 where
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

-- _◃S_ : ∀ {n m} (f : n ⊸ m) -> List (Step n) -> List (Step m)
-- _◃S_ f = Data.List.map (fmapS (f ◃_))

-- map-[] : ∀ {n m} (f : n ⊸ m) ps -> f ◃S ps ≡ [] -> ps ≡ []
-- map-[] f [] _ = refl
-- map-[] f (x ∷ xs) ()

-- module StepM where

--   lemma1 : ∀ {n} (x : Step n) xs t -> [ x ] ⊹ ( xs ⊹ t ) ≡ (x ∷ xs) ⊹ t
--   lemma1 (left y) xs t = refl
--   lemma1 (right y) xs t = refl
--   lemma1 (function fn ls rs) xs t = refl

--   lemma2 : ∀ {n} {r} {t} {xs} (x : Step n) -> xs ⊹ t ≡ r -> ((x ∷ xs) ⊹ t ) ≡ [ x ] ⊹ r
--   lemma2 (left y) eq = cong (λ t -> t fork y) eq
--   lemma2 (right y) eq = cong (λ t -> y fork t) eq
--   lemma2 (function fn ls rs) eq = cong (λ t → function fn (ls ++V t ∷ rs)) eq

--   fact1 : ∀ {n} ps qs (t : Term n) -> (ps ++L qs) ⊹ t ≡ ps ⊹ (qs ⊹ t)
--   fact1 [] qs t = refl
--   fact1 (p ∷ ps) qs t = begin (p ∷ (ps ++L qs)) ⊹ t ≡⟨ lemma2 p (fact1 ps qs t) ⟩
--                               [ p ] ⊹ (ps ⊹ (qs ⊹ t)) ≡⟨ lemma1 p ps (qs ⊹ t)  ⟩
--                               (p ∷ ps) ⊹ (qs ⊹ t) ∎

--   ◃-fact1 : ∀ {m n} (f : m ⊸ n) {N} (rs : Vec (Term m) N) → f ◃s rs ≡ mapV (f ◃_) rs
--   ◃-fact1 f [] = refl
--   ◃-fact1 f (x ∷ rs) rewrite ◃-fact1 f rs = refl

--   ◃-fact2 : ∀ {m n} (f : m ⊸ n) {L} (ls : Vec (Term m) L) {R} (rs : Vec (Term m) R) → f ◃s (ls ++V rs) ≡ (f ◃s ls) ++V (f ◃s rs)
--   ◃-fact2 f [] rs = refl
--   ◃-fact2 f (l ∷ ls) rs = cong ((f ◃ l) ∷_) (◃-fact2 f ls rs)


--   fact2 : ∀ {m n} (f : m ⊸ n) t ps ->
--                f ◃ (ps ⊹ t) ≡ (f ◃S ps) ⊹ (f ◃ t)
--   fact2 f t [] = refl
--   fact2 f t (left y ∷ xs) = cong (λ t -> t fork (f ◃ y)) (fact2 f t xs)
--   fact2 f t (right y ∷ xs) = cong (λ t -> (f ◃ y) fork t) (fact2 f t xs)
--   fact2 f t (function fn ls rs ∷ xs) rewrite sym (◃-fact1 f ls) | sym (◃-fact1 f rs) = cong (function fn) (trans (◃-fact2 f ls ((xs ⊹ t) ∷ rs)) (cong ((f ◃s ls) ++V_) (cong (_∷ (f ◃s rs)) (fact2 f t xs))))

-- mutual

--   check-props : ∀ {m} (x : Fin (suc m)) {N} (ts : Vec (Term (suc m)) N) fn ->
--                  (∃ λ (ts' : Vec (Term m) N) -> ts ≡ ▹ (thin x) ◃s ts' × check x ts ≡ just ts')
--                  ⊎ (∃ λ ps -> function fn ts ≡ (ps ⊹ i x) × check x ts ≡ nothing)
--   check-props x [] fn = inj₁ ([] , refl , refl)
--   check-props x (t ∷ ts) fn with check-prop x t
--   … | inj₂ (ps , t=ps+ix , checkxt=no) rewrite t=ps+ix | checkxt=no = inj₂ (function fn [] ts ∷ ps , refl , refl)
--   … | inj₁ (t' , t=thinxt' , checkxt=t') rewrite checkxt=t' with check-props x ts fn
--   … | inj₁ (ts' , ts=thinxts' , checkxts=ts') rewrite t=thinxt' | ts=thinxts' | checkxts=ts' = inj₁ (_ , refl , refl)
--   … | inj₂ ([] , () , checkxts=no)
--   … | inj₂ (left _ ∷ ps , () , checkxts=no)
--   … | inj₂ (right _ ∷ ps , () , checkxts=no)
--   … | inj₂ (function fn' ls rs ∷ ps , ts=ps+ix , checkxts=no) with Term-function-inj-VecSize ts=ps+ix
--   … | refl with Term-function-inj-Vector ts=ps+ix
--   … | refl rewrite checkxts=no = inj₂ (function fn (t ∷ ls) rs ∷ ps , refl , refl)

--   check-prop : ∀ {m} (x : Fin (suc m)) t ->
--                 (∃ λ t' -> t ≡ ▹ (thin x) ◃ t' × check x t ≡ just t')
--                 ⊎ (∃ λ ps -> t ≡ (ps ⊹ i x) × check x t ≡ nothing)
--   check-prop x (i x') with checkfact1 x x' (check x x') refl
--   check-prop x (i .x) | inj₁ (refl , e) = inj₂ ([] , refl , cong (_<$>_ i) e)
--   ... | inj₂ (y , thinxy≡x' , thickxx'≡justy')
--       = inj₁ (i y
--              , cong i (sym (thinxy≡x'))
--              , cong (_<$>_ i) thickxx'≡justy' )
--   check-prop x leaf = inj₁ (leaf , (refl , refl))
--   check-prop x (s fork t)
--    with check-prop x s                     | check-prop x t
--   ... | inj₁ (s' , s≡thinxs' , checkxs≡s') | inj₁ (t' , t≡thinxt' , checkxt≡t')
--       = inj₁ (s' fork t' , cong₂ _fork_ s≡thinxs' t≡thinxt'
--              , cong₂ (λ a b -> _fork_ <$> a ⊛ b) checkxs≡s' checkxt≡t' )
--   ... | inj₂ (ps , s≡ps+ix , checkxs≡no )  | _
--       = inj₂ (left t ∷ ps , cong (λ s -> s fork t) s≡ps+ix
--              , cong (λ a -> _fork_ <$> a ⊛ check x t) checkxs≡no )
--   ... | _                                  | inj₂ (ps , s≡ps+ix , checkxs≡no )
--       = inj₂ (right s ∷ ps , cong (λ t -> s fork t) s≡ps+ix
--              , trans (cong (λ a -> _fork_ <$> check x s ⊛ a) checkxs≡no) (lemma (_fork_ <$> check x s)))
--     where
--       lemma : ∀ {a b : Set} {y : b} (x : Maybe a) -> maybe (λ _ → y) y x ≡ y
--       lemma (just x') = refl
--       lemma nothing = refl
--   check-prop x (function fn ts) with check-props x ts fn
--   … | inj₁ (t' , t=thinxt' , checkxt=t') rewrite checkxt=t' = inj₁ (function fn t' , cong (function fn) t=thinxt' , refl)
--   … | inj₂ (ps , t=ps+ix , checkxt=no) rewrite checkxt=no = inj₂ (ps , t=ps+ix , refl)

-- -- data SizedTerm (n : ℕ) : ℕ → Set where
-- --   i : (x : Fin n) -> SizedTerm n (suc zero)
-- --   leaf : SizedTerm n (suc zero)
-- --   _fork_ : (s : ∃ (SizedTerm n)) (t : ∃ (SizedTerm n)) -> SizedTerm n (suc (proj₁ s + proj₁ t))
-- --   function : FunctionName → ∀ {f} → (ts : Vec (∃ (SizedTerm n)) f) → SizedTerm n (suc (Data.Vec.sum (Data.Vec.map proj₁ ts)))

-- -- data SizedStep (n : ℕ) : Set where
-- --   left : ∃ (SizedTerm n) -> SizedStep n
-- --   right : ∃ (SizedTerm n) -> SizedStep n
-- --   function : FunctionName → ∀ {L} → Vec (∃ (SizedTerm n)) L → ∀ {R} → Vec (∃ (SizedTerm n)) R → SizedStep n

-- -- mutual

-- --   toSizedTerm : ∀ {n} → Term n → ∃ (SizedTerm n)
-- --   toSizedTerm (i x) = suc zero , i x
-- --   toSizedTerm leaf = suc zero , leaf
-- --   toSizedTerm (l fork r) with toSizedTerm l | toSizedTerm r
-- --   … | L , sl | R , sr = (suc (L + R)) , ((L , sl) fork (R , sr))
-- --   toSizedTerm (function fn ts) with toSizedTerms ts
-- --   … | sts = suc (Data.Vec.sum (Data.Vec.map proj₁ sts)) , SizedTerm.function fn sts

-- --   fromSizedTerm : ∀ {n} → ∃ (SizedTerm n) → Term n
-- --   fromSizedTerm (_ , i x) = i x
-- --   fromSizedTerm (_ , leaf) = leaf
-- --   fromSizedTerm (_ , (_fork_ t₁ t₂)) = (fromSizedTerm t₁ fork fromSizedTerm t₂)
-- --   fromSizedTerm (_ , function fn ts) = function fn (fromSizedTerms ts)

-- --   toSizedTerms : ∀ {n N} → Vec (Term n) N → Vec (∃ (SizedTerm n)) N
-- --   toSizedTerms [] = []
-- --   toSizedTerms (t ∷ ts) = toSizedTerm t ∷ toSizedTerms ts

-- --   fromSizedTerms : ∀ {n N} → Vec (∃ (SizedTerm n)) N → Vec (Term n) N
-- --   fromSizedTerms [] = []
-- --   fromSizedTerms (t ∷ ts) = fromSizedTerm t ∷ fromSizedTerms ts

-- -- mutual

-- --   isoSizedTerm : ∀ {n} → (st : ∃ (SizedTerm n)) → st ≡ toSizedTerm (fromSizedTerm st)
-- --   isoSizedTerm (._ , i x) = refl
-- --   isoSizedTerm (._ , leaf) = refl
-- --   isoSizedTerm (.(suc (proj₁ s + proj₁ t)) , (s fork t)) rewrite sym (isoSizedTerm s) | sym (isoSizedTerm t) = refl
-- --   isoSizedTerm (._ , function x ts) rewrite sym (isoSizedTerms ts) = refl

-- --   isoSizedTerms : ∀ {n N} → (st : Vec (∃ (SizedTerm n)) N) → st ≡ toSizedTerms (fromSizedTerms st)
-- --   isoSizedTerms [] = refl
-- --   isoSizedTerms (t ∷ ts) rewrite sym (isoSizedTerm t) | sym (isoSizedTerms ts) = refl

-- -- mutual

-- --   isoTerm : ∀ {n} → (t : Term n) → t ≡ fromSizedTerm (toSizedTerm t)
-- --   isoTerm (i x) = refl
-- --   isoTerm leaf = refl
-- --   isoTerm (s fork t) rewrite sym (isoTerm s) | sym (isoTerm t) = refl
-- --   isoTerm (function fn ts) rewrite sym (isoTerms ts) = refl

-- --   isoTerms : ∀ {n N} → (t : Vec (Term n) N) → t ≡ fromSizedTerms (toSizedTerms t)
-- --   isoTerms [] = refl
-- --   isoTerms (t ∷ ts) rewrite sym (isoTerm t) | sym (isoTerms ts) = refl

-- -- toSizedStep : ∀ {n} → Step n → SizedStep n
-- -- toSizedStep (left r) = left (toSizedTerm r)
-- -- toSizedStep (right l) = right (toSizedTerm l)
-- -- toSizedStep (function fn ls rs) = function fn (toSizedTerms ls) (toSizedTerms rs)

-- -- fromSizedStep : ∀ {n} → SizedStep n → Step n
-- -- fromSizedStep (left r) = left (fromSizedTerm r)
-- -- fromSizedStep (right l) = right (fromSizedTerm l)
-- -- fromSizedStep (function fn ls rs) = function fn (fromSizedTerms ls) (fromSizedTerms rs)

-- -- isoSizedStep : ∀ {n} → (ss : SizedStep n) → ss ≡ toSizedStep (fromSizedStep ss)
-- -- isoSizedStep (left r) rewrite sym (isoSizedTerm r) = refl
-- -- isoSizedStep (right l) rewrite sym (isoSizedTerm l) = refl
-- -- isoSizedStep (function fn ls rs) rewrite sym (isoSizedTerms ls) | sym (isoSizedTerms rs) = refl

-- -- isoStep : ∀ {n} → (s : Step n) → s ≡ fromSizedStep (toSizedStep s)
-- -- isoStep (left r) rewrite sym (isoTerm r) = refl
-- -- isoStep (right l) rewrite sym (isoTerm l) = refl
-- -- isoStep (function fn ls rs) rewrite sym (isoTerms ls) | sym (isoTerms rs) = refl

-- -- toSizedSteps : ∀ {n} → List (Step n) → List (SizedStep n)
-- -- toSizedSteps [] = []
-- -- toSizedSteps (s ∷ ss) = toSizedStep s ∷ toSizedSteps ss

-- -- fromSizedSteps : ∀ {n} → List (SizedStep n) → List (Step n)
-- -- fromSizedSteps [] = []
-- -- fromSizedSteps (s ∷ ss) = fromSizedStep s ∷ fromSizedSteps ss

-- -- isoSizedSteps : ∀ {n} → (ss : List (SizedStep n)) → ss ≡ toSizedSteps (fromSizedSteps ss)
-- -- isoSizedSteps [] = refl
-- -- isoSizedSteps (s ∷ ss) rewrite sym (isoSizedStep s) | sym (isoSizedSteps ss) = refl

-- -- isoSteps : ∀ {n} → (s : List (Step n)) → s ≡ fromSizedSteps (toSizedSteps s)
-- -- isoSteps [] = refl
-- -- isoSteps (s ∷ ss) rewrite sym (isoStep s) | sym (isoSteps ss) = refl

-- -- _Sized⊹_ : ∀ {n} (ps : List (SizedStep n)) (t : ∃ (SizedTerm n)) -> ∃ (SizedTerm n)
-- -- [] Sized⊹ t = t
-- -- (left r ∷ ps) Sized⊹ t = _ , (ps Sized⊹ t) SizedTerm.fork r
-- -- (right l ∷ ps) Sized⊹ t = _ , l SizedTerm.fork (ps Sized⊹ t)
-- -- (function fn ls rs ∷ ps) Sized⊹ t = _ , function fn (ls ++V (ps Sized⊹ t) ∷ rs)

-- -- fromSizedTerms-commute : ∀ {n} {L R} → (ls : Vec (∃ (SizedTerm n)) L) (rs : Vec (∃ (SizedTerm n)) R) → fromSizedTerms (ls ++V rs) ≡ fromSizedTerms ls ++V fromSizedTerms rs
-- -- fromSizedTerms-commute [] rs = refl
-- -- fromSizedTerms-commute (l ∷ ls) rs rewrite fromSizedTerms-commute ls rs = refl

-- -- toSizedTerms-commute : ∀ {n} {L R} → (ls : Vec (Term n) L) (rs : Vec (Term n) R) → toSizedTerms (ls ++V rs) ≡ toSizedTerms ls ++V toSizedTerms rs
-- -- toSizedTerms-commute [] rs = refl
-- -- toSizedTerms-commute (l ∷ ls) rs rewrite toSizedTerms-commute ls rs = refl

-- -- isoSized⊹ : ∀ {n} (ps : List (SizedStep n)) (t : ∃ (SizedTerm n)) → fromSizedTerm (ps Sized⊹ t) ≡ fromSizedSteps ps ⊹ fromSizedTerm t
-- -- isoSized⊹ [] t = refl
-- -- isoSized⊹ (left r ∷ ps) t rewrite isoSized⊹ ps t = refl
-- -- isoSized⊹ (right l ∷ ps) t rewrite isoSized⊹ ps t = refl
-- -- isoSized⊹ (function fn ls rs ∷ ps) t rewrite sym (isoSized⊹ ps t) | fromSizedTerms-commute ls ((ps Sized⊹ t) ∷ rs) = refl

-- -- iso⊹ : ∀ {n} (ps : List (Step n)) (t : Term n) → toSizedTerm (ps ⊹ t) ≡ toSizedSteps ps Sized⊹ toSizedTerm t
-- -- iso⊹ [] t = refl
-- -- iso⊹ (left r ∷ ps) t rewrite iso⊹ ps t = refl
-- -- iso⊹ (right l ∷ ps) t rewrite iso⊹ ps t = refl
-- -- iso⊹ (function fn ls rs ∷ ps) t rewrite sym (iso⊹ ps t) | toSizedTerms-commute ls ((ps ⊹ t) ∷ rs) = refl

-- -- import Data.Vec.Properties
-- -- import Relation.Binary.PropositionalEquality as PE
-- -- open Data.Vec.Properties.UsingVectorEquality (PE.setoid ℕ)
-- -- import Data.Vec.Equality
-- -- open Data.Vec.Equality.PropositionalEquality using (to-≡)

-- -- -- some equivalences needed to adapt Tactic.Nat to the standard library
-- -- module EquivalenceOf≤ where
-- --   open import Agda.Builtin.Equality
-- --   open import Agda.Builtin.Nat

-- --   open import Data.Nat using (less-than-or-equal) renaming (_≤_ to _≤s_)
-- --   open import Data.Nat.Properties using (≤⇒≤″; ≤″⇒≤)
-- --   open import Prelude using (diff; id) renaming (_≤_ to _≤p_)

-- --   open import Tactic.Nat.Generic (quote _≤p_) (quote Function.id) (quote Function.id) using (by)

-- --   ≤p→≤s : ∀ {a b} → a ≤p b → a ≤s b
-- --   ≤p→≤s (diff k b₊₁≡k₊₁+a) = ≤″⇒≤ (less-than-or-equal {k = k} (by b₊₁≡k₊₁+a))

-- --   ≤s→≤p : ∀ {a b} → a ≤s b → a ≤p b
-- --   ≤s→≤p a≤sb with ≤⇒≤″ a≤sb
-- --   ≤s→≤p _ | less-than-or-equal {k = k} a+k≡b = diff k (by a+k≡b)

-- -- module _ where
-- --   open EquivalenceOf≤
-- --   open import Data.Nat
-- --   open import Tactic.Nat.Generic (quote Data.Nat._≤_) (quote ≤s→≤p) (quote ≤p→≤s) public

-- -- growingSize : ∀ {m} (st : ∃ (SizedTerm m)) → (sp : SizedStep m) (sps : List (SizedStep m)) → proj₁ ((sp ∷ sps) Sized⊹ st) > proj₁ st
-- -- growingSize st (left r) [] = auto
-- -- growingSize st (right l) [] = auto
-- -- growingSize {m} st (function fn ls rs) [] rewrite to-≡ (map-++-commute proj₁ ls {ys = st ∷ rs}) | Data.Vec.Properties.sum-++-commute (mapV proj₁ ls) {ys = mapV proj₁ (st ∷ rs)} = auto
-- -- growingSize st (left x) (p₂ ∷ ps) = by (growingSize st p₂ ps)
-- -- growingSize st (right x) (p₂ ∷ ps) = by (growingSize st p₂ ps)
-- -- growingSize st (function fn ls rs) (p₂ ∷ ps) rewrite to-≡ (map-++-commute proj₁ ls {ys = ((p₂ ∷ ps) Sized⊹ st) ∷ rs}) | Data.Vec.Properties.sum-++-commute (mapV proj₁ ls) {ys = mapV proj₁ (((p₂ ∷ ps) Sized⊹ st) ∷ rs)} = by (growingSize st p₂ ps)

-- -- No-Cycle : ∀{m} (t : Term m) ps -> (eq : t ≡ ps ⊹ t) → ps ≡ []
-- -- No-Cycle t [] eq = refl
-- -- No-Cycle t (p ∷ ps) eq = refute (subst (λ v → v > proj₁ (toSizedTerm t)) (sym (trans same iso)) growth) where
-- --   same : proj₁ (toSizedTerm t) ≡ proj₁ (toSizedTerm ((p ∷ ps) ⊹ t))
-- --   growth : proj₁ ((toSizedStep p ∷ toSizedSteps ps) Sized⊹ toSizedTerm t) > proj₁ (toSizedTerm t)
-- --   iso : proj₁ (toSizedTerm ((p ∷ ps) ⊹ t)) ≡ proj₁ ((toSizedStep p ∷ toSizedSteps ps) Sized⊹ toSizedTerm t)
-- --   growth = growingSize (toSizedTerm t) (toSizedStep p) (toSizedSteps ps)
-- --   same = cong (proj₁ ∘ toSizedTerm) eq
-- --   iso = cong proj₁ (iso⊹ (p ∷ ps) t)

-- -- module Step2 where
-- --   fact : ∀{m} (x : Fin m) p ps -> Nothing (Unifies (i x) ((p ∷ ps) ⊹ i x))
-- --   fact x p ps f r with No-Cycle (f x) (f ◃S (p ∷ ps)) (trans r (StepM.fact2 f (i x) (p ∷ ps)))
-- --   ... | ()

-- -- NothingStep : ∀ {l} (x : Fin (suc l)) (t : Term (suc l)) →
-- --               i x ≢ t →
-- --               (ps : List (Step (suc l))) →
-- --               t ≡ (ps ⊹ i x) →
-- --               ∀ {n} (f : Fin (suc l) → Term n) → f x ≢ (f ◃ t)
-- -- NothingStep {l} x t ix≢t ps r = No-Unifier
-- --   where
-- --     No-Unifier : {n : ℕ} (f : Fin (suc l) → Term n) → f x ≢ f ◃ t
-- --     No-Unifier f fx≡f◃t = ix≢t (sym (trans r (cong (λ ps -> ps ⊹ i x) ps≡[])))
-- --           where
-- --             ps≡[] : ps ≡ []
-- --             ps≡[] = map-[] f ps (No-Cycle (f x) (f ◃S ps)
-- --                   (begin f x             ≡⟨ fx≡f◃t ⟩
-- --                          f ◃ t           ≡⟨ cong (f ◃_) r ⟩
-- --                          f ◃ (ps ⊹ i x)  ≡⟨ StepM.fact2 f (i x) ps ⟩
-- --                          (f ◃S ps) ⊹ f x ∎))
