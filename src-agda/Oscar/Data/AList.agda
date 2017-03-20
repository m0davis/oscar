
module Oscar.Data.AList {𝔣} (FunctionName : Set 𝔣) where

open import Oscar.Data.Fin
open import Oscar.Data.Nat
open import Oscar.Data.Product
open import Oscar.Data.Term FunctionName

data AList : Nat -> Nat -> Set 𝔣 where
  anil : ∀ {n} -> AList n n
  _asnoc_/_ : ∀ {m n} (σ : AList m n) (t' : Term m) (x : Fin (suc m))
               -> AList (suc m) n

-- open import Relation.Binary.PropositionalEquality renaming ([_] to [[_]])
-- open ≡-Reasoning

-- step-prop : ∀ {m n} (s t : Term (suc m)) (σ : AList m n) r z ->
--           (Unifies s t [-◇ sub (σ asnoc r / z) ]) ⇔ (Unifies ((r for z) ◃ s) ((r for z) ◃ t) [-◇ sub σ ])
-- step-prop s t σ r z f = to , from
--   where
--     lemma1 : ∀ t -> (f ◇ sub σ) ◃ ((r for z) ◃ t) ≡ (f ◇ (sub σ ◇ (r for z))) ◃ t
--     lemma1 t = bind-assoc f (sub σ) (r for z) t
--     to = λ a → begin
--                  (f ◇ sub σ) ◃ ((r for z) ◃ s) ≡⟨ lemma1 s ⟩
--                  (f ◇ (sub σ ◇ (r for z))) ◃ s ≡⟨ a ⟩
--                  (f ◇ (sub σ ◇ (r for z))) ◃ t ≡⟨ sym (lemma1 t) ⟩
--                  (f ◇ sub σ) ◃ ((r for z) ◃ t) ∎
--     from = λ a → begin
--                    (f ◇ (sub σ ◇ (r for z))) ◃ s ≡⟨ sym (lemma1 s) ⟩
--                    (f ◇ sub σ) ◃ ((r for z) ◃ s) ≡⟨ a ⟩
--                    (f ◇ sub σ) ◃ ((r for z) ◃ t) ≡⟨ lemma1 t ⟩
--                    (f ◇ (sub σ ◇ (r for z))) ◃ t ∎

-- record ⋆amgu (T : ℕ → Set) : Set where
--   field amgu : ∀ {m} (s t : T m) (acc : ∃ (AList m)) -> Maybe (∃ (AList m))

-- open ⋆amgu ⦃ … ⦄ public

-- open import Category.Monad using (RawMonad)
-- import Level
-- open RawMonad (Data.Maybe.monad {Level.zero})

-- open import Relation.Binary using (IsDecEquivalence)
-- open import Relation.Nullary using (Dec; yes; no)
-- open import Data.Nat using (ℕ; _≟_)
-- open import Data.Product using () renaming (Σ to Σ₁)
-- open Σ₁ renaming (proj₁ to π₁; proj₂ to π₂)
-- open import Data.Product using (Σ)
-- open Σ
-- open import Data.Sum
-- open import Function

-- NothingForkLeft : ∀ {m l} (s1 t1 : Term m) (ρ : AList m l) (s2 t2 : Term m) →
--                Nothing⋆ $ Unifies⋆ s1 t1 [-◇⋆ sub ρ ] →
--                Nothing⋆ $ Unifies⋆ (s1 fork s2) (t1 fork t2) [-◇⋆ sub ρ ]
-- NothingForkLeft s1 t1 ρ s2 t2 nounify = No[Q◇ρ]→No[P◇ρ] No[Q◇ρ]
--   where
--     P = Unifies⋆ (s1 fork s2) (t1 fork t2)
--     Q = (Unifies⋆ s1 t1 ∧⋆ Unifies⋆ s2 t2)
--     Q⇔P : Q ⇔⋆ P
--     Q⇔P = switch⋆ P Q (Properties.fact1' {_} {s1} {s2} {t1} {t2})
--     No[Q◇ρ]→No[P◇ρ] : Nothing⋆ (Q [-◇⋆ sub ρ ]) -> Nothing⋆ (P [-◇⋆ sub ρ ])
--     No[Q◇ρ]→No[P◇ρ] = Properties.fact2⋆ (Q [-◇⋆ sub ρ ]) (P [-◇⋆ sub ρ ]) (Properties.fact5⋆ Q P (sub ρ) Q⇔P)
--     No[Q◇ρ] : Nothing⋆ (Q [-◇⋆ sub ρ ])
--     No[Q◇ρ] = failure-propagation.first⋆ (sub ρ) (Unifies⋆ s1 t1) (Unifies⋆ s2 t2) nounify

-- NothingForkRight : ∀ {m l n} (σ : AList l n)
--                   (s1 s2 : Term m)
--                   (t1 t2 : Term m) →
--                   (ρ : AList m l) →
--                   Max⋆ (Unifies⋆ s1 t1 [-◇⋆ sub ρ ]) $ sub σ →
--                   Nothing⋆ $ Unifies⋆ s2 t2 [-◇⋆ sub (σ ++ ρ) ] →
--                   Nothing⋆ $ Unifies⋆ (s1 fork s2) (t1 fork t2) [-◇⋆ sub ρ ]
-- NothingForkRight σ s1 s2 t1 t2 ρ a nounify = No[Q◇ρ]→No[P◇ρ]⋆ No[Q◇ρ]⋆
--     where
--     P⋆ = Unifies⋆ (s1 fork s2) (t1 fork t2)
--     Q⋆ = (Unifies⋆ s1 t1 ∧⋆ Unifies⋆ s2 t2)
--     Q⇔P⋆ : Q⋆ ⇔⋆ P⋆
--     Q⇔P⋆ = switch⋆ P⋆ Q⋆ (Properties.fact1'⋆ {_} {s1} {s2} {t1} {t2})
--     No[Q◇ρ]→No[P◇ρ]⋆ : Nothing⋆ (Q⋆ [-◇⋆ sub ρ ]) -> Nothing⋆ (P⋆ [-◇⋆ sub ρ ])
--     No[Q◇ρ]→No[P◇ρ]⋆ = Properties.fact2⋆ (Q⋆ [-◇⋆ sub ρ ]) (P⋆ [-◇⋆ sub ρ ]) (Properties.fact5⋆ Q⋆ P⋆ (sub ρ) Q⇔P⋆)
--     No[Q◇ρ]⋆ : Nothing⋆ (Q⋆ [-◇⋆ sub ρ ])
--     No[Q◇ρ]⋆ = failure-propagation.second⋆ (sub ρ) (sub σ) (Unifies⋆ s1 t1) (Unifies s2 t2) a
--        (λ f → nounify f ∘ π₂ (Unifies s2 t2) (cong (f ◃_) ∘ sym ∘ SubList.fact1 σ ρ))

-- MaxFork : ∀ {m l n n1} (s1 s2 t1 t2 : Term m)
--                        (ρ : AList m l) (σ : AList l n) →
--                      Max⋆ (Unifies⋆ s1 t1 [-◇⋆ sub ρ ]) $ sub σ →
--                      (σ1 : AList n n1) →
--                      Max⋆ (Unifies⋆ s2 t2 [-◇⋆ sub (σ ++ ρ) ]) $ sub σ1 →
--                      Max⋆ (Unifies⋆ (s1 fork s2) (t1 fork t2) [-◇⋆ sub ρ ]) $ sub (σ1 ++ σ)
-- MaxFork s1 s2 t1 t2 ρ σ a σ1 b = Max[P∧Q◇ρ][σ1++σ]
--     where
--       P = Unifies s1 t1
--       Q = Unifies s2 t2
--       P∧Q = P ∧ Q
--       C = Unifies (s1 fork s2) (t1 fork t2)
--       Max[C◇ρ]⇔Max[P∧Q◇ρ] : Max (C [-◇ sub ρ ]) ⇔ Max (P∧Q [-◇ sub ρ ])
--       Max[C◇ρ]⇔Max[P∧Q◇ρ] = Max.fact (C [-◇ sub ρ ]) (P∧Q [-◇ sub ρ ]) (Properties.fact5 C P∧Q (sub ρ)
--                       (Properties.fact1' {_} {s1} {s2} {t1} {t2}))
--       Max[Q◇σ++ρ]⇔Max[Q◇σ◇ρ] : Max (Q [-◇ sub (σ ++ ρ)]) ⇔ Max (Q [-◇ sub σ ◇ sub ρ ])
--       Max[Q◇σ++ρ]⇔Max[Q◇σ◇ρ] = Max.fact (Q [-◇ sub (σ ++ ρ)]) (Q [-◇ sub σ ◇ sub ρ ]) (Properties.fact6 Q (SubList.fact1 σ ρ))
--       Max[P∧Q◇ρ][σ1++σ] : π₁ (Max (C [-◇ sub ρ ])) (sub (σ1 ++ σ))
--       Max[P∧Q◇ρ][σ1++σ] = π₂ (Max (C [-◇ sub ρ ])) (≐-sym (SubList.fact1 σ1 σ))
--                (proj₂ (Max[C◇ρ]⇔Max[P∧Q◇ρ] (sub σ1 ◇ sub σ))
--                       (optimist (sub ρ) (sub σ) (sub σ1) P Q (DClosed.fact1 s1 t1) a (proj₁ (Max[Q◇σ++ρ]⇔Max[Q◇σ◇ρ] (sub σ1)) b)))

-- NothingVecHead : ∀ {m l} (t₁ t₂ : Term m) (ρ : AList m l) {N} (ts₁ ts₂ : Vec (Term m) N) →
--                Nothing⋆ $ Unifies⋆ t₁ t₂ [-◇⋆ sub ρ ] →
--                Nothing⋆ $ Unifies⋆V (t₁ ∷ ts₁) (t₂ ∷ ts₂) [-◇⋆ sub ρ ]
-- NothingVecHead t₁ t₂ ρ ts₁ ts₂ nounify = No[Q◇ρ]→No[P◇ρ] No[Q◇ρ]
--   where
--     P = Unifies⋆V (t₁ ∷ ts₁) (t₂ ∷ ts₂)
--     Q = (Unifies⋆ t₁ t₂ ∧⋆ Unifies⋆V ts₁ ts₂)
--     Q⇔P : Q ⇔⋆ P
--     Q⇔P = switch⋆ P Q (Properties.fact1'V {_} {t₁} {t₂} {_} {ts₁} {ts₂})
--     No[Q◇ρ]→No[P◇ρ] : Nothing⋆ (Q [-◇⋆ sub ρ ]) -> Nothing⋆ (P [-◇⋆ sub ρ ])
--     No[Q◇ρ]→No[P◇ρ] = Properties.fact2⋆ (Q [-◇⋆ sub ρ ]) (P [-◇⋆ sub ρ ]) (Properties.fact5⋆ Q P (sub ρ) Q⇔P)
--     No[Q◇ρ] : Nothing⋆ (Q [-◇⋆ sub ρ ])
--     No[Q◇ρ] = failure-propagation.first⋆ (sub ρ) (Unifies⋆ t₁ t₂) (Unifies⋆V ts₁ ts₂) nounify

-- NothingVecTail : ∀ {m l n} (σ : AList l n)
--                   (t₁ t₂ : Term m)
--                   {N}
--                   (ts₁ ts₂ : Vec (Term m) N) →
--                   (ρ : AList m l) →
--                   Max⋆ (Unifies⋆ t₁ t₂ [-◇⋆ sub ρ ]) $ sub σ →
--                   Nothing⋆ $ Unifies⋆V ts₁ ts₂ [-◇⋆ sub (σ ++ ρ) ] →
--                   Nothing⋆ $ Unifies⋆V (t₁ ∷ ts₁) (t₂ ∷ ts₂) [-◇⋆ sub ρ ]
-- NothingVecTail σ t₁ t₂ ts₁ ts₂ ρ a nounify = No[Q◇ρ]→No[P◇ρ]⋆ No[Q◇ρ]⋆
--     where
--     P⋆ = Unifies⋆V (t₁ ∷ ts₁) (t₂ ∷ ts₂)
--     Q⋆ = (Unifies⋆ t₁ t₂ ∧⋆ Unifies⋆V ts₁ ts₂)
--     Q⇔P⋆ : Q⋆ ⇔⋆ P⋆
--     Q⇔P⋆ = switch⋆ P⋆ Q⋆ (Properties.fact1'V {_} {t₁} {t₂} {_} {ts₁} {ts₂})
-- --    Q⇔P⋆ = switch⋆ P⋆ Q⋆ (Properties.fact1'⋆ {_} {s1} {s2} {t1} {t2})
--     No[Q◇ρ]→No[P◇ρ]⋆ : Nothing⋆ (Q⋆ [-◇⋆ sub ρ ]) -> Nothing⋆ (P⋆ [-◇⋆ sub ρ ])
--     No[Q◇ρ]→No[P◇ρ]⋆ = Properties.fact2⋆ (Q⋆ [-◇⋆ sub ρ ]) (P⋆ [-◇⋆ sub ρ ]) (Properties.fact5⋆ Q⋆ P⋆ (sub ρ) Q⇔P⋆)
--     No[Q◇ρ]⋆ : Nothing⋆ (Q⋆ [-◇⋆ sub ρ ])
--     No[Q◇ρ]⋆ = failure-propagation.second⋆ (sub ρ) (sub σ) (Unifies⋆ t₁ t₂) (UnifiesV ts₁ ts₂) a
--        (λ f → nounify f ∘ π₂ (UnifiesV ts₁ ts₂) (cong (f ◃_) ∘ sym ∘ SubList.fact1 σ ρ))

-- MaxVec : ∀ {m l n n1} (t₁ t₂ : Term m) {N} (ts₁ ts₂ : Vec (Term m) N)
--                        (ρ : AList m l) (σ : AList l n) →
--                      Max⋆ (Unifies⋆ t₁ t₂ [-◇⋆ sub ρ ]) $ sub σ →
--                      (σ1 : AList n n1) →
--                      Max⋆ (Unifies⋆V ts₁ ts₂ [-◇⋆ sub (σ ++ ρ) ]) $ sub σ1 →
--                      Max⋆ (Unifies⋆V (t₁ ∷ ts₁) (t₂ ∷ ts₂) [-◇⋆ sub ρ ]) $ sub (σ1 ++ σ)
-- MaxVec t₁ t₂ ts₁ ts₂ ρ σ a σ1 b = Max[P∧Q◇ρ][σ1++σ]
--     where
--       P = Unifies t₁ t₂
--       Q = UnifiesV ts₁ ts₂
--       P∧Q = P ∧ Q
--       C = UnifiesV (t₁ ∷ ts₁) (t₂ ∷ ts₂)
--       Max[C◇ρ]⇔Max[P∧Q◇ρ] : Max (C [-◇ sub ρ ]) ⇔ Max (P∧Q [-◇ sub ρ ])
--       Max[C◇ρ]⇔Max[P∧Q◇ρ] = Max.fact (C [-◇ sub ρ ]) (P∧Q [-◇ sub ρ ]) (Properties.fact5 C P∧Q (sub ρ)
--                       (Properties.fact1'V {_} {t₁} {t₂} {_} {ts₁} {ts₂}))
--       Max[Q◇σ++ρ]⇔Max[Q◇σ◇ρ] : Max (Q [-◇ sub (σ ++ ρ)]) ⇔ Max (Q [-◇ sub σ ◇ sub ρ ])
--       Max[Q◇σ++ρ]⇔Max[Q◇σ◇ρ] = Max.fact (Q [-◇ sub (σ ++ ρ)]) (Q [-◇ sub σ ◇ sub ρ ]) (Properties.fact6 Q (SubList.fact1 σ ρ))
--       Max[P∧Q◇ρ][σ1++σ] : π₁ (Max (C [-◇ sub ρ ])) (sub (σ1 ++ σ))
--       Max[P∧Q◇ρ][σ1++σ] = π₂ (Max (C [-◇ sub ρ ])) (≐-sym (SubList.fact1 σ1 σ))
--                (proj₂ (Max[C◇ρ]⇔Max[P∧Q◇ρ] (sub σ1 ◇ sub σ))
--                       (optimist (sub ρ) (sub σ) (sub σ1) P Q (DClosed.fact1 t₁ t₂) a (proj₁ (Max[Q◇σ++ρ]⇔Max[Q◇σ◇ρ] (sub σ1)) b)))

-- NothingFor→NothingComposition : ∀ {m l} (s t : Term (suc m)) (ρ : AList m l)
--              (r : Term m) (z : Fin (suc m)) →
--            Nothing⋆ (Unifies⋆ ((r for z) ◃ s) ((r for z) ◃ t) [-◇⋆ sub ρ ]) →
--            Nothing⋆ (Unifies⋆ s t [-◇⋆ sub (ρ asnoc r / z) ])
-- NothingFor→NothingComposition s t ρ r z nounify = NoQ→NoP nounify
--       where
--         P = Unifies s t [-◇ sub (ρ asnoc r / z) ]
--         Q = Unifies ((r for z) ◃ s) ((r for z) ◃ t) [-◇ sub ρ ]
--         NoQ→NoP : Nothing Q → Nothing P
--         NoQ→NoP = Properties.fact2 Q P (switch P Q (step-prop s t ρ r z))

-- MaxFor→MaxComposition : ∀ {m l n} (s t : Term (suc m)) (ρ : AList m l)
--               (r : Term m) (z : Fin (suc m)) (σ : AList l n) →
--             Max⋆ (Unifies⋆ ((r for z) ◃ s) ((r for z) ◃ t) [-◇⋆ sub ρ ]) $ sub σ →
--             Max⋆ (Unifies⋆ s t [-◇⋆ sub (ρ asnoc r / z) ]) $ sub σ
-- MaxFor→MaxComposition s t ρ r z σ a = proj₂ (MaxP⇔MaxQ (sub σ)) a
--       where
--         P = Unifies s t [-◇ sub (ρ asnoc r / z) ]
--         Q = Unifies ((r for z) ◃ s) ((r for z) ◃ t) [-◇ sub ρ ]
--         MaxP⇔MaxQ : Max P ⇔ Max Q
--         MaxP⇔MaxQ = Max.fact P Q (step-prop s t ρ r z)

-- module _ ⦃ isDecEquivalenceA : IsDecEquivalence (_≡_ {A = FunctionName}) ⦄ where

--   open IsDecEquivalence isDecEquivalenceA using () renaming (_≟_ to _≟F_)

--   mutual

--     instance ⋆amguTerm : ⋆amgu Term
--     ⋆amgu.amgu ⋆amguTerm leaf leaf acc = just acc
--     ⋆amgu.amgu ⋆amguTerm leaf (function _ _) acc = nothing
--     ⋆amgu.amgu ⋆amguTerm leaf (s' fork t') acc = nothing
--     ⋆amgu.amgu ⋆amguTerm (s' fork t') leaf acc = nothing
--     ⋆amgu.amgu ⋆amguTerm (s' fork t') (function _ _) acc = nothing
--     ⋆amgu.amgu ⋆amguTerm (s1 fork s2) (t1 fork t2) acc =
--                       amgu s2 t2 =<< amgu s1 t1 acc
--     ⋆amgu.amgu ⋆amguTerm (function fn₁ ts₁) leaf acc = nothing
--     ⋆amgu.amgu ⋆amguTerm (function fn₁ {n₁} ts₁) (function fn₂ {n₂} ts₂) acc
--      with fn₁ ≟F fn₂
--     … | no _ = nothing
--     … | yes _ with n₁ ≟ n₂
--     … | no _ = nothing
--     … | yes refl = amgu ts₁ ts₂ acc
--     ⋆amgu.amgu ⋆amguTerm (function fn₁ ts₁) (_ fork _) acc = nothing
--     ⋆amgu.amgu ⋆amguTerm (i x) (i y) (m , anil) = just (flexFlex x y)
--     ⋆amgu.amgu ⋆amguTerm (i x) t     (m , anil) = flexRigid x t
--     ⋆amgu.amgu ⋆amguTerm t     (i x) (m , anil) = flexRigid x t
--     ⋆amgu.amgu ⋆amguTerm s     t  (n , σ asnoc r / z) =
--              (λ σ -> σ ∃asnoc r / z) <$>
--                amgu ((r for z) ◃ s) ((r for z) ◃ t) (n , σ)

--     instance ⋆amguVecTerm : ∀ {N} → ⋆amgu (flip Vec N ∘ Term)
--     ⋆amgu.amgu ⋆amguVecTerm [] [] acc = just acc
--     ⋆amgu.amgu ⋆amguVecTerm (t₁ ∷ t₁s) (t₂ ∷ t₂s) acc = amgu t₁s t₂s =<< amgu t₁ t₂ acc

--   mgu : ∀ {m} -> (s t : Term m) -> Maybe (∃ (AList m))
--   mgu {m} s t = amgu s t (m , anil)

--   mutual

--     -- We use a view so that we need to handle fewer cases in the main proof
--     data AmguT : {m : ℕ} -> (s t : Term m) -> ∃ (AList m) -> Maybe (∃ (AList m)) -> Set where
--       Flip : ∀ {m s t acc} -> amgu t s acc ≡ amgu s t acc ->
--         AmguT {m} t s acc (amgu t s acc) -> AmguT         s            t            acc        (amgu s t acc)
--       leaf-leaf : ∀ {m acc} ->             AmguT {m}     leaf         leaf         acc        (just acc)
--       fn-name   : ∀ {m fn₁ fn₂ N₁ N₂ acc} {ts₁ : Vec (Term m) N₁} {ts₂ : Vec (Term m) N₂} →
--                     fn₁ ≢ fn₂ →
--                                            AmguT {m}     (function fn₁ ts₁)
--                                                                      (function fn₂ ts₂)
--                                                                                   acc        nothing
--       fn-size   : ∀ {m fn₁ fn₂ N₁ N₂ acc} {ts₁ : Vec (Term m) N₁} {ts₂ : Vec (Term m) N₂} →
--                     N₁ ≢ N₂ →
--                                            AmguT {m}     (function fn₁ ts₁)
--                                                                      (function fn₂ ts₂)
--                                                                                    acc        nothing
--       fn-fn     : ∀ {m fn N acc} {ts₁ ts₂ : Vec (Term m) N} →
--                                            AmguT {m}     (function fn ts₁)
--                                                                      (function fn ts₂)
--                                                                                   acc        (amgu ts₁ ts₂ acc)
--       leaf-fork : ∀ {m s t acc} ->         AmguT {m}     leaf         (s fork t)   acc        nothing
--       leaf-fn   : ∀ {m fn N} {ts : Vec (Term _) N} {acc} ->       AmguT {m}     leaf         (function fn ts)   acc        nothing
--       fork-fn   : ∀ {m s t fn N} {ts : Vec (Term _) N} {acc} ->   AmguT {m}     (s fork t)   (function fn ts)   acc        nothing
--       fork-fork : ∀ {m s1 s2 t1 t2 acc} -> AmguT {m}     (s1 fork s2) (t1 fork t2) acc        (amgu s2 t2 =<< amgu s1 t1 acc)
--       var-var   : ∀ {m x y} ->             AmguT         (i x)        (i y)        (m , anil) (just (flexFlex x y))
--       var-t : ∀ {m x t} -> i x ≢ t ->      AmguT         (i x)        t            (m , anil) (flexRigid x t)
--       s-t : ∀{m s t n σ r z} ->            AmguT {suc m} s            t            (n , σ asnoc r / z) ((λ σ -> σ ∃asnoc r / z) <$>
--                                                                                                          amgu ((r for z) ◃ s) ((r for z) ◃ t) (n , σ))


--     data AmguTV : {m : ℕ} -> ∀ {N} (ss ts : Vec (Term m) N) -> ∃ (AList m) -> Maybe (∃ (AList m)) -> Set where
--       fn0-fn0   : ∀ {m acc} →
--                                            AmguTV {m}     ([])
--                                                                      ([])
--                                                                                   acc        (just acc)

--       fns-fns   : ∀ {m N acc} {t₁ t₂ : Term m} {ts₁ ts₂ : Vec (Term m) N} →
--                                            AmguTV {m}     ((t₁ ∷ ts₁))
--                                                                      ((t₂ ∷ ts₂))
--                                                                                   acc        (amgu ts₁ ts₂ =<< amgu t₁ t₂ acc)

--   view : ∀ {m : ℕ} -> (s t : Term m) -> (acc : ∃ (AList m)) -> AmguT s t acc (amgu s t acc)
--   view leaf         leaf         acc        = leaf-leaf
--   view leaf         (s fork t)   acc        = leaf-fork
--   view (s fork t)   leaf         acc        = Flip refl leaf-fork
--   view (s1 fork s2) (t1 fork t2) acc        = fork-fork
--   view (function fn₁ {n₁} ts₁) (function fn₂ {n₂} ts₂) acc  with
--    fn₁ ≟F fn₂
--   … | no neq = fn-name neq
--   … | yes refl with n₁ ≟ n₂
--   … | yes refl = fn-fn
--   … | no neq = fn-size neq
--   view leaf         (function fn ts) acc    = leaf-fn
--   view (function fn ts) leaf         acc    = Flip refl leaf-fn
--   view (function fn ts) (_ fork _)   acc    = Flip refl fork-fn
--   view (s fork t)   (function fn ts) acc    = fork-fn
--   view (i x)        (i y)        (m , anil) = var-var
--   view (i x)        leaf         (m , anil) = var-t (λ ())
--   view (i x)        (s fork t)   (m , anil) = var-t (λ ())
--   view (i x)        (function fn ts)   (m , anil) = var-t (λ ())
--   view leaf         (i x)        (m , anil) = Flip refl (var-t (λ ()))
--   view (s fork t)   (i x)        (m , anil) = Flip refl (var-t (λ ()))
--   view (function fn ts) (i x)    (m , anil) = Flip refl (var-t (λ ()))
--   view (i x)        (i x')       (n , σ asnoc r / z) = s-t
--   view (i x)        leaf         (n , σ asnoc r / z) = s-t
--   view (i x)        (s fork t)   (n , σ asnoc r / z) = s-t
--   view leaf         (i x)        (n , σ asnoc r / z) = s-t
--   view (s fork t)   (i x)        (n , σ asnoc r / z) = s-t
--   view (function fn ts)   (i x)        (n , σ asnoc r / z) = s-t
--   view (i x) (function fn ts)          (n , σ asnoc r / z) = s-t

--   viewV : ∀ {m : ℕ} {N} -> (ss ts : Vec (Term m) N) -> (acc : ∃ (AList m)) -> AmguTV ss ts acc (amgu ss ts acc)
--   viewV []         []         acc        = fn0-fn0
--   viewV (t ∷ ts₁) (t₂ ∷ ts₂) acc         = fns-fns

--   amgu-Correctness : {m : ℕ} -> (s t : Term m) -> ∃ (AList m) -> Set
--   amgu-Correctness s t (l , ρ) =
--       (∃ λ n → ∃ λ σ → π₁ (Max (Unifies s t [-◇ sub ρ ])) (sub σ) × amgu s t (l , ρ) ≡ just (n , σ ++ ρ ))
--     ⊎ (Nothing ((Unifies s t) [-◇ sub ρ ]) ×  amgu s t (l , ρ) ≡ nothing)

--   amgu-Correctness⋆ : {m : ℕ} -> (s t : Term m) -> ∃ (AList m) -> Set
--   amgu-Correctness⋆ s t (l , ρ) =
--       (∃ λ n → ∃ λ σ → π₁ (Max (Unifies s t [-◇ sub ρ ])) (sub σ) × amgu s t (l , ρ) ≡ just (n , σ ++ ρ ))
--     ⊎ (Nothing ((Unifies s t) [-◇ sub ρ ]) ×  amgu s t (l , ρ) ≡ nothing)

--   amgu-Ccomm : ∀ {m} s t acc -> amgu {m = m} s t acc ≡ amgu t s acc -> amgu-Correctness s t acc -> amgu-Correctness t s acc
--   amgu-Ccomm s t (l , ρ) st≡ts = lemma
--     where
--       Unst = (Unifies s t) [-◇ sub ρ ]
--       Unts = (Unifies t s) [-◇ sub ρ ]

--       Unst⇔Unts : ((Unifies s t) [-◇ sub ρ ]) ⇔ ((Unifies t s) [-◇ sub ρ ])
--       Unst⇔Unts = Properties.fact5 (Unifies s t) (Unifies t s) (sub ρ) (Properties.fact1 {_} {s} {t})

--       lemma : amgu-Correctness s t (l , ρ) -> amgu-Correctness t s (l , ρ)
--       lemma (inj₁ (n , σ , MaxUnst , amgu≡just)) =
--         inj₁ (n , σ , proj₁ (Max.fact Unst Unts Unst⇔Unts (sub σ)) MaxUnst , trans (sym st≡ts) amgu≡just)
--       lemma (inj₂ (NoUnst , amgu≡nothing)) =
--         inj₂ ((λ {_} → Properties.fact2 Unst Unts Unst⇔Unts NoUnst) , trans (sym st≡ts) amgu≡nothing)

--   amgu-Ccomm⋆ : ∀ {m} s t acc -> amgu {m = m} s t acc ≡ amgu t s acc -> amgu-Correctness⋆ s t acc -> amgu-Correctness⋆ t s acc
--   amgu-Ccomm⋆ s t (l , ρ) st≡ts = lemma
--     where
--       Unst = (Unifies s t) [-◇ sub ρ ]
--       Unts = (Unifies t s) [-◇ sub ρ ]

--       Unst⇔Unts : ((Unifies s t) [-◇ sub ρ ]) ⇔ ((Unifies t s) [-◇ sub ρ ])
--       Unst⇔Unts = Properties.fact5 (Unifies s t) (Unifies t s) (sub ρ) (Properties.fact1 {_} {s} {t})

--       lemma : amgu-Correctness s t (l , ρ) -> amgu-Correctness t s (l , ρ)
--       lemma (inj₁ (n , σ , MaxUnst , amgu≡just)) =
--         inj₁ (n , σ , proj₁ (Max.fact Unst Unts Unst⇔Unts (sub σ)) MaxUnst , trans (sym st≡ts) amgu≡just)
--       lemma (inj₂ (NoUnst , amgu≡nothing)) =
--         inj₂ ((λ {_} → Properties.fact2 Unst Unts Unst⇔Unts NoUnst) , trans (sym st≡ts) amgu≡nothing)

--   mutual

--     amguV-c : ∀ {m N} {ss ts : Vec (Term m) N} {l ρ} -> AmguTV ss ts (l , ρ) (amgu ss ts (l , ρ)) ->
--                 (∃ λ n → ∃ λ σ → Max⋆ (Unifies⋆V ss ts [-◇⋆ sub ρ ]) (sub σ) × amgu {m = m} ss ts (l , ρ) ≡ just (n , σ ++ ρ ))
--               ⊎ (Nothing⋆ (Unifies⋆V ss ts [-◇⋆ sub ρ ])                     × amgu {m = m} ss ts (l , ρ) ≡ nothing)
--     amguV-c {m} {N} {ss} {ts} {l} {ρ} amg with amgu ss ts (l , ρ)
--     amguV-c {m} {0} {.[]} {.[]} {l} {ρ} fn0-fn0 | .(just (l , ρ)) = inj₁ (_ , anil , trivial-problemV {_} {_} {_} {[]} {sub ρ} , cong (just ∘ _,_ l) (sym (SubList.anil-id-l ρ)))
--     amguV-c {m} {.(suc _)} {(t₁ ∷ ts₁)} {(t₂ ∷ ts₂)} {l} {ρ} fns-fns | _  with amgu t₁ t₂ (l , ρ)  | amgu-c $ view t₁ t₂ (l , ρ)
--     amguV-c {m} {.(suc _)} {(t₁ ∷ ts₁)} {(t₂ ∷ ts₂)} {l} {ρ} fns-fns | _ | am | inj₂ (nounify , refl) = inj₂ ((λ {_} → NothingVecHead t₁ t₂ ρ _ _ nounify) , refl)
--     amguV-c {m} {.(suc _)} {(t₁ ∷ ts₁)} {(t₂ ∷ ts₂)} {l} {ρ} fns-fns | _ | am | inj₁ (n , σ , a , refl)
--      with amgu ts₁ ts₂ (n , σ ++ ρ) | amguV-c (viewV (ts₁) (ts₂) (n , (σ ++ ρ)))
--     … | _ | inj₂ (nounify , refl) = inj₂ ((λ {_} → NothingVecTail σ t₁ t₂ _ _ ρ a nounify) , refl)
--     … | _ | inj₁ (n1 , σ1 , a1 , refl) = inj₁ (n1 , σ1 ++ σ , MaxVec t₁ t₂ _ _ ρ σ a σ1 a1 , cong (λ σ -> just (n1 , σ)) (++-assoc σ1 σ ρ))

--     amgu-c : ∀ {m s t l ρ} -> AmguT s t (l , ρ) (amgu s t (l , ρ)) ->
--                (∃ λ n → ∃ λ σ → Max⋆ (Unifies⋆ s t [-◇⋆ sub ρ ]) (sub σ) × amgu {m = m} s t (l , ρ) ≡ just (n , σ ++ ρ ))
--              ⊎ (Nothing⋆ (Unifies⋆ s t [-◇⋆ sub ρ ])                     × amgu {m = m} s t (l , ρ) ≡ nothing)
--     amgu-c {m} {s} {t} {l} {ρ} amg with amgu s t (l , ρ)
--     amgu-c {l = l} {ρ} leaf-leaf | ._
--       = inj₁ (l , anil , trivial-problem {_} {_} {leaf} {sub ρ} , cong (λ x -> just (l , x)) (sym (SubList.anil-id-l ρ)) )
--     amgu-c (fn-name neq) | _ = inj₂ ((λ f x → neq (Term-function-inj-FunctionName x)) , refl)
--     amgu-c (fn-size neq) | _ = inj₂ ((λ f x → neq (Term-function-inj-VecSize x)) , refl)
--     amgu-c {s = function fn ts₁} {t = function .fn ts₂} {l = l} {ρ = ρ} fn-fn | _ with amgu ts₁ ts₂ | amguV-c (viewV ts₁ ts₂ (l , ρ))
--     … | _ | inj₂ (nounify , refl!) rewrite refl! = inj₂ ((λ {_} f feq → nounify f (Term-function-inj-Vector feq)) , refl)
--     … | _ | inj₁ (n , σ , (b , c) , refl!) rewrite refl! = inj₁ (_ , _ , ((cong (function fn) b) , (λ {_} f' feq → c f' (Term-function-inj-Vector feq))) , refl )
--     amgu-c leaf-fork | .nothing = inj₂ ((λ _ () ) , refl)
--     amgu-c leaf-fn | _ = inj₂ ((λ _ () ) , refl)
--     amgu-c fork-fn | _ = inj₂ ((λ _ () ) , refl)
--     amgu-c {m} {s1 fork s2} {t1 fork t2} {l} {ρ} fork-fork | ._
--      with amgu s1 t1 (l , ρ)  | amgu-c $ view s1 t1 (l , ρ)
--     … | .nothing             | inj₂ (nounify , refl) = inj₂ ((λ {_} -> NothingForkLeft s1 t1 ρ s2 t2 nounify) , refl)
--     … | .(just (n , σ ++ ρ)) | inj₁ (n , σ , a , refl)
--      with amgu s2 t2 (n , σ ++ ρ) | amgu-c (view s2 t2 (n , (σ ++ ρ)))
--     … | .nothing                | inj₂ (nounify , refl) = inj₂ ( (λ {_} -> NothingForkRight σ s1 s2 t1 t2 ρ a nounify) , refl)
--     … | .(just (n1 , σ1 ++ (σ ++ ρ))) | inj₁ (n1 , σ1 , b , refl)
--         = inj₁ (n1 , σ1 ++ σ , MaxFork s1 s2 t1 t2 ρ σ a σ1 b , cong (λ σ -> just (n1 , σ)) (++-assoc σ1 σ ρ))
--     amgu-c {suc l} {i x} {i y} (var-var) | .(just (flexFlex x y))
--      with thick? x y | Thick.fact1 x y (thick? x y) refl
--     …  | .(just y') | inj₂ (y' , thinxy'≡y , refl )
--       = inj₁ (l , anil asnoc i y' / x , var-elim-i-≡ x (i y) (sym (cong i thinxy'≡y)) , refl )
--     …  | .nothing | inj₁ ( x≡y , refl ) rewrite sym x≡y
--       = inj₁ (suc l , anil , trivial-problem {_} {_} {i x} {sub anil} , refl)
--     amgu-c {suc l} {i x} {t} (var-t ix≢t) | .(flexRigid x t)
--      with check x t | check-prop x t
--     … | .nothing  | inj₂ ( ps , r , refl) = inj₂ ( (λ {_} -> NothingStep x t ix≢t ps r )  , refl)
--     … | .(just t') | inj₁ (t' , r , refl) = inj₁ ( l , anil asnoc t' / x , var-elim-i-≡ x t r , refl )
--     amgu-c {suc m} {s} {t} {l} {ρ asnoc r / z} s-t
--       | .((λ x' → x' ∃asnoc r / z) <$>
--           (amgu ((r for z) ◃ s) ((r for z) ◃ t) (l , ρ)))
--      with amgu-c (view ((r for z) ◃ s) ((r for z) ◃ t) (l , ρ))
--     … | inj₂ (nounify , ra) = inj₂ ( (λ {_} -> NothingFor→NothingComposition s t ρ r z nounify) , cong (_<$>_ (λ x' → x' ∃asnoc r / z)) ra )
--     … | inj₁ (n , σ , a , ra)  = inj₁ (n , σ , MaxFor→MaxComposition s t ρ r z σ a , cong (_<$>_ (λ x' → x' ∃asnoc r / z)) ra)
--     amgu-c {m} {s} {t} {l} {ρ} (Flip amguts≡amgust amguts) | ._ = amgu-Ccomm⋆ t s (l , ρ) amguts≡amgust (amgu-c amguts)
--     amgu-c {zero} {i ()} _ | _

--   mgu-c : ∀ {m} (s t : Term m) ->
--              (∃ λ n → ∃ λ σ → (Max⋆ (Unifies⋆ s t)) (sub σ) × mgu s t ≡ just (n , σ))
--            ⊎ (Nothing⋆ (Unifies⋆ s t)                       × mgu s t ≡ nothing)
--   mgu-c {m} s t = amgu-c (view s t (m , anil))

--   unify : ∀ {m} (s t : Term m) ->
--              (∃ λ n → ∃ λ (σ : AList m n) → Max⋆ (Unifies⋆ s t) $ sub σ)
--              ⊎ Nothing⋆ (Unifies⋆ s t)
--   unify {m} s t with amgu-c (view s t (m , anil))
--   unify {m} s₁ t | inj₁ (proj₃ , proj₄ , proj₅ , proj₆) = inj₁ (proj₃ , proj₄ , proj₅)
--   unify {m} s t | inj₂ (proj₃ , _) = inj₂ proj₃

--   unifyV : ∀ {m N} (s t : Vec (Term m) N) ->
--              (∃ λ n → ∃ λ (σ : AList m n) → Max⋆ (Unifies⋆V s t) $ sub σ)
--              ⊎ Nothing⋆ (Unifies⋆V s t)
--   unifyV {m} {N} s t with amguV-c (viewV s t (m , anil))
--   … | inj₁ (proj₃ , proj₄ , proj₅ , proj₆) = inj₁ (proj₃ , proj₄ , proj₅)
--   … | inj₂ (proj₃ , _) = inj₂ proj₃

--   open import Oscar.Data.Permutation

--   unifyWith : ∀ {m N} (p q : Term m) (X Y : Vec (Term m) N) →
--               (∃ λ X* → X* ≡ordering' X × ∃ λ n → ∃ λ (σ : AList m n) → Max⋆ (Unifies⋆V (p ∷ X*) (q ∷ Y)) $ sub σ)
--               ⊎
--               (∀ X* → X* ≡ordering' X → Nothing⋆ (Unifies⋆V (p ∷ X*) (q ∷ Y)))
--   unifyWith p q X Y = {!!}
