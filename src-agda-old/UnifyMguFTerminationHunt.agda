open import Relation.Binary using (IsDecEquivalence)
open import Agda.Builtin.Equality

-- module UnifyMguFTerminationHunt (FunctionName : Set) ⦃ isDecEquivalenceA : IsDecEquivalence (_≡_ {A = FunctionName}) ⦄ where

module UnifyMguFTerminationHunt where

postulate
  FunctionName : Set
  instance isDecEquivalenceA : IsDecEquivalence (_≡_ {A = FunctionName})

open IsDecEquivalence isDecEquivalenceA using () renaming (_≟_ to _≟F_)

open import UnifyTermF FunctionName

open import Data.Product using (∃; _,_)
open import Data.Maybe using (Maybe; just; nothing)
open import Category.Monad using (RawMonad)
import Level
open RawMonad (Data.Maybe.monad {Level.zero})
open import Relation.Nullary using (Dec; yes; no)

open import Data.Fin using (Fin)
open import Data.Nat using (suc)
postulate
  _◃′_ : ∀ {m n} -> (f : m ~> n) -> Term m -> Term n
  _for'_ : ∀ {n} (t' : Term n) (x : Fin (suc n)) -> Fin (suc n) -> Term n


amterm : ∀ {m} (s t : Term m) (acc : ∃ (AList m)) -> Maybe (∃ (AList m))
amterm leaf leaf acc = just acc
amterm leaf (function _ _) acc = nothing
amterm leaf (s' fork t') acc = nothing
amterm (s' fork t') leaf acc = nothing
amterm (s' fork t') (function _ _) acc = nothing
amterm (s1 fork s2) (t1 fork t2) acc = amterm s2 t2 =<< amterm s1 t1 acc {- Data.Maybe.maybe (⋆amgu.amgu ⋆amguTerm' s2 t2) nothing (⋆amgu.amgu ⋆amguTerm' s1 t1 acc) -}
amterm (function fn₁ ts₁) leaf acc = nothing
amterm (function fn₁ {n₁} ts₁) (function fn₂ {n₂} ts₂) acc = nothing
amterm (function fn₁ ts₁) (_ fork _) acc = nothing
amterm (i x) (i y) (m , anil) = nothing
amterm (i x) t     (m , anil) = nothing
amterm t     (i x) (m , anil) = nothing
amterm s     t  (n , σ asnoc r / z) =
         (λ σ -> σ ∃asnoc r / z) <$>
           -- amgu ((r for z) ◃ s) ((r for z) ◃ t) (n , σ)
           amterm ((r for' z) ◃′ s) ((r for' z) ◃′ t) (n , σ)


-- instance ⋆amguTerm' : ⋆amgu Term
-- ⋆amguTerm' .⋆amgu.amgu leaf leaf acc = just acc
-- ⋆amguTerm' .⋆amgu.amgu leaf (function _ _) acc = nothing
-- ⋆amguTerm' .⋆amgu.amgu leaf (s' fork t') acc = nothing
-- ⋆amguTerm' .⋆amgu.amgu (s' fork t') leaf acc = nothing
-- ⋆amguTerm' .⋆amgu.amgu (s' fork t') (function _ _) acc = nothing
-- ⋆amguTerm' .⋆amgu.amgu (s1 fork s2) (t1 fork t2) acc = amgu s2 t2 =<< amgu s1 t1 acc {- Data.Maybe.maybe (⋆amgu.amgu ⋆amguTerm' s2 t2) nothing (⋆amgu.amgu ⋆amguTerm' s1 t1 acc) -}
-- ⋆amguTerm' .⋆amgu.amgu (function fn₁ ts₁) leaf acc = nothing
-- ⋆amguTerm' .⋆amgu.amgu (function fn₁ {n₁} ts₁) (function fn₂ {n₂} ts₂) acc = nothing
-- ⋆amguTerm' .⋆amgu.amgu (function fn₁ ts₁) (_ fork _) acc = nothing
-- ⋆amguTerm' .⋆amgu.amgu (i x) (i y) (m , anil) = nothing
-- ⋆amguTerm' .⋆amgu.amgu (i x) t     (m , anil) = nothing
-- ⋆amguTerm' .⋆amgu.amgu t     (i x) (m , anil) = nothing
-- ⋆amguTerm' .⋆amgu.amgu s     t  (n , σ asnoc r / z) =
--          (λ σ -> σ ∃asnoc r / z) <$>
--            -- amgu ((r for z) ◃ s) ((r for z) ◃ t) (n , σ)
--            amgu ((r for z) ◃′ s) ((r for z) ◃′ t) (n , σ)

-- -- instance ⋆amguTerm' : ⋆amgu Term
-- -- ⋆amgu.amgu ⋆amguTerm' leaf leaf acc = just acc
-- -- ⋆amgu.amgu ⋆amguTerm' leaf (function _ _) acc = nothing
-- -- ⋆amgu.amgu ⋆amguTerm' leaf (s' fork t') acc = nothing
-- -- ⋆amgu.amgu ⋆amguTerm' (s' fork t') leaf acc = nothing
-- -- ⋆amgu.amgu ⋆amguTerm' (s' fork t') (function _ _) acc = nothing
-- -- ⋆amgu.amgu ⋆amguTerm' (s1 fork s2) (t1 fork t2) acc = {!amgu s2 t2 =<< amgu s1 t1 acc!} {- Data.Maybe.maybe (⋆amgu.amgu ⋆amguTerm' s2 t2) nothing (⋆amgu.amgu ⋆amguTerm' s1 t1 acc) -}
-- -- ⋆amgu.amgu ⋆amguTerm' (function fn₁ ts₁) leaf acc = nothing
-- -- ⋆amgu.amgu ⋆amguTerm' (function fn₁ {n₁} ts₁) (function fn₂ {n₂} ts₂) acc = nothing
-- -- ⋆amgu.amgu ⋆amguTerm' (function fn₁ ts₁) (_ fork _) acc = nothing
-- -- ⋆amgu.amgu ⋆amguTerm' (i x) (i y) (m , anil) = nothing
-- -- ⋆amgu.amgu ⋆amguTerm' (i x) t     (m , anil) = nothing
-- -- ⋆amgu.amgu ⋆amguTerm' t     (i x) (m , anil) = nothing
-- -- ⋆amgu.amgu ⋆amguTerm' s     t  (n , σ asnoc r / z) =
-- --          (λ σ -> σ ∃asnoc r / z) <$>
-- --            -- amgu ((r for z) ◃ s) ((r for z) ◃ t) (n , σ)
-- --            amgu ((r for z) ◃′ s) ((r for z) ◃′ t) (n , σ)


-- -- -- mutual

-- -- --   instance ⋆amguTerm : ⋆amgu Term
-- -- --   ⋆amgu.amgu ⋆amguTerm leaf leaf acc = just acc
-- -- --   ⋆amgu.amgu ⋆amguTerm leaf (function _ _) acc = nothing
-- -- --   ⋆amgu.amgu ⋆amguTerm leaf (s' fork t') acc = nothing
-- -- --   ⋆amgu.amgu ⋆amguTerm (s' fork t') leaf acc = nothing
-- -- --   ⋆amgu.amgu ⋆amguTerm (s' fork t') (function _ _) acc = nothing
-- -- --   ⋆amgu.amgu ⋆amguTerm (s1 fork s2) (t1 fork t2) acc =
-- -- --                     amgu s2 t2 =<< amgu s1 t1 acc
-- -- --   ⋆amgu.amgu ⋆amguTerm (function fn₁ ts₁) leaf acc = nothing
-- -- --   ⋆amgu.amgu ⋆amguTerm (function fn₁ {n₁} ts₁) (function fn₂ {n₂} ts₂) acc
-- -- --    with fn₁ ≟F fn₂
-- -- --   … | no _ = nothing
-- -- --   … | yes _ with n₁ ≟ n₂
-- -- --   … | no _ = nothing
-- -- --   … | yes refl = amgu ts₁ ts₂ acc
-- -- --   ⋆amgu.amgu ⋆amguTerm (function fn₁ ts₁) (_ fork _) acc = nothing
-- -- --   ⋆amgu.amgu ⋆amguTerm (i x) (i y) (m , anil) = just (flexFlex x y)
-- -- --   ⋆amgu.amgu ⋆amguTerm (i x) t     (m , anil) = flexRigid x t
-- -- --   ⋆amgu.amgu ⋆amguTerm t     (i x) (m , anil) = flexRigid x t
-- -- --   ⋆amgu.amgu ⋆amguTerm s     t  (n , σ asnoc r / z) =
-- -- --            (λ σ -> σ ∃asnoc r / z) <$>
-- -- --              amgu ((r for z) ◃ s) ((r for z) ◃ t) (n , σ)

-- -- --   instance ⋆amguVecTerm : ∀ {N} → ⋆amgu (flip Vec N ∘ Term)
-- -- --   ⋆amgu.amgu ⋆amguVecTerm [] [] acc = just acc
-- -- --   ⋆amgu.amgu ⋆amguVecTerm (t₁ ∷ t₁s) (t₂ ∷ t₂s) acc = amgu t₁s t₂s =<< amgu t₁ t₂ acc

-- -- -- mgu : ∀ {m} -> (s t : Term m) -> Maybe (∃ (AList m))
-- -- -- mgu {m} s t = amgu s t (m , anil)
