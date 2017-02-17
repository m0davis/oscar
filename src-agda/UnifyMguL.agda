open import Relation.Binary using (IsDecEquivalence)
open import Agda.Builtin.Equality

module UnifyMguL (A : Set) ⦃ isDecEquivalenceA : IsDecEquivalence (_≡_ {A = A}) ⦄ where

open import UnifyTermL A

open import Data.Product using (∃; _,_)
open import Data.Maybe using (Maybe; just; nothing)
open import Category.Monad using (RawMonad)
import Level
open RawMonad (Data.Maybe.monad {Level.zero})

open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

open IsDecEquivalence isDecEquivalenceA

amgu : ∀ {m} (s t : Term m) (acc : ∃ (AList m)) -> Maybe (∃ (AList m))
amgu (leaf l₁) (leaf l₂) acc with l₁ ≟ l₂
… | yes _ = just acc
… | no _ = nothing
amgu (leaf l) (s' fork t') acc = nothing
amgu (s' fork t') (leaf l) acc = nothing
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
