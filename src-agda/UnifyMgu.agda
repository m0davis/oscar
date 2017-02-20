
module UnifyMgu where

open import UnifyTerm

open import Data.Product using (∃; _,_)
open import Data.Maybe using (Maybe; just; nothing)
open import Category.Monad using (RawMonad)
import Level
open RawMonad (Data.Maybe.monad {Level.zero})

amgu : ∀ {m} (s t : Term m) (acc : ∃ (AList m)) -> Maybe (∃ (AList m))
amgu leaf leaf acc = just acc
amgu leaf (s' fork t') acc = nothing
amgu (s' fork t') leaf acc = nothing
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
