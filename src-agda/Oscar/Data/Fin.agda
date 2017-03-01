
module Oscar.Data.Fin where

open import Data.Fin public

module _ where

  open import Data.Product
  open import Oscar.Data.Vec
  open import Data.Nat
  open import Function

  enumFin⋆ : ∀ n → ∃ λ (F : Vec (Fin n) n) → ∀ f → f ∈ F
  enumFin⋆ n = tabulate⋆ id

module _ where

  open import Agda.Builtin.Nat using (zero; suc)
  open import Agda.Primitive using (lzero)
  open import Category.Functor using (RawFunctor)
  open import Data.Maybe using (Maybe; nothing; just; functor)
  open RawFunctor (functor {f = lzero}) using (_<$>_)

  thick? : ∀ {n} -> (x y : Fin (suc n)) -> Maybe (Fin n)
  thick? zero zero = nothing
  thick? zero (suc y) = just y
  thick? {zero} (suc ()) _
  thick? {suc _} (suc x) zero = just zero
  thick? {suc _} (suc x) (suc y) = suc <$> (thick? x y)

open import Agda.Builtin.Equality
open import Agda.Builtin.Nat
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Product
open import Data.Empty
open import Function

previous : ∀ {n} -> Fin (suc (suc n)) -> Fin (suc n)
previous (suc x) = x
previous zero = zero

module Thin where
  fact1 : ∀ {n} x y z -> thin {n} x y ≡ thin x z -> y ≡ z
  fact1 zero y .y refl = refl
  fact1 (suc x) zero zero r = refl
  fact1 (suc x) zero (suc z) ()
  fact1 (suc x) (suc y) zero ()
  fact1 (suc x) (suc y) (suc z) r = cong suc (fact1 x y z (cong previous r))

  fact2 : ∀ {n} x y -> ¬ thin {n} x y ≡ x
  fact2 zero y ()
  fact2 (suc x) zero ()
  fact2 (suc x) (suc y) r = fact2 x y (cong previous r)

  fact3 : ∀{n} x y -> ¬ x ≡ y -> ∃ λ y' -> thin {n} x y' ≡ y
  fact3 zero zero ne = ⊥-elim (ne refl)
  fact3 zero (suc y) _ = y , refl
  fact3 {zero} (suc ()) _ _
  fact3 {suc n} (suc x) zero ne = zero , refl
  fact3 {suc n} (suc x) (suc y) ne with y | fact3 x y (ne ∘ cong suc)
  ... | .(thin x y') | y' , refl = suc y' , refl

open import Data.Maybe
open import Category.Functor
open import Category.Monad
import Level
open RawMonad (Data.Maybe.monad {Level.zero})

open import Data.Sum

_≡Fin_ : ∀ {n} -> (x y : Fin n) -> Dec (x ≡ y)
zero ≡Fin zero = yes refl
zero ≡Fin suc y = no λ ()
suc x ≡Fin zero = no λ ()
suc {suc _} x ≡Fin suc y with x ≡Fin y
...              | yes r = yes (cong suc r)
...              | no r = no λ e -> r (cong previous e)
suc {zero} () ≡Fin _

module Thick where
  half1 : ∀ {n} (x : Fin (suc n)) -> thick? x x ≡ nothing
  half1 zero = refl
  half1 {suc _} (suc x) = cong ((_<$>_ suc)) (half1 x)
  half1 {zero} (suc ())

  half2 : ∀ {n} (x : Fin (suc n)) y -> ∀ y' -> thin x y' ≡ y -> thick? x y ≡ just y'
  half2 zero zero y' ()
  half2 zero (suc y) .y refl = refl
  half2 {suc n} (suc x) zero zero refl = refl
  half2 {suc _} (suc _) zero (suc _) ()
  half2 {suc n} (suc x) (suc y) zero ()
  half2 {suc n} (suc x) (suc .(thin x y')) (suc y') refl with thick? x (thin x y') | half2 x (thin x y') y' refl
  ...                                                       | .(just y')          | refl = refl
  half2 {zero} (suc ()) _ _ _

  fact1 : ∀ {n} (x : Fin (suc n)) y r
    -> thick? x y ≡ r
    -> x ≡ y × r ≡ nothing ⊎ ∃ λ y' -> thin x y' ≡ y × r ≡ just y'
  fact1 x y .(thick? x y) refl with x ≡Fin y
  fact1 x .x ._ refl | yes refl = inj₁ (refl , half1 x)
  ... | no el with Thin.fact3 x y el
  ...            | y' , thinxy'=y = inj₂ (y' , ( thinxy'=y , half2 x y y' thinxy'=y ))

open import Data.Maybe using (Maybe; nothing; just; functor; maybe′)
open import Category.Monad
import Level
open RawMonad (Data.Maybe.monad {Level.zero})
open import Data.Nat using (ℕ)

record Check (T : ℕ → Set) : Set where
  field
    check : ∀{n} (x : Fin (suc n)) (t : T (suc n)) -> Maybe (T n)

open Check ⦃ … ⦄ public
