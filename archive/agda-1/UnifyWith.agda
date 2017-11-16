open import Relation.Binary using (IsDecEquivalence)
open import Agda.Builtin.Equality

module UnifyWith (FunctionName : Set) ⦃ isDecEquivalenceA : IsDecEquivalence (_≡_ {A = FunctionName}) ⦄ where


open import UnifyTermF FunctionName
open import UnifyMguF FunctionName
open import UnifyMguCorrectF FunctionName

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


open import Data.Unit

-- moved to UnifyMguCorrectF
