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
open import Data.Permutation

vectorPermutation : ∀ {A : Set} {N} (p : Permutation N) → (v : Vec A N) → ∃ λ v' → ∀ f g → < p > f ≡ g → v' Data.Vec.[ f ]= Data.Vec.lookup g v
vectorPermutation [] v = v , λ {() g x}
vectorPermutation (p ∷ ps) v with vectorPermutation ps {!!}
… | vp = {!!} , (λ {f g x → {!!}})

_≡ordering_ : ∀ {m N} → Vec (Term m) N → Vec (Term m) N → Set
_≡ordering_ {_} {N} ss ts = Σ (Permutation N) λ p → ∀ f g → < p > f ≡ g → ss Data.Vec.[ f ]= Data.Vec.lookup g ts

enumOrderings : ∀ {A : Set} {N} → Vec A N → Vec (Vec A N) (size N N)
enumOrderings = {!!}

unifyWith : ∀ {m N} (p q : Term m) (X Y : Vec (Term m) N) →
            (∃ λ X* → X* ≡ordering X × ∃ λ n → ∃ λ (σ : AList m n) → Max⋆ (Unifies⋆V (p ∷ X*) (q ∷ Y)) $ sub σ)
            ⊎
            (∀ X* → X* ≡ordering X → Nothing⋆ (Unifies⋆V (p ∷ X*) (q ∷ Y)))
unifyWith p₁ q X Y = {!!}
