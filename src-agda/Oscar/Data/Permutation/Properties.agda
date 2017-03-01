
module Oscar.Data.Permutation.Properties where

open import Data.Permutation.Properties public

open import Data.Nat
open import Oscar.Data.Vec renaming (delete to deleteV)
open import Oscar.Data.Vec.Properties
open import Oscar.Data.Permutation

∈-enum : ∀ {n m} (i : Inj n m) → i ∈ enum n m
∈-enum {zero} [] = here
∈-enum {suc n} (i ∷ is) = ∈-map₂ _∷_ (∈-allFin i) (∈-enum is)

open import Data.Fin
open import Relation.Binary.PropositionalEquality

permute-correct : ∀ {a n} {A : Set a} → (p : Permutation n) → (v : Vec A n) →
                  [ v ≡Permutation permute p v ] p
permute-correct [] [] = λ ()
permute-correct (p ∷ ps) (_ ∷ _) zero = here
permute-correct (p ∷ ps) v@(_ ∷ _) (suc f) =
  let bs = permute ps (deleteV p v)
      delresult = permute-correct ps (deleteV p v)
  in
  there ((subst (bs [ f ]=_) (lookup-delete-thin p (< ps > f) v) ((delresult f))))

open import Data.Product
open import Relation.Binary.PropositionalEquality

enumPermutations-complete : ∀ {a n} {A : Set a} → (xs : Vec A n) → ∀ ys → xs ∃≡Permutation ys → ys ∈ enumPermutations xs
enumPermutations-complete [] [] ([] , xs=ys|p) = here
enumPermutations-complete (x ∷ xs) (y ∷ ys) (p ∷ ps , xs=ys|p∷ps) = {!!}
