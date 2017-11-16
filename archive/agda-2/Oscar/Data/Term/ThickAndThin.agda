{-# OPTIONS --allow-unsolved-metas #-}
module Oscar.Data.Term.ThickAndThin {𝔣} (FunctionName : Set 𝔣) where

open import Oscar.Class.ThickAndThin
open import Oscar.Data.Term FunctionName
import Oscar.Data.Term.ThickAndThin.internal FunctionName as ⋆

instance ThickAndThinTerm : ThickAndThin Term
ThickAndThin.thin ThickAndThinTerm = ⋆.thin
ThickAndThin.thin-injective ThickAndThinTerm = ⋆.thin-injective
ThickAndThin.thick ThickAndThinTerm = ⋆.thick
ThickAndThin.thick∘thin=id ThickAndThinTerm = {!!}
ThickAndThin.check ThickAndThinTerm = {!!}
ThickAndThin.thin-check-id ThickAndThinTerm = {!!}

instance ThickAndThinTerms : ∀ {N} → ThickAndThin (Terms N)
ThickAndThin.thin ThickAndThinTerms x = ⋆.thins x
ThickAndThin.thin-injective ThickAndThinTerms y = ⋆.thins-injective y
ThickAndThin.thick ThickAndThinTerms = ⋆.thicks
ThickAndThin.thick∘thin=id ThickAndThinTerms = {!!}
ThickAndThin.check ThickAndThinTerms = {!!}
ThickAndThin.thin-check-id ThickAndThinTerms = {!!}

open import Oscar.Data.Fin
open import Oscar.Data.Fin.ThickAndThin
open import Oscar.Data.Maybe.properties
open import Oscar.Data.Nat

_for_ : ∀ {n} → Term n → Fin (suc n) → suc n ⊸ n
(t' for x) y = maybe i t' ((check x y))
