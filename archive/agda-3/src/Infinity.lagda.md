```agda
open import Data.Empty
open import Data.Nat
open import Relation.Nullary
open import Data.Product
open import Data.Unit

finite : ℕ → Set
finite zero = ⊤
finite (suc n) = finite n

infinite : ℕ → Set
infinite n = finite n → ⊥

nothing-is-infinite : ¬ ∃ λ n → infinite n
nothing-is-infinite (zero , inf) = inf tt
nothing-is-infinite (suc n , inf) = nothing-is-infinite (n , inf)

but-can-we : ∀ n → infinite n → ⊥
but-can-we zero inf = inf tt
but-can-we (suc n) inf = but-can-we n inf
```
