
module Oscar.Data.IList where

open import Oscar.Data.Nat

-- List = [_]

-- data List↥ {a} (A : Nat → Set a) (n : Nat) : Nat → Set a where
--   [] : List↥ A n n
--   _∷_ : ∀ {m} → A m → List↥ A n m → List↥ A n (suc m)

-- data IIList {a} (A : Nat → Nat → Set a) : Nat → Nat → Set a where
--   [] : ∀ {n} → IIList A 0 n
--   _∷_ : ∀ {m n} → A m n → IIList A m n → IIList A (suc m) (suc n)

-- open import Oscar.Data.Vec

-- {-
-- List[_/_] = Vec
-- --_/_ = {!!}
-- --_/_⇒_ = {!!}
-- --_⇒_ = ?

-- List[_/_⇒_] = IList
-- List[_⇒_] = {!!}

-- foo = List[ (λ _ → Nat) / 0 ⇒ 3 ]
-- -}
