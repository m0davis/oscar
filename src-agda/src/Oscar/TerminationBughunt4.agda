
module Oscar.TerminationBughunt4 where

open import Oscar.Prelude
open import Oscar.Data hiding (module Term)

postulate
  𝔓 : Ø₀

module Term' {𝔭} (𝔓 : Ø 𝔭) where

  data Term (n : ¶) : Ø 𝔭 where
    i : (x : ¶⟨< n ⟩) → Term n
    fork : (t : Term n) → Term n

open Term' 𝔓

data Sub : ¶ → ¶ → Ø₀ where
  ∅ : ∀ {m} → Sub m m
  _asub_ : ∀ {n m} → Term n → Sub n m → Sub (↑ n) m

Substitunction : ¶ → ¶ → Ø₀
Substitunction m n = ¶⟨< m ⟩ → Term n

postulate
  fmapMaybe : ∀ {n} → Maybe (∃ Sub n) → Maybe (∃ Sub (↑ n))
  bindMaybe : ∀ {n} → (∃ Sub n → Maybe (∃ Sub n)) → Maybe (∃ Sub n)
  𝓼' : ∀ {x y} → Term x → Term (¡ y)
  𝓼'' : ∀ {x y} → Term x → Term y

{-
test : ∀ {m} (t : Term'') (acc : ∃ Sub m) -> Maybe (∃ Sub m)
test (fork t2) acc = bindMaybe (test t2)
test (i x) (m , ∅) = ∅
test t  (n , r asub σ) =
  fmapMaybe
  (test
    (s'' for t)
    (n , σ)
  )
-}

test' : ∀ {m} (t : Term m) (acc : ∃ Sub m) -> Maybe (∃ Sub m)
test' (fork t2) acc = bindMaybe (test' t2)
test' (i x) (m , ∅) = ∅
test' t  (n , r asub σ) = fmapMaybe $ test' (𝓼'' t) (n , σ)
