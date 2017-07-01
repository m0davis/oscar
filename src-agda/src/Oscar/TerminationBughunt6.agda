
module Oscar.TerminationBughunt6 where

open import Oscar.Prelude
open import Oscar.Data hiding (module Term)

module Test1 where

  data Term (n : ¶) : Ø₀ where
    leaf : Term n
    fork : (t : Term n) → Term n

  data Sub : ¶ → ¶ → Ø₀ where
    ∅ : ∀ {m} → Sub m m
    _asub_ : ∀ {n m} → Term n → Sub n m → Sub (↑ n) m

  postulate
    fmapMaybe : ∀ {n} → ∃ Sub n → ∃ Sub (↑ n)
    bindMaybe : ∀ {n} → (∃ Sub n → ∃ Sub n) → ∃ Sub n
    𝓼' : ∀ {x y} → Term x → Term (¡ y)
    𝓼'' : ∀ {x y} → Term x → Term y

  test : ∀ {m} (t : Term m) (acc : ∃ Sub m) -> ∃ Sub m
  test (fork t2) acc = bindMaybe $ test t2
  test leaf (m , ∅) = (m , ∅)
  test t  (n , r asub σ) = fmapMaybe $ test (𝓼'' t) (n , σ)

module Test2 where

  data Term (n : ¶) : Ø₀ where
    leaf : Term n
    fork : (t : Term n) → Term n

  data Sub : ¶ → Ø₀ where
    ∅ : ∀ {m} → Sub m
    _asub_ : ∀ {n} → Term n → Sub n → Sub (↑ n)

  postulate
    fmapMaybe : ∀ {n} → Sub n → Sub (↑ n)
    bindMaybe : ∀ {n} → (Sub n → Sub n) → Sub n
    𝓼' : ∀ {x y} → Term x → Term (¡ y)
    𝓼'' : ∀ {x y} → Term x → Term y

  test : ∀ {m} (t : Term m) (acc : Sub m) -> Sub m
  test (fork t2) acc = bindMaybe $ test t2
  test leaf ∅ = ∅
  test t (r asub σ) = fmapMaybe $ test (𝓼'' t) σ

module Test3 where

  data Term (n : ¶) : Ø₀ where
    leaf : Term n
    fork : (t : Term n) → Term n

  data Sub : ¶ → Ø₀ where
    ∅ : ∀ {m} → Sub m
    asub : ∀ {n} → Term n → Sub n → Sub (↑ n)

  postulate
    up : ∀ {n} → (Sub n → Sub n) → Sub (↑ n)
    down : ∀ {n} → Sub (↑ n) → Sub n
    𝓼' : ∀ {x y} → Term x → Term (¡ y)
    𝓼'' : ∀ {x y} → Term x → Term y

  test : ∀ {m} → Term m → Sub m → Sub m
  test (fork t) acc = down (up (test t))
  test leaf ∅ = ∅
  test t (asub r σ) = up (test ((𝓼'' t)))
