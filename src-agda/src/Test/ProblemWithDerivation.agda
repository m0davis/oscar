{-# OPTIONS --allow-unsolved-metas #-}

open import Everything

module Test.ProblemWithDerivation where

module _ (𝔓 : Ø₀) where

  open Substitunction 𝔓

  test-level-0 : ∀ {m n} (f : Substitunction m n) → Substitunction m n
  test-level-0 f = transitivity f ε -- FIXME

postulate
  A : Set
  B : Set
  _~A~_ : A → A → Set
  _~B~_ : B → B → Set
  s1 : A → B
  f1 : ∀ {x y} → x ~A~ y → s1 x ~B~ s1 y

module _ {𝔭} (𝔓 : Ø 𝔭) where

  open Substitunction 𝔓

  test-before : ∀ {m n ℓ} {f : Substitunction m n} (P : LeftExtensionṖroperty ℓ Substitunction Proposextensequality m) (let P₀ = π₀ (π₀ P)) → P₀ f → P₀ (ε ∙ f)
  test-before P pf = hmap _ P pf -- needs Oscar.Class.Hmap.Transleftidentity.Relprop'idFromTransleftidentity

  instance

    𝓢urjectivity1 : Smap.class _~A~_ _~B~_ s1 s1
    𝓢urjectivity1 .⋆ _ _ = f1

  test : ∀ {x y} → x ~A~ y → s1 x ~B~ s1 y
  test {x} {y} = smap -- FIXME confused by Oscar.Class.Hmap.Transleftidentity.Relprop'idFromTransleftidentity

  test-after : ∀ {m n ℓ} {f : Substitunction m n} (P : LeftExtensionṖroperty ℓ Substitunction Proposextensequality m) (let P₀ = π₀ (π₀ P)) → P₀ f → P₀ (ε ∙ f)
  test-after P pf = hmap _ P pf
